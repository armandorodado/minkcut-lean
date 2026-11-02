import MinKCut.Weighted
/-! # Part L: communication, additive-query and fixed-slot simulations -/

namespace MinKCut

/-! ## Part L: simulations (communication protocols, additive queries, fixed-slot arrays) -/

/-- A deterministic two-party protocol: at each node Alice or Bob sends one bit computed from
    their own input; leaves carry the output. Public coins are modelled by a family of
    protocols indexed by the shared random string. -/
inductive Prot (IA IB α : Type) where
  | ret : α → Prot IA IB α
  | sendA : (IA → Bool) → (Bool → Prot IA IB α) → Prot IA IB α
  | sendB : (IB → Bool) → (Bool → Prot IA IB α) → Prot IA IB α

namespace Prot
variable {IA IB α : Type}
def exec (a : IA) (b : IB) : Prot IA IB α → α
  | ret r => r
  | sendA f k => exec a b (k (f a))
  | sendB g k => exec a b (k (g b))
def bits (a : IA) (b : IB) : Prot IA IB α → Nat
  | ret _ => 0
  | sendA f k => 1 + bits a b (k (f a))
  | sendB g k => 1 + bits a b (k (g b))

/-- Alice sends the c low bits of f a; the continuation receives the number. -/
def numA (f : IA → Nat) : Nat → (Nat → Prot IA IB α) → Prot IA IB α
  | 0, k => k 0
  | c + 1, k => sendA (fun a => f a % 2 == 1)
      (fun bit => numA (fun a => f a / 2) c (fun r => k (2 * r + ind bit)))
def numB (g : IB → Nat) : Nat → (Nat → Prot IA IB α) → Prot IA IB α
  | 0, k => k 0
  | c + 1, k => sendB (fun b => g b % 2 == 1)
      (fun bit => numB (fun b => g b / 2) c (fun r => k (2 * r + ind bit)))
end Prot

theorem mod_two_pow (m c : Nat) : 2 * (m / 2 % 2 ^ c) + ind (m % 2 == 1) = m % 2 ^ (c + 1) := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ c) 2, Nat.mod_mul]
  have : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases this with h | h <;> simp [h, ind] <;> omega

theorem numA_spec {IA IB α : Type} (a : IA) (b : IB) : ∀ (c : Nat) (f : IA → Nat) (k : Nat → Prot IA IB α),
    Prot.exec a b (Prot.numA f c k) = Prot.exec a b (k (f a % 2 ^ c)) ∧
    Prot.bits a b (Prot.numA f c k) = c + Prot.bits a b (k (f a % 2 ^ c)) := by
  intro c
  induction c with
  | zero => intro f k; simp [Prot.numA, Nat.mod_one]
  | succ c ih =>
    intro f k
    simp only [Prot.numA, Prot.exec, Prot.bits]
    have h := ih (fun a => f a / 2) (fun r => k (2 * r + ind (f a % 2 == 1)))
    simp only [mod_two_pow] at h
    rw [h.1, h.2]; exact ⟨rfl, by omega⟩

theorem numB_spec {IA IB α : Type} (a : IA) (b : IB) : ∀ (c : Nat) (g : IB → Nat) (k : Nat → Prot IA IB α),
    Prot.exec a b (Prot.numB g c k) = Prot.exec a b (k (g b % 2 ^ c)) ∧
    Prot.bits a b (Prot.numB g c k) = c + Prot.bits a b (k (g b % 2 ^ c)) := by
  intro c
  induction c with
  | zero => intro g k; simp [Prot.numB, Nat.mod_one]
  | succ c ih =>
    intro g k
    simp only [Prot.numB, Prot.exec, Prot.bits]
    have h := ih (fun b => g b / 2) (fun r => k (2 * r + ind (g b % 2 == 1)))
    simp only [mod_two_pow] at h
    rw [h.1, h.2]; exact ⟨rfl, by omega⟩

/-- Simulation of a cut-query algorithm when every answer splits as a public part plus Alice's
    part plus Bob's part: per query, Alice and Bob each send their part in c bits. -/
def simQ {IA IB α : Type} (c : Nat) (pub : (Nat → Bool) → Nat) (qa : IA → (Nat → Bool) → Nat)
    (qb : IB → (Nat → Bool) → Nat) : Alg α → Prot IA IB α
  | .ret r => .ret r
  | .ask S k => Prot.numA (fun a => qa a S) c (fun ra =>
      Prot.numB (fun b => qb b S) c (fun rb => simQ c pub qa qb (k (pub S + ra + rb))))

theorem simQ_spec {IA IB α : Type} (c : Nat) (pub : (Nat → Bool) → Nat) (qa : IA → (Nat → Bool) → Nat)
    (qb : IB → (Nat → Bool) → Nat) (a : IA) (b : IB)
    (ha : ∀ S, qa a S < 2 ^ c) (hb : ∀ S, qb b S < 2 ^ c) (A : Alg α) :
    Prot.exec a b (simQ c pub qa qb A) = Alg.run (fun S => pub S + qa a S + qb b S) A ∧
    Prot.bits a b (simQ c pub qa qb A) = 2 * c * Alg.cost (fun S => pub S + qa a S + qb b S) A := by
  induction A with
  | ret r => simp [simQ, Prot.exec, Prot.bits, Alg.run, Alg.cost]
  | ask S k ih =>
    simp only [simQ, Alg.run, Alg.cost]
    have h1 := numA_spec a b c (fun a => qa a S) (fun ra =>
      Prot.numB (fun b => qb b S) c (fun rb => simQ c pub qa qb (k (pub S + ra + rb))))
    have h2 := numB_spec a b c (fun b => qb b S) (fun rb => simQ c pub qa qb (k (pub S + qa a S % 2 ^ c + rb)))
    simp only [Nat.mod_eq_of_lt (ha S), Nat.mod_eq_of_lt (hb S)] at h1 h2
    rw [h1.1, h1.2, h2.1, h2.2, (ih _).1, (ih _).2]
    refine ⟨rfl, ?_⟩
    rw [Nat.mul_add]; omega


namespace Prot
variable {IA IB α : Type}
/-- Alice sends the vector (f a 0, ..., f a (p-1)), c bits per entry. -/
def vecA (f : IA → Nat → Nat) (c : Nat) : Nat → ((Nat → Nat) → Prot IA IB α) → Prot IA IB α
  | 0, k => k (fun _ => 0)
  | p + 1, k => vecA f c p (fun g => numA (fun a => f a p) c (fun r => k (fun v => if v = p then r else g v)))
def vecB (f : IB → Nat → Nat) (c : Nat) : Nat → ((Nat → Nat) → Prot IA IB α) → Prot IA IB α
  | 0, k => k (fun _ => 0)
  | p + 1, k => vecB f c p (fun g => numB (fun b => f b p) c (fun r => k (fun v => if v = p then r else g v)))
end Prot

theorem vec_upd (h : Nat → Nat) (p : Nat) :
    (fun v => if v = p then h p else (if v < p then h v else 0)) = (fun v => if v < p + 1 then h v else 0) := by
  funext v
  by_cases h1 : v = p
  · subst h1; simp
  · by_cases h2 : v < p
    · simp [h1, h2, show v < p + 1 by omega]
    · simp [h1, h2, show ¬ v < p + 1 by omega]

theorem vecA_spec {IA IB α : Type} (a : IA) (b : IB) (f : IA → Nat → Nat) (c : Nat)
    (hf : ∀ v, f a v < 2 ^ c) : ∀ (p : Nat) (k : (Nat → Nat) → Prot IA IB α),
    Prot.exec a b (Prot.vecA f c p k) = Prot.exec a b (k (fun v => if v < p then f a v else 0)) ∧
    Prot.bits a b (Prot.vecA f c p k) = p * c + Prot.bits a b (k (fun v => if v < p then f a v else 0)) := by
  intro p
  induction p with
  | zero => intro k; simp [Prot.vecA]
  | succ p ih =>
    intro k
    simp only [Prot.vecA]
    rw [(ih _).1, (ih _).2]
    have h := numA_spec a b c (fun a => f a p)
      (fun r => k (fun v => if v = p then r else (if v < p then f a v else 0)))
    rw [Nat.mod_eq_of_lt (hf p)] at h
    rw [h.1, h.2, vec_upd (f a) p, Nat.succ_mul]
    exact ⟨rfl, by omega⟩

theorem vecB_spec {IA IB α : Type} (a : IA) (b : IB) (f : IB → Nat → Nat) (c : Nat)
    (hf : ∀ v, f b v < 2 ^ c) : ∀ (p : Nat) (k : (Nat → Nat) → Prot IA IB α),
    Prot.exec a b (Prot.vecB f c p k) = Prot.exec a b (k (fun v => if v < p then f b v else 0)) ∧
    Prot.bits a b (Prot.vecB f c p k) = p * c + Prot.bits a b (k (fun v => if v < p then f b v else 0)) := by
  intro p
  induction p with
  | zero => intro k; simp [Prot.vecB]
  | succ p ih =>
    intro k
    simp only [Prot.vecB]
    rw [(ih _).1, (ih _).2]
    have h := numB_spec a b c (fun b => f b p)
      (fun r => k (fun v => if v = p then r else (if v < p then f b v else 0)))
    rw [Nat.mod_eq_of_lt (hf p)] at h
    rw [h.1, h.2, vec_upd (f b) p, Nat.succ_mul]
    exact ⟨rfl, by omega⟩

/-- Cut values are additive in the weights. -/
theorem q_add3 (n : Nat) (w1 w2 w3 : Nat → Nat → Nat) (S : Nat → Bool) :
    q n (fun u v => w1 u v + w2 u v + w3 u v) S = q n w1 S + q n w2 S + q n w3 S := by
  unfold q
  rw [← D_add, ← D_add]
  apply D_congr; intro u v _ _
  simp only [Nat.mul_add]

/-- Cut values of a graph with weights at most one fit in 2⌈log₂ n⌉ + 1 bits. -/
theorem q_lt_pow (n : Nat) (w : Nat → Nat → Nat) (hw : ∀ u v, w u v ≤ 1) (S : Nat → Bool) :
    q n w S < 2 ^ (2 * clog n + 1) := by
  have h1 : q n w S ≤ D n (fun _ _ => 1) := by
    unfold q; apply D_mono; intro u v _ _
    have := hw u v
    unfold ind; split <;> omega
  have h2 : D n (fun _ _ => 1) = n * n := by
    unfold D
    rw [lsum_congr _ _ (fun _ => n) (fun u _ => lsum_ones n)]
    rw [show (fun _ : Nat => n) = (fun x : Nat => (fun _ => 1) x * n) from by funext x; simp, lsum_mul, lsum_ones]
  have h3 : n * n ≤ 2 ^ clog n * 2 ^ clog n := Nat.mul_le_mul (clog_pow n) (clog_pow n)
  rw [← Nat.pow_add] at h3
  have h4 : 2 ^ (clog n + clog n) < 2 ^ (2 * clog n + 1) := by
    rw [show 2 * clog n + 1 = (clog n + clog n) + 1 by omega, Nat.pow_succ]
    have := Nat.two_pow_pos (clog n + clog n)
    omega
  omega

/-! ### Lemma 24: the triangle reduction as a communication protocol

  Γ_t on vertices a_i = i, b_j = t + j, c_i = 2t + i (i, j < t): public matching a_i c_i,
  Alice's edges a_i b_j (x_ij = 1) and Bob's edges b_j c_i (y_ij = 1). -/

def gPub (t : Nat) (u v : Nat) : Nat :=
  ind (decide (u < t) && v == u + 2 * t) + ind (decide (v < t) && u == v + 2 * t)
def gA (t : Nat) (x : Nat → Nat → Bool) (u v : Nat) : Nat :=
  ind (decide (u < t) && decide (t ≤ v) && decide (v < 2 * t) && x u (v - t)) +
  ind (decide (v < t) && decide (t ≤ u) && decide (u < 2 * t) && x v (u - t))
def gB (t : Nat) (y : Nat → Nat → Bool) (u v : Nat) : Nat :=
  ind (decide (t ≤ u) && decide (u < 2 * t) && decide (2 * t ≤ v) && decide (v < 3 * t) && y (v - 2 * t) (u - t)) +
  ind (decide (t ≤ v) && decide (v < 2 * t) && decide (2 * t ≤ u) && decide (u < 3 * t) && y (u - 2 * t) (v - t))
def gamma (t : Nat) (x y : Nat → Nat → Bool) (u v : Nat) : Nat := gPub t u v + gA t x u v + gB t y u v

theorem gA_le (t : Nat) (x : Nat → Nat → Bool) (u v : Nat) : gA t x u v ≤ 1 := by
  unfold gA ind
  by_cases h : u < t <;> by_cases h' : v < t <;> simp [h, h'] <;> (repeat' split) <;> omega
theorem gB_le (t : Nat) (y : Nat → Nat → Bool) (u v : Nat) : gB t y u v ≤ 1 := by
  unfold gB ind
  by_cases h : u < 2 * t <;> by_cases h' : v < 2 * t <;> simp [h, h'] <;> (repeat' split) <;> omega

/-- Decoding a vertex of Γ_t. -/
def gdec (t u : Nat) : Gv := if u < t then .a u else if u < 2 * t then .b (u - t) else .c (u - 2 * t)

def mask (t : Nat) (x : Nat → Nat → Bool) : Nat → Nat → Bool := fun i j => x i j && decide (i < t) && decide (j < t)

theorem gamma_gadj (t : Nat) (x y : Nat → Nat → Bool) (u v : Nat) (hu : u < 3 * t) (hv : v < 3 * t) :
    gamma t x y u v = ind (gadj (mask t x) (mask t y) (gdec t u) (gdec t v)) := by
  unfold gamma gPub gA gB gdec mask
  by_cases a1 : u < t <;> by_cases a2 : u < 2 * t <;> by_cases b1 : v < t <;> by_cases b2 : v < 2 * t <;>
    simp [a1, a2, b1, b2, gadj, ind] <;> (try omega)
  all_goals (repeat' split) <;> first | omega | (simp_all; done) | (simp_all; omega)

theorem gamma_triangle_nat (t : Nat) (x y : Nat → Nat → Bool) :
    (∃ u v w, u < 3 * t ∧ v < 3 * t ∧ w < 3 * t ∧
      1 ≤ gamma t x y u v ∧ 1 ≤ gamma t x y v w ∧ 1 ≤ gamma t x y u w) ↔
    ∃ i j, i < t ∧ j < t ∧ x i j = true ∧ y i j = true := by
  constructor
  · rintro ⟨u, v, w, hu, hv, hw, h1, h2, h3⟩
    rw [gamma_gadj t x y _ _ hu hv] at h1
    rw [gamma_gadj t x y _ _ hv hw] at h2
    rw [gamma_gadj t x y _ _ hu hw] at h3
    have g : ∀ b : Bool, 1 ≤ ind b → b = true := by intro b hb; cases b <;> simp_all [ind]
    obtain ⟨i, j, hx, hy⟩ := (gamma_triangle (mask t x) (mask t y)).mp ⟨_, _, _, g _ h1, g _ h2, g _ h3⟩
    simp only [mask, Bool.and_eq_true, decide_eq_true_eq] at hx hy
    exact ⟨i, j, hx.1.2, hx.2, hx.1.1, hy.1.1⟩
  · rintro ⟨i, j, hi, hj, hx, hy⟩
    refine ⟨i, t + j, 2 * t + i, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [gamma_gadj t x y _ _ (by omega) (by omega)]
      simp [gdec, hi, show ¬ t + j < t by omega, show t + j < 2 * t by omega, gadj, mask, hx, hj, ind, show t + j - t = j by omega]
    · rw [gamma_gadj t x y _ _ (by omega) (by omega)]
      simp [gdec, show ¬ t + j < t by omega, show t + j < 2 * t by omega, show ¬ 2 * t + i < t by omega,
        show ¬ 2 * t + i < 2 * t by omega, gadj, mask, hy, hi, hj, ind, show t + j - t = j by omega, show 2 * t + i - 2 * t = i by omega]
    · rw [gamma_gadj t x y _ _ (by omega) (by omega)]
      simp [gdec, hi, show ¬ 2 * t + i < t by omega, show ¬ 2 * t + i < 2 * t by omega, gadj, ind, show 2 * t + i - 2 * t = i by omega]

/-- Lemma 24, simulation step: any cut-query algorithm A on Γ_t becomes a protocol in which
    Alice holds x and Bob holds y; the protocol outputs exactly what A outputs on Γ_t(x, y)
    and uses 2(2⌈log₂ 3t⌉ + 1) bits per query. Applied seed by seed, a public-coin randomized
    algorithm becomes a public-coin protocol with the same output on every seed, hence the same
    error probability. -/
theorem triangle_protocol (t : Nat) {α : Type} (A : Alg α) (x y : Nat → Nat → Bool) :
    let c := 2 * clog (3 * t) + 1
    let P := simQ c (q (3 * t) (gPub t)) (fun x => q (3 * t) (gA t x)) (fun y => q (3 * t) (gB t y)) A
    Prot.exec x y P = Alg.run (q (3 * t) (gamma t x y)) A ∧
    Prot.bits x y P = 2 * c * Alg.cost (q (3 * t) (gamma t x y)) A := by
  intro c P
  have hO : (fun S => q (3 * t) (gPub t) S + q (3 * t) (gA t x) S + q (3 * t) (gB t y) S)
      = q (3 * t) (gamma t x y) := by
    funext S; unfold gamma; rw [q_add3]
  have := simQ_spec c (q (3 * t) (gPub t)) (fun x => q (3 * t) (gA t x)) (fun y => q (3 * t) (gB t y)) x y
    (fun S => q_lt_pow _ _ (gA_le t x) S) (fun S => q_lt_pow _ _ (gB_le t y) S) A
  rw [hO] at this
  exact this


/-! ### Lemma 26: Li's gadget with canonical attachments, and query preservation

  Base vertices 0..p-1 carry F = Fp + Fa + Fb (public, Alice's and Bob's edges); the clique W
  is p..p+M-1; base vertex v is attached to the first p - d_F(v) vertices of W. -/

def rb (p : Nat) (w : Nat → Nat → Nat) (u v : Nat) : Nat := ind (decide (u < p) && decide (v < p)) * w u v
def cliqueW (p M : Nat) (u v : Nat) : Nat :=
  ind (decide (p ≤ u) && decide (p ≤ v) && decide (u < p + M) && decide (v < p + M) && u != v)
def att (p : Nat) (d : Nat → Nat) (u v : Nat) : Nat :=
  ind (decide (u < p) && decide (p ≤ v) && decide (v < p + (p - d u)))
def liPub (p M : Nat) (Fp : Nat → Nat → Nat) (d : Nat → Nat) (u v : Nat) : Nat :=
  rb p Fp u v + cliqueW p M u v + att p d u v + att p d v u
def degF (p : Nat) (F : Nat → Nat → Nat) (v : Nat) : Nat := lsum (List.range p) (fun y => F v y)
/-- The canonical gadget L_{k,M}(F). -/
def liG (p M : Nat) (Fp Fa Fb : Nat → Nat → Nat) (u v : Nat) : Nat :=
  liPub p M Fp (degF p (fun a b => Fp a b + Fa a b + Fb a b)) u v + rb p Fa u v + rb p Fb u v

theorem att_congr (p : Nat) (d d' : Nat → Nat) (h : ∀ v, v < p → d v = d' v) (u v : Nat) :
    att p d u v = att p d' u v := by
  unfold att
  by_cases hu : u < p
  · rw [h u hu]
  · simp [hu]

theorem rb_le (p : Nat) (w : Nat → Nat → Nat) (hw : ∀ u v, w u v ≤ 1) (u v : Nat) : rb p w u v ≤ 1 := by
  unfold rb; have := hw u v; unfold ind; split <;> omega

theorem degF_lt (p : Nat) (w : Nat → Nat → Nat) (hw : ∀ u v, w u v ≤ 1) (v : Nat) :
    degF p w v < 2 ^ (clog p + 1) := by
  have h1 : degF p w v ≤ p := by
    unfold degF
    calc lsum (List.range p) (fun y => w v y) ≤ lsum (List.range p) (fun _ => 1) :=
          lsum_mono _ _ _ (fun y _ => hw v y)
      _ = p := lsum_ones p
  have := clog_pow p
  have := Nat.two_pow_pos (clog p)
  rw [Nat.pow_succ]; omega

/-- Lemma 26: after Alice and Bob exchange their contributions to the base degrees (p numbers of
    ⌈log₂ p⌉ + 1 bits each), every cut query to the gadget costs 2(2⌈log₂(p+M)⌉ + 1) bits, and
    the protocol outputs exactly what the cut-query algorithm outputs on L_{k,M}(F). -/
theorem li_protocol (p M : Nat) (Fp : Nat → Nat → Nat) {α : Type} (A : Alg α)
    (Fa Fb : Nat → Nat → Nat) (ha : ∀ u v, Fa u v ≤ 1) (hb : ∀ u v, Fb u v ≤ 1) :
    let c1 := clog p + 1
    let c := 2 * clog (p + M) + 1
    let P : Prot (Nat → Nat → Nat) (Nat → Nat → Nat) α :=
      Prot.vecA (fun F => degF p F) c1 p (fun gA => Prot.vecB (fun F => degF p F) c1 p (fun gB =>
        simQ c (q (p + M) (liPub p M Fp (fun v => degF p Fp v + gA v + gB v)))
          (fun F => q (p + M) (rb p F)) (fun F => q (p + M) (rb p F)) A))
    Prot.exec Fa Fb P = Alg.run (q (p + M) (liG p M Fp Fa Fb)) A ∧
    Prot.bits Fa Fb P = 2 * (p * c1) + 2 * c * Alg.cost (q (p + M) (liG p M Fp Fa Fb)) A := by
  intro c1 c P
  have hA := vecA_spec (α := α) Fa Fb (fun F => degF p F) c1 (fun v => degF_lt p Fa ha v) p
  have hB := vecB_spec (α := α) Fa Fb (fun F => degF p F) c1 (fun v => degF_lt p Fb hb v) p
  simp only [P]
  rw [(hA _).1, (hA _).2, (hB _).1, (hB _).2]
  have hS := simQ_spec c (q (p + M) (liPub p M Fp (fun v => degF p Fp v + (if v < p then degF p Fa v else 0)
      + (if v < p then degF p Fb v else 0))))
    (fun F => q (p + M) (rb p F)) (fun F => q (p + M) (rb p F)) Fa Fb
    (fun S => q_lt_pow _ _ (rb_le p Fa ha) S) (fun S => q_lt_pow _ _ (rb_le p Fb hb) S) A
  have hO : (fun S => q (p + M) (liPub p M Fp (fun v => degF p Fp v + (if v < p then degF p Fa v else 0)
      + (if v < p then degF p Fb v else 0))) S + q (p + M) (rb p Fa) S + q (p + M) (rb p Fb) S)
      = q (p + M) (liG p M Fp Fa Fb) := by
    funext S
    rw [← q_add3]
    unfold liG
    have hd : ∀ v, v < p → degF p Fp v + (if v < p then degF p Fa v else 0) + (if v < p then degF p Fb v else 0)
        = degF p (fun a b => Fp a b + Fa a b + Fb a b) v := by
      intro v hv
      simp only [hv, ite_true, degF]
      rw [lsum_add, lsum_add]
    have : ∀ u v, liPub p M Fp (fun v => degF p Fp v + (if v < p then degF p Fa v else 0)
        + (if v < p then degF p Fb v else 0)) u v
        = liPub p M Fp (degF p (fun a b => Fp a b + Fa a b + Fb a b)) u v := by
      intro u v; unfold liPub
      rw [att_congr p _ _ hd u v, att_congr p _ _ hd v u]
    simp only [this]
  rw [hO] at hS
  rw [hS.1, hS.2]
  exact ⟨rfl, by omega⟩

theorem lsum_lt_count (M r : Nat) (hr : r ≤ M) : lsum (List.range M) (fun i => ind (decide (i < r))) = r := by
  have := lsum_range_add r (fun i => ind (decide (i < r))) (M - r)
  rw [show r + (M - r) = M by omega] at this
  rw [this, lsum_congr _ _ (fun _ => 1) (fun i hi => by simp [ind, List.mem_range.mp hi]), lsum_ones,
    lsum_congr _ _ (fun _ => 0) (fun i _ => by simp [ind]), lsum_zero]
  omega

/-- The canonical gadget is a Li gadget: simple, W is a clique, and every base vertex has degree
    exactly p (the hypotheses `hdeg` of `li_gadget_lower` and `li_gadget_equality`). -/
theorem liG_shape (p M : Nat) (Fp Fa Fb : Nat → Nat → Nat) (hpM : p ≤ M)
    (hsym : ∀ u v, Fp u v + Fa u v + Fb u v = Fp v u + Fa v u + Fb v u)
    (hloop : ∀ u, Fp u u + Fa u u + Fb u u = 0)
    (hle : ∀ u v, Fp u v + Fa u v + Fb u v ≤ 1) :
    (∀ u v, liG p M Fp Fa Fb u v = liG p M Fp Fa Fb v u) ∧ (∀ u, liG p M Fp Fa Fb u u = 0) ∧
    (∀ u v, liG p M Fp Fa Fb u v ≤ 1) ∧
    (∀ u v, p ≤ u → p ≤ v → u < p + M → v < p + M → u ≠ v → liG p M Fp Fa Fb u v = 1) ∧
    (∀ v, v < p → deg (p + M) (liG p M Fp Fa Fb) v = p) := by
  generalize hd : degF p (fun a b => Fp a b + Fa a b + Fb a b) = d
  have hL : ∀ u v, liG p M Fp Fa Fb u v =
      ind (decide (u < p) && decide (v < p)) * (Fp u v + Fa u v + Fb u v) + cliqueW p M u v
        + att p d u v + att p d v u := by
    intro u v; unfold liG liPub rb; rw [hd]; simp only [Nat.mul_add]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v; rw [hL, hL, hsym u v]
    unfold cliqueW
    have e1 : (decide (u < p) && decide (v < p)) = (decide (v < p) && decide (u < p)) := Bool.and_comm _ _
    have e2 : (decide (p ≤ u) && decide (p ≤ v) && decide (u < p + M) && decide (v < p + M) && u != v)
        = (decide (p ≤ v) && decide (p ≤ u) && decide (v < p + M) && decide (u < p + M) && v != u) := by
      by_cases h : u = v
      · subst h; rfl
      · have h' : v ≠ u := fun e => h e.symm
        have e3 : (u != v) = true := by simp [h]
        have e4 : (v != u) = true := by simp [h']
        rw [e3, e4]
        cases decide (p ≤ u) <;> cases decide (p ≤ v) <;> cases decide (u < p + M) <;>
          cases decide (v < p + M) <;> rfl
    rw [e1, e2]; omega
  · intro u; rw [hL, hloop u]; simp [cliqueW, att, ind]; intro h1 h2; omega
  · intro u v; rw [hL]; have := hle u v
    unfold cliqueW att ind
    by_cases hu : u < p <;> by_cases hv : v < p <;> simp [hu, hv] <;> (repeat' split) <;> omega
  · intro u v hu hv hu' hv' huv; rw [hL]
    simp [cliqueW, att, ind, show ¬ u < p by omega, show ¬ v < p by omega, hu, hv, hu', hv', huv]
  · intro v hv
    unfold deg row
    have hdv : d v ≤ p := by
      rw [← hd]; unfold degF
      calc lsum (List.range p) (fun y => Fp v y + Fa v y + Fb v y) ≤ lsum (List.range p) (fun _ => 1) :=
            lsum_mono _ _ _ (fun y _ => hle v y)
        _ = p := lsum_ones p
    rw [lsum_range_add p _ M]
    have h1 : lsum (List.range p) (fun y => ind true * liG p M Fp Fa Fb v y) = d v := by
      rw [← hd]; unfold degF
      apply lsum_congr; intro y hy
      have hy := List.mem_range.mp hy
      rw [hL]; simp [cliqueW, att, ind, hv, hy, show ¬ p ≤ y by omega]; omega
    have h2 : lsum (List.range M) (fun i => ind true * liG p M Fp Fa Fb v (p + i)) = p - d v := by
      rw [← lsum_lt_count M (p - d v) (by omega)]
      apply lsum_congr; intro i _
      rw [hL]; simp [cliqueW, att, ind, hv, show ¬ p + i < p by omega]; omega
    rw [h1, h2]; omega


/-! ### Additive queries from cut queries (upper bound of Theorem 3, Grebinski–Kucherov step)

  After the n singleton queries, an additive query e(S) (`inner/2`, the number of edges inside S
  for symmetric weights) is answered by one cut query via e(S) = (Σ_{v∈S} d(v) - q(S)) / 2. -/

/-- Query the n singleton cuts. -/
def degsAlg : Nat → Alg (Nat → Nat)
  | 0 => .ret (fun _ => 0)
  | m + 1 => Alg.bind (degsAlg m) (fun g => .ask (sing m) (fun r => .ret (fun v => if v = m then r else g v)))

theorem degsAlg_spec (O : (Nat → Bool) → Nat) : ∀ m,
    Alg.run O (degsAlg m) = (fun v => if v < m then O (sing v) else 0) ∧ Alg.cost O (degsAlg m) = m := by
  intro m
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    simp only [degsAlg, Alg.run_bind, Alg.cost_bind, ih.1, ih.2, Alg.run, Alg.cost]
    refine ⟨?_, by simp [Alg.cost]⟩
    funext v
    by_cases h1 : v = m
    · subst h1; simp
    · by_cases h2 : v < m
      · simp [h1, h2, show v < m + 1 by omega]
      · simp [h1, h2, show ¬ v < m + 1 by omega]

/-- Replace each additive query by one cut query. -/
def addSim {α : Type} (n : Nat) (ds : Nat → Nat) : Alg α → Alg α
  | .ret r => .ret r
  | .ask S k => .ask S (fun r => addSim n ds (k ((lsum (List.range n) (fun x => ind (S x) * ds x) - r) / 2)))

theorem addSim_spec {α : Type} (n : Nat) (ds : Nat → Nat) (O E : (Nat → Bool) → Nat)
    (h : ∀ S, (lsum (List.range n) (fun x => ind (S x) * ds x) - O S) / 2 = E S) (A : Alg α) :
    Alg.run O (addSim n ds A) = Alg.run E A ∧ Alg.cost O (addSim n ds A) = Alg.cost E A := by
  induction A with
  | ret r => exact ⟨rfl, rfl⟩
  | ask S k ih =>
    simp only [addSim, Alg.run, Alg.cost, h S]
    exact ⟨(ih _).1, by rw [(ih _).2]⟩

theorem dq_sing_loop (n : Nat) (wt : Nat → Nat → Nat) (hloop : ∀ x, wt x x = 0) (v : Nat) (hv : v < n) :
    dq n wt (sing v) = deg n wt v := by
  unfold dq deg row sing
  have := D_left n v hv (fun x y => ind (!(y == v)) * wt x y)
  have e : lsum (List.range n) (fun y => ind ((fun _ => true) y) * wt v y)
      = lsum (List.range n) (fun y => ind (!(y == v)) * wt v y) := by
    apply lsum_congr; intro y _
    by_cases hy : y = v
    · subst hy; simp [hloop, ind]
    · simp [hy, ind]
  rw [e, ← this]
  apply D_congr; intro x y _ _
  by_cases hx : x = v
  · subst hx; by_cases hy : y = x
    · subst hy; simp [hloop, ind]
    · simp [hy, ind]
  · simp [hx, ind]

/-- An additive-query algorithm A becomes a cut-query algorithm with n extra queries and the
    same output. -/
theorem additive_from_cut (n : Nat) (wt : Nat → Nat → Nat) (hloop : ∀ x, wt x x = 0) {α : Type} (A : Alg α) :
    Alg.run (dq n wt) (Alg.bind (degsAlg n) (fun ds => addSim n ds A)) = Alg.run (fun S => inner n wt S / 2) A ∧
    Alg.cost (dq n wt) (Alg.bind (degsAlg n) (fun ds => addSim n ds A)) = n + Alg.cost (fun S => inner n wt S / 2) A := by
  rw [Alg.run_bind, Alg.cost_bind, (degsAlg_spec _ n).1, (degsAlg_spec _ n).2]
  have h : ∀ S, (lsum (List.range n) (fun x => ind (S x) * (fun v => if v < n then dq n wt (sing v) else 0) x)
      - dq n wt S) / 2 = inner n wt S / 2 := by
    intro S
    have e : lsum (List.range n) (fun x => ind (S x) * (fun v => if v < n then dq n wt (sing v) else 0) x)
        = lsum (List.range n) (fun x => ind (S x) * deg n wt x) := by
      apply lsum_congr; intro x hx
      have hx := List.mem_range.mp hx
      simp only [hx, ite_true, dq_sing_loop n wt hloop x hx]
    rw [e, sumdeg_identity]
    congr 1; omega
  have := addSim_spec n _ (dq n wt) (fun S => inner n wt S / 2) h A
  exact ⟨this.1, by rw [this.2]⟩

/-! ### Theorem 20: the fixed-slot adjacency array of H_x

  Vertex t·c + i (block c < 4, index i < t) has 2t - 1 slots. Slot s < t is the cross slot for
  partner index s; it returns a vertex in block `cross c b` where b is one bit of x
  (`slotBit`). Slots t ≤ s < 2t - 1 list the other vertices of the own block, independent
  of x. -/

def cross (c : Nat) (b : Bool) : Nat :=
  if c = 0 then (if b then 2 else 1) else if c = 1 then (if b then 3 else 0)
  else if c = 2 then (if b then 0 else 3) else (if b then 1 else 2)

def slotBit (t v s : Nat) : Nat × Nat := if blk t v = 0 ∨ blk t v = 3 then (idx t v, s) else (s, idx t v)

def nbrF (t v s : Nat) (b : Bool) : Nat :=
  if s < t then t * cross (blk t v) b + s
  else t * blk t v + (if s - t < idx t v then s - t else s - t + 1)

/-- The s-th entry of the adjacency array of vertex v in H_x. -/
def nbr (t : Nat) (x : Nat → Nat → Bool) (v s : Nat) : Nat := nbrF t v s (x (slotBit t v s).1 (slotBit t v s).2)

/-- Locality: each array entry depends on x only through the single bit at `slotBit t v s`, so
    a (coherent) array query costs O(1) queries to x. -/
theorem nbr_local (t : Nat) (x x' : Nat → Nat → Bool) (v s : Nat)
    (h : x (slotBit t v s).1 (slotBit t v s).2 = x' (slotBit t v s).1 (slotBit t v s).2) :
    nbr t x v s = nbr t x' v s := by
  unfold nbr; rw [h]

theorem enc_eq (t c c' i j : Nat) (ht : 0 < t) (hi : i < t) (hj : j < t) :
    t * c + i = t * c' + j ↔ c = c' ∧ i = j := by
  constructor
  · intro h
    have h1 := blk_eq t c i ht hi
    have h2 := idx_eq t c i hi
    rw [h] at h1 h2
    rw [blk_eq t c' j ht hj] at h1
    rw [idx_eq t c' j hj] at h2
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem wx_blk (t c c' i j : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (hi : i < t) (hj : j < t) :
    wx t x (t * c + i) (t * c' + j) =
      ind ((!(c == c') || !(i == j)) && (decide (c < 2) == decide (c' < 2)) &&
        !((c == 0 && c' == 1 && x i j) || (c == 1 && c' == 0 && x j i) ||
          (c == 2 && c' == 3 && x j i) || (c == 3 && c' == 2 && x i j))) +
      ind ((c == 0 && c' == 2 && x i j) || (c == 2 && c' == 0 && x j i) ||
        (c == 1 && c' == 3 && x j i) || (c == 3 && c' == 1 && x i j)) := by
  unfold wx halfA
  rw [remB_blk t c c' i j x ht hi hj, addB_blk t c c' i j x ht hi hj, blk_eq t c i ht hi, blk_eq t c' j ht hj]
  have e : (t * c + i != t * c' + j) = (!(c == c') || !(i == j)) := by
    by_cases h : t * c + i = t * c' + j
    · have := (enc_eq t c c' i j ht hi hj).mp h
      simp [h, this.1, this.2]
    · have : ¬ (c = c' ∧ i = j) := fun hh => h ((enc_eq t c c' i j ht hi hj).mpr hh)
      have hb : (t * c + i != t * c' + j) = true := by simp [h]
      rw [hb]
      by_cases hc : c = c'
      · have : i ≠ j := fun e => this ⟨hc, e⟩
        simp [hc, this]
      · simp [hc]
  rw [e]

theorem slot_decomp (t v : Nat) (ht : 0 < t) (hv : v < t * 4) :
    ∃ c i, c < 4 ∧ i < t ∧ v = t * c + i ∧ blk t v = c ∧ idx t v = i := by
  refine ⟨v / t, v % t, ?_, Nat.mod_lt _ ht, (Nat.div_add_mod v t).symm, rfl, rfl⟩
  exact (Nat.div_lt_iff_lt_mul ht).mpr (by omega)

/-- Every array entry is a neighbour of v in H_x. -/
theorem nbr_adj (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (v s : Nat) (hv : v < t * 4)
    (hs : s < 2 * t - 1) : nbr t x v s < t * 4 ∧ wx t x v (nbr t x v s) = 1 := by
  obtain ⟨c, i, hc, hi, rfl, hb, hix⟩ := slot_decomp t v ht hv
  unfold nbr nbrF slotBit
  rw [hb, hix]
  by_cases hst : s < t
  · simp only [hst, ite_true]
    have hcr : ∀ b, cross c b < 4 := by intro b; unfold cross; (repeat' split) <;> omega
    constructor
    · have := hcr (x (if c = 0 ∨ c = 3 then (i, s) else (s, i)).1 (if c = 0 ∨ c = 3 then (i, s) else (s, i)).2)
      have := Nat.mul_le_mul_left t (show cross c _ + 1 ≤ 4 from this)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    · rw [wx_blk t c _ i s x ht hi hst]
      rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
      · cases hb' : x i s <;> simp [cross, hb', ind]
      · cases hb' : x s i <;> simp [cross, hb', ind]
      · cases hb' : x s i <;> simp [cross, hb', ind]
      · cases hb' : x i s <;> simp [cross, hb', ind]
  · simp only [hst, ite_false]
    have hr : (if s - t < i then s - t else s - t + 1) < t := by split <;> omega
    have hri : (if s - t < i then s - t else s - t + 1) ≠ i := by split <;> omega
    generalize (if s - t < i then s - t else s - t + 1) = r at hr hri ⊢
    constructor
    · have := Nat.mul_le_mul_left t (show c + 1 ≤ 4 by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    · rw [wx_blk t c c i r x ht hi hr]
      have : (i == r) = false := by simp; omega
      rw [this]
      rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> simp [ind]

/-- Distinct slots hold distinct entries (no collisions). -/
theorem nbr_inj (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (v s s' : Nat) (hv : v < t * 4)
    (hs : s < 2 * t - 1) (hs' : s' < 2 * t - 1) (h : nbr t x v s = nbr t x v s') : s = s' := by
  obtain ⟨c, i, hc, hi, rfl, hb, hix⟩ := slot_decomp t v ht hv
  unfold nbr nbrF at h
  rw [hb, hix] at h
  have hne : ∀ b, cross c b ≠ c := by
    intro b; unfold cross
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> cases b <;> simp
  by_cases h1 : s < t <;> by_cases h2 : s' < t <;> simp only [h1, h2, ite_true, ite_false] at h
  · exact ((enc_eq t _ _ s s' ht h1 h2).mp h).2
  · have hr : (if s' - t < i then s' - t else s' - t + 1) < t := by split <;> omega
    exact absurd ((enc_eq t _ _ s _ ht h1 hr).mp h).1 (hne _)
  · have hr : (if s - t < i then s - t else s - t + 1) < t := by split <;> omega
    exact absurd ((enc_eq t _ _ _ s' ht hr h2).mp h).1.symm (hne _)
  · have hr : (if s - t < i then s - t else s - t + 1) < t := by split <;> omega
    have hr' : (if s' - t < i then s' - t else s' - t + 1) < t := by split <;> omega
    have := ((enc_eq t _ _ _ _ ht hr hr').mp h).2
    split at this <;> split at this <;> omega

/-- Every neighbour of v in H_x appears in some slot, so the array lists the neighbourhood
    exactly once (with `nbr_adj`, `nbr_inj`); the degree 2t - 1 does not depend on x
    (`Hx_regular`). -/
theorem nbr_complete (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (v u : Nat) (hv : v < t * 4)
    (hu : u < t * 4) (h : 1 ≤ wx t x v u) : ∃ s, s < 2 * t - 1 ∧ nbr t x v s = u := by
  obtain ⟨c, i, hc, hi, rfl, hb, hix⟩ := slot_decomp t v ht hv
  obtain ⟨c', j, hc', hj, rfl, _, _⟩ := slot_decomp t u ht hu
  rw [wx_blk t c c' i j x ht hi hj] at h
  by_cases hcc : c = c'
  · subst hcc
    have hij : i ≠ j := by
      intro e; subst e
      rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> simp [ind] at h
    refine ⟨t + (if j < i then j else j - 1), by split <;> omega, ?_⟩
    unfold nbr nbrF
    rw [hb, hix]
    simp only [show ¬ (t + (if j < i then j else j - 1) < t) by omega, ite_false,
      show t + (if j < i then j else j - 1) - t = (if j < i then j else j - 1) by omega]
    congr 1
    by_cases hj' : j < i
    · simp [hj']
    · simp [hj', show ¬ (j - 1 < i) by omega]; omega
  · refine ⟨j, by omega, ?_⟩
    unfold nbr nbrF slotBit
    rw [hb, hix]
    simp only [hj, ite_true]
    congr 2
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : c' = 0 ∨ c' = 1 ∨ c' = 2 ∨ c' = 3) with rfl | rfl | rfl | rfl <;>
    simp at hcc <;> simp [cross] <;> (try cases hx1 : x i j) <;> (try cases hx2 : x j i) <;>
      simp_all [ind]


/-! ### Lemma 27: the composed reduction DISJ → Γ_t → L_{k,M}(Γ_t) -/

namespace Prot
/-- Run a protocol on transformed inputs (each player transforms their own input locally). -/
def comap {IA IB IA' IB' α : Type} (fa : IA' → IA) (fb : IB' → IB) : Prot IA IB α → Prot IA' IB' α
  | ret r => ret r
  | sendA f k => sendA (fun a => f (fa a)) (fun bit => comap fa fb (k bit))
  | sendB g k => sendB (fun b => g (fb b)) (fun bit => comap fa fb (k bit))

theorem comap_spec {IA IB IA' IB' α : Type} (fa : IA' → IA) (fb : IB' → IB) (a : IA') (b : IB')
    (P : Prot IA IB α) :
    exec a b (comap fa fb P) = exec (fa a) (fb b) P ∧ bits a b (comap fa fb P) = bits (fa a) (fb b) P := by
  induction P with
  | ret r => exact ⟨rfl, rfl⟩
  | sendA f k ih => simp only [comap, exec, bits]; exact ⟨(ih _).1, by rw [(ih _).2]⟩
  | sendB g k ih => simp only [comap, exec, bits]; exact ⟨(ih _).1, by rw [(ih _).2]⟩
end Prot

theorem gamma_simple (t : Nat) (x y : Nat → Nat → Bool) :
    (∀ u v, gPub t u v + gA t x u v + gB t y u v = gPub t v u + gA t x v u + gB t y v u) ∧
    (∀ u, gPub t u u + gA t x u u + gB t y u u = 0) ∧
    (∀ u v, gPub t u v + gA t x u v + gB t y u v ≤ 1) := by
  refine ⟨fun u v => ?_, fun u => ?_, fun u v => ?_⟩
  · unfold gPub gA gB; omega
  · unfold gPub gA gB ind
    by_cases h1 : u < t <;> by_cases h2 : u < 2 * t <;> simp [h1, h2] <;> (repeat' split) <;> omega
  · unfold gPub gA gB ind
    by_cases a1 : u < t <;> by_cases a2 : u < 2 * t <;> by_cases b1 : v < t <;> by_cases b2 : v < 2 * t <;>
      simp [a1, a2, b1, b2] <;> (repeat' split) <;> omega

/-- Lemma 27, simulation part: Alice (holding x) and Bob (holding y) simulate any cut-query
    algorithm on Li's gadget L_{k,M}(Γ_t(x, y)) exactly, with 2·3t(⌈log₂ 3t⌉ + 1) bits of
    preprocessing and 2(2⌈log₂(3t + M)⌉ + 1) bits per query; the gadget is simple, its clique is
    complete and its base vertices have degree 3t (`liG_shape`, `gamma_simple`). -/
theorem kge4_protocol (t M : Nat) {α : Type} (A : Alg α) (x y : Nat → Nat → Bool) :
    let c1 := clog (3 * t) + 1
    let c := 2 * clog (3 * t + M) + 1
    let P : Prot (Nat → Nat → Nat) (Nat → Nat → Nat) α :=
      Prot.vecA (fun F => degF (3 * t) F) c1 (3 * t) (fun gA => Prot.vecB (fun F => degF (3 * t) F) c1 (3 * t)
        (fun gB => simQ c (q (3 * t + M) (liPub (3 * t) M (gPub t)
          (fun v => degF (3 * t) (gPub t) v + gA v + gB v)))
          (fun F => q (3 * t + M) (rb (3 * t) F)) (fun F => q (3 * t + M) (rb (3 * t) F)) A))
    Prot.exec x y (Prot.comap (gA t) (gB t) P) = Alg.run (q (3 * t + M) (liG (3 * t) M (gPub t) (gA t x) (gB t y))) A ∧
    Prot.bits x y (Prot.comap (gA t) (gB t) P) =
      2 * (3 * t * c1) + 2 * c * Alg.cost (q (3 * t + M) (liG (3 * t) M (gPub t) (gA t x) (gB t y))) A := by
  intro c1 c P
  rw [(Prot.comap_spec _ _ x y P).1, (Prot.comap_spec _ _ x y P).2]
  exact li_protocol (3 * t) M (gPub t) A (gA t x) (gB t y) (gA_le t x) (gB_le t y)



end MinKCut
