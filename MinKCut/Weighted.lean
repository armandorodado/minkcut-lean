import MinKCut.Gamma
/-! # Part K: Proposition 29 (weighted deterministic lower bound) -/

namespace MinKCut

/-! ## Part K: integer linear algebra and the weighted deterministic lower bound (Proposition 29) -/

def isum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | N + 1, f => isum N f + f N

theorem isum_congr (f g : Nat → Int) : ∀ N, (∀ j, j < N → f j = g j) → isum N f = isum N g := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih => intro h; simp only [isum]; rw [ih (fun j hj => h j (by omega)), h N (by omega)]

theorem isum_add (f g : Nat → Int) : ∀ N, isum N (fun j => f j + g j) = isum N f + isum N g := by
  intro N
  induction N with
  | zero => simp [isum]
  | succ N ih => simp only [isum]; rw [ih]; omega

theorem isum_mul (c : Int) (f : Nat → Int) : ∀ N, isum N (fun j => c * f j) = c * isum N f := by
  intro N
  induction N with
  | zero => simp [isum]
  | succ N ih => simp only [isum]; rw [ih, Int.mul_add]

theorem isum_zero : ∀ N, isum N (fun _ => 0) = 0 := by
  intro N; induction N with
  | zero => rfl
  | succ N ih => simp [isum, ih]

/-- Number of free (not forced to zero) unknowns among 0..N-1. -/
def free (Z : Nat → Bool) : Nat → Nat
  | 0 => 0
  | N + 1 => free Z N + (if Z N then 0 else 1)

/-- Size bound for the solution produced by elimination (depends only on N and c). -/
def bnd : Nat → Nat → Nat
  | 0, _ => 1
  | N + 1, c => (N + 1) * (c + 1) * bnd N (c * c + c * c + c)

theorem bnd_pos : ∀ N c, 1 ≤ bnd N c := by
  intro N; induction N with
  | zero => intro c; simp [bnd]
  | succ N ih => intro c; simp only [bnd]; have := ih (c * c + c * c + c)
                 exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) this

theorem bnd_mono : ∀ N c c', c ≤ c' → bnd N c ≤ bnd N c' := by
  intro N; induction N with
  | zero => intro c c' _; simp [bnd]
  | succ N ih =>
    intro c c' h
    simp only [bnd]
    have h2 : c * c + c * c + c ≤ c' * c' + c' * c' + c' := by
      have := Nat.mul_le_mul h h; omega
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (ih _ _ h2)

theorem natAbs_isum (f : Nat → Int) (b : Nat) : ∀ N, (∀ j, j < N → (f j).natAbs ≤ b) →
    (isum N f).natAbs ≤ N * b := by
  intro N; induction N with
  | zero => intro _; simp [isum]
  | succ N ih =>
    intro h
    simp only [isum]
    have := ih (fun j hj => h j (by omega))
    have := h N (by omega)
    have := Int.natAbs_add_le (isum N f) (f N)
    rw [Nat.succ_mul]; omega

/-- Elimination with bounds: a homogeneous integer system with fewer equations than free
    unknowns has a nonzero solution vanishing on the forced unknowns, with entries bounded by
    `bnd N c` when the coefficients are bounded by c. -/
theorem homogB : ∀ (N m c : Nat) (E : Nat → Nat → Int) (Z : Nat → Bool), m < free Z N →
    (∀ i j, (E i j).natAbs ≤ c) →
    ∃ x : Nat → Int, (∃ j, j < N ∧ Z j = false ∧ x j ≠ 0) ∧ (∀ j, Z j = true → x j = 0) ∧
      (∀ j, (x j).natAbs ≤ bnd N c) ∧ ∀ i, i < m → isum N (fun j => E i j * x j) = 0 := by
  intro N
  induction N with
  | zero => intro m c E Z h; simp [free] at h
  | succ N ih =>
    intro m c E Z hm hc
    by_cases hZ : Z N = true
    · -- unknown N is forced to zero
      have hm' : m < free Z N := by simp only [free, hZ, ite_true] at hm; omega
      obtain ⟨y, ⟨j0, hj0, hz0, hy0⟩, hyZ, hyb, hy⟩ := ih m c E Z hm' hc
      refine ⟨fun j => if j = N then 0 else y j, ⟨j0, by omega, hz0, by simp [show j0 ≠ N by omega, hy0]⟩,
        ?_, ?_, ?_⟩
      · intro j hj; by_cases h : j = N
        · simp [h]
        · simp [h, hyZ j hj]
      · intro j
        have hb : bnd N c ≤ bnd (N + 1) c := by
          simp only [bnd]
          have h1 := bnd_mono N c (c * c + c * c + c) (by omega)
          have h2 : 1 ≤ (N + 1) * (c + 1) := Nat.mul_pos (by omega) (by omega)
          calc bnd N c ≤ bnd N (c * c + c * c + c) := h1
            _ = 1 * bnd N (c * c + c * c + c) := by omega
            _ ≤ (N + 1) * (c + 1) * bnd N (c * c + c * c + c) := Nat.mul_le_mul_right _ h2
        by_cases h : j = N
        · simp [h]
        · simp only [h, ite_false]; exact Nat.le_trans (hyb j) hb
      · intro i hi
        simp only [isum, ite_true, Int.mul_zero, Int.add_zero]
        rw [isum_congr _ (fun j => E i j * y j) N (fun j hj => by simp [show j ≠ N by omega])]
        exact hy i hi
    · have hZf : Z N = false := by simpa using hZ
      have hfree : free Z (N + 1) = free Z N + 1 := by simp [free, hZf]
      by_cases hz : ∀ i, i < m → E i N = 0
      · refine ⟨fun j => if j = N then 1 else 0, ⟨N, by omega, hZf, by simp⟩, ?_, ?_, ?_⟩
        · intro j hj; by_cases h : j = N
          · subst h; rw [hZf] at hj; exact absurd hj (by simp)
          · simp [h]
        · intro j; have := bnd_pos (N + 1) c; by_cases h : j = N <;> simp [h] <;> omega
        · intro i hi
          simp only [isum]
          rw [isum_congr _ (fun _ => 0) N (fun j hj => by simp [show j ≠ N by omega]), isum_zero]
          simp [hz i hi]
      · have : ∃ p, p < m ∧ E p N ≠ 0 := by
          apply Classical.byContradiction
          intro h; apply hz; intro i hi
          apply Classical.byContradiction; intro h2; exact h ⟨i, hi, h2⟩
        obtain ⟨p, hp, ha⟩ := this
        let idx := fun k => if k < p then k else k + 1
        let E' := fun k j => (E p N) * E (idx k) j - E (idx k) N * E p j
        have hc' : ∀ k j, (E' k j).natAbs ≤ c * c + c * c + c := by
          intro k j
          have h1 := Int.natAbs_sub_le ((E p N) * E (idx k) j) (E (idx k) N * E p j)
          rw [Int.natAbs_mul, Int.natAbs_mul] at h1
          have h2 := Nat.mul_le_mul (hc p N) (hc (idx k) j)
          have h3 := Nat.mul_le_mul (hc (idx k) N) (hc p j)
          show ((E p N) * E (idx k) j - E (idx k) N * E p j).natAbs ≤ _
          omega
        obtain ⟨y, ⟨j0, hj0, hz0, hy0⟩, hyZ, hyb, hy⟩ := ih (m - 1) (c * c + c * c + c) E' Z (by omega) hc'
        let S := isum N (fun j => E p j * y j)
        refine ⟨fun j => if j = N then -S else (E p N) * y j, ⟨j0, by omega, hz0, ?_⟩, ?_, ?_, ?_⟩
        · simp only [show j0 ≠ N by omega, ite_false]
          exact Int.mul_ne_zero ha hy0
        · intro j hj
          by_cases h : j = N
          · subst h; rw [hZf] at hj; exact absurd hj (by simp)
          · simp [h, hyZ j hj]
        · intro j
          have hB : bnd (N + 1) c = (N + 1) * (c + 1) * bnd N (c * c + c * c + c) := rfl
          by_cases h : j = N
          · simp only [h, ite_true]
            rw [Int.natAbs_neg]
            have := natAbs_isum (fun j => E p j * y j) (c * bnd N (c * c + c * c + c)) N (by
              intro j _
              rw [Int.natAbs_mul]; exact Nat.mul_le_mul (hc p j) (hyb j))
            have e1 : N * (c * bnd N (c * c + c * c + c)) ≤ (N + 1) * (c + 1) * bnd N (c * c + c * c + c) := by
              rw [← Nat.mul_assoc]
              exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
            omega
          · simp only [h, ite_false]
            rw [Int.natAbs_mul]
            have e1 := Nat.mul_le_mul (hc p N) (hyb j)
            have e2 : c * bnd N (c * c + c * c + c) ≤ (N + 1) * (c + 1) * bnd N (c * c + c * c + c) := by
              apply Nat.mul_le_mul_right
              calc c ≤ 1 * (c + 1) := by omega
                _ ≤ (N + 1) * (c + 1) := Nat.mul_le_mul_right _ (by omega)
            omega
        · intro i hi
          simp only [isum, ite_true]
          have hcong : ∀ (c : Nat → Int), isum N (fun j => c j * (if j = N then -S else (E p N) * y j))
              = (E p N) * isum N (fun j => c j * y j) := by
            intro c
            rw [← isum_mul]
            apply isum_congr; intro j hj
            simp only [show j ≠ N by omega, ite_false]
            rw [Int.mul_left_comm]
          rw [hcong]
          by_cases hip : i = p
          · subst hip
            show (E i N) * S + (E i N) * -S = 0
            rw [Int.mul_neg]; omega
          · have hk : ∃ k, k < m - 1 ∧ idx k = i := by
              by_cases h : i < p
              · exact ⟨i, by omega, by simp [idx, h]⟩
              · have h2 : ¬ (i - 1 < p) := by omega
                exact ⟨i - 1, by omega, by simp only [idx, h2, ite_false]; omega⟩
            obtain ⟨k, hk1, hk2⟩ := hk
            have := hy k hk1
            have e : isum N (fun j => E' k j * y j)
                = (E p N) * isum N (fun j => E i j * y j) - E i N * S := by
              have h1 : (fun j => E' k j * y j) = (fun j => (E p N) * (E i j * y j) + (-(E i N)) * (E p j * y j)) := by
                funext j
                simp only [E', hk2]
                simp only [Int.sub_eq_add_neg, Int.add_mul, Int.neg_mul, Int.mul_assoc]
              rw [h1, isum_add, isum_mul, isum_mul, Int.neg_mul]
              simp only [S]
              omega
            rw [e] at this
            rw [Int.mul_neg]
            simp only [S] at this ⊢
            omega

/-! ### Part K: the weighted deterministic lower bound (Proposition 29) -/

/-- The sequence of query sets asked by A against oracle O. -/
def trace {α : Type} (O : (Nat → Bool) → Nat) : Alg α → List (Nat → Bool)
  | .ret _ => []
  | .ask S k => S :: trace O (k (O S))

theorem trace_length {α : Type} (O : (Nat → Bool) → Nat) (A : Alg α) :
    (trace O A).length = Alg.cost O A := by
  induction A with
  | ret a => rfl
  | ask S k ih => simp only [trace, Alg.cost, List.length_cons]; rw [ih]; omega

/-- Determinism/adaptivity: an oracle agreeing with O on every query asked under O produces the
    same run and the same cost. -/
theorem trace_agree {α : Type} (O1 O2 : (Nat → Bool) → Nat) (A : Alg α)
    (h : ∀ i, i < (trace O1 A).length → O2 ((trace O1 A).getD i (fun _ => false))
      = O1 ((trace O1 A).getD i (fun _ => false))) :
    Alg.run O2 A = Alg.run O1 A ∧ Alg.cost O2 A = Alg.cost O1 A := by
  induction A with
  | ret a => exact ⟨rfl, rfl⟩
  | ask S k ih =>
    have h0 := h 0 (by simp [trace])
    simp only [trace, List.getD_cons_zero] at h0
    simp only [Alg.run, Alg.cost]
    rw [h0]
    have := ih (O1 S) (fun i hi => by
      have := h (i + 1) (by simp only [trace, List.length_cons]; omega)
      simpa [trace, List.getD_cons_succ] using this)
    exact ⟨this.1, by rw [this.2]⟩

theorem D_flat (n : Nat) (f : Nat → Nat → Nat) :
    D n f = lsum (List.range (n * n)) (fun j => f (j / n) (j % n)) := by
  rw [lsum_blocks]
  unfold D
  apply lsum_congr; intro u hu
  apply lsum_congr; intro v hv
  have hu := List.mem_range.mp hu
  have hv := List.mem_range.mp hv
  have h1 : (n * u + v) / n = u := by
    rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hv]; omega
  have h2 : (n * u + v) % n = v := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
  rw [h1, h2]

theorem D_swap (n : Nat) (f : Nat → Nat → Nat) : D n (fun u v => f v u) = D n f := by
  unfold D; rw [lsum_swap]

/-- Symmetric weighting of K_n given by one value per unordered pair {u < v}, stored at index
    n·u + v. -/
def W (n : Nat) (y : Nat → Nat) (u v : Nat) : Nat :=
  if u < v then y (n * u + v) else if v < u then y (n * v + u) else 0

theorem W_symm (n : Nat) (y : Nat → Nat) (u v : Nat) : W n y u v = W n y v u := by
  unfold W
  by_cases h1 : u < v
  · simp [h1, show ¬ v < u by omega]
  · by_cases h2 : v < u
    · simp [h1, h2]
    · simp [h1, h2]

theorem W_loop (n : Nat) (y : Nat → Nat) (u : Nat) : W n y u u = 0 := by simp [W]

/-- The pair indices: j encodes (j / n, j % n); only j with j / n < j % n are used. -/
def Zf (n : Nat) (j : Nat) : Bool := !decide (j / n < j % n)

theorem pair_sum (n : Nat) (y : Nat → Nat) (F : Nat → Nat → Nat) (hF : ∀ u v, F u v = F v u) :
    D n (fun u v => F u v * W n y u v)
      = 2 * lsum (List.range (n * n)) (fun j => ind (!Zf n j) * F (j / n) (j % n) * y j) := by
  let G : Nat → Nat → Nat := fun u v => ind (decide (u < v)) * F u v * y (n * u + v)
  have hpt : ∀ u v, F u v * W n y u v = G u v + G v u := by
    intro u v
    simp only [G, W]
    by_cases h1 : u < v
    · simp [h1, show ¬ v < u by omega, ind]
    · by_cases h2 : v < u
      · simp [h1, h2, ind, hF u v]
      · simp [h1, h2, ind]
  rw [show (fun u v => F u v * W n y u v) = (fun u v => G u v + G v u) from by
    funext u v; exact hpt u v]
  rw [D_add, D_swap n G, D_flat]
  have : ∀ j, G (j / n) (j % n) = ind (!Zf n j) * F (j / n) (j % n) * y j := by
    intro j
    simp only [G, Zf, Bool.not_not]
    rw [Nat.div_add_mod]
  rw [lsum_congr _ _ _ (fun j _ => this j)]
  omega

theorem lsum_cast (g : Nat → Nat) : ∀ N,
    ((lsum (List.range N) g : Nat) : Int) = isum N (fun j => (g j : Int)) := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, lsum_append, Int.ofNat_add, ih]
    simp [lsum, isum]

theorem free_lsum (Z : Nat → Bool) : ∀ N, free Z N = lsum (List.range N) (fun j => ind (!Z j)) := by
  intro N
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, lsum_append, ← ih]
    simp only [free, lsum]
    cases Z N <;> simp [ind]

theorem rowK (n u : Nat) (hu : u < n) : lsum (List.range n) (fun v => ind (u != v)) = n - 1 := by
  have h1 := lsum_add (List.range n) (fun v => ind (u != v)) (fun v => ind (u == v))
  rw [lsum_congr _ _ (fun _ => 1) (fun v _ => ind_pair2 u v), lsum_ones] at h1
  have h2 := count_one u true n
  simp only [Bool.and_true, hu, decide_true, ind_true] at h2
  omega

theorem free_pairs (n : Nat) : 2 * free (Zf n) (n * n) = n * (n - 1) := by
  rw [free_lsum]
  have h0 : lsum (List.range (n * n)) (fun j => ind (!Zf n j))
      = D n (fun u v => ind (decide (u < v))) := by
    rw [D_flat]; apply lsum_congr; intro j _; simp [Zf]
  rw [h0]
  have h1 : D n (fun u v => ind (decide (u < v))) + D n (fun u v => ind (decide (v < u)))
      = D n (fun u v => ind (u != v)) := by
    rw [← D_add]; apply D_congr; intro u v _ _
    by_cases h : u < v
    · simp [h, show ¬ v < u by omega, show u ≠ v by omega, ind]
    · by_cases h' : v < u
      · simp [h, h', show u ≠ v by omega, ind]
      · simp [h, h', show u = v by omega, ind]
  rw [D_swap n (fun u v => ind (decide (u < v)))] at h1
  have h2 : D n (fun u v => ind (u != v)) = lsum (List.range n) (fun _ => n - 1) := by
    unfold D; apply lsum_congr; intro u hu; exact rowK n u (List.mem_range.mp hu)
  have h3 : lsum (List.range n) (fun _ => n - 1) = n * (n - 1) := by
    rw [show (fun _ : Nat => n - 1) = (fun x : Nat => (fun _ => 1) x * (n - 1)) from by funext x; simp,
      lsum_mul, lsum_ones]
  omega

theorem deg_pairs (n : Nat) (y : Nat → Nat) (x : Nat) (hx : x < n) :
    deg n (W n y) x = lsum (List.range (n * n))
      (fun j => ind (!Zf n j) * ind (j / n == x || j % n == x) * y j) := by
  have h := pair_sum n y (fun u v => ind (u == x || v == x)) (by intro u v; simp [Bool.or_comm])
  dsimp only at h
  have h2 : D n (fun u v => ind (u == x || v == x) * W n y u v)
      = D n (fun u v => ind (u == x) * W n y u v) + D n (fun u v => ind (v == x) * W n y u v) := by
    rw [← D_add]; apply D_congr; intro u v _ _
    by_cases hu : u = x
    · by_cases hv : v = x
      · subst hu hv; simp [W_loop]
      · simp [hu, hv, ind]
    · by_cases hv : v = x
      · simp [hu, hv, ind]
      · simp [hu, hv, ind]
  rw [D_left n x hx, D_right n x hx] at h2
  have h3 : lsum (List.range n) (fun u => W n y u x) = lsum (List.range n) (fun v => W n y x v) := by
    apply lsum_congr; intro u _; exact W_symm n y u x
  have hd : deg n (W n y) x = lsum (List.range n) (fun v => W n y x v) := by
    unfold deg row; apply lsum_congr; intro v _; simp [ind]
  omega

theorem D_mul_const (n K : Nat) (f : Nat → Nat → Nat) : D n (fun u v => f u v * K) = D n f * K := by
  unfold D
  rw [lsum_congr _ _ (fun u => lsum (List.range n) (fun v => f u v) * K) (fun u _ => lsum_mul _ _ _),
    lsum_mul]

theorem W_const (n K : Nat) (u v : Nat) : W n (fun _ => K) u v = wK u v * K := by
  unfold W wK
  by_cases h : u < v
  · simp [h, show u ≠ v by omega, ind]
  · by_cases h' : v < u
    · simp [h, h', show u ≠ v by omega, ind]
    · simp [h, h', show u = v by omega, ind]

theorem cost_const (n K : Nat) (lab : Nat → Nat) :
    cost n (W n (fun _ => K)) lab = cost n wK lab * K := by
  unfold cost
  rw [← D_mul_const]
  apply D_congr; intro u v _ _; rw [W_const, Nat.mul_assoc]

theorem deg_wK (n x : Nat) (hx : x < n) : deg n wK x = n - 1 := by
  unfold deg row wK
  rw [lsum_congr _ _ (fun v => ind (x != v)) (fun v _ => by simp [ind])]
  exact rowK n x hx

theorem kn_labUV (n a b : Nat) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    cost n wK (labUV a b) = 2 * (2 * n - 3) := by
  have h := two_singleton_value n wK (by
    intro x y; unfold wK
    by_cases h : x = y
    · subst h; rfl
    · have : y ≠ x := fun e => h e.symm
      have e1 : (x != y) = true := by simp [h]
      have e2 : (y != x) = true := by simp [this]
      rw [e1, e2]) (by intro x; simp [wK, ind])
    a b ha hb hab
  rw [deg_wK n a ha, deg_wK n b hb] at h
  have : wK a b = 1 := by simp [wK, hab, ind]
  rw [this] at h
  omega

/-- A labelled 3-partition of the vertices 0..n-1 with all parts nonempty. -/
def Valid3 (n : Nat) (lab : Nat → Nat) : Prop :=
  (∀ y, y < n → lab y < 3) ∧ ∀ c, c < 3 → 1 ≤ cnt n (part lab c)

/-- m is the (doubled) minimum 3-cut value of w. -/
def IsMin3 (n : Nat) (w : Nat → Nat → Nat) (m : Nat) : Prop :=
  (∃ lab, Valid3 n lab ∧ cost n w lab = m) ∧ ∀ lab, Valid3 n lab → m ≤ cost n w lab

/-- A complete graph with positive integer edge weights. -/
def PosComplete (n : Nat) (w : Nat → Nat → Nat) : Prop :=
  (∀ x y, w x y = w y x) ∧ (∀ x, w x x = 0) ∧ ∀ x y, x < n → y < n → x ≠ y → 1 ≤ w x y

theorem cnt_pos (n : Nat) (P : Nat → Bool) (x : Nat) (hx : x < n) (hP : P x = true) : 1 ≤ cnt n P := by
  have := lsum_ge_term (fun y => ind (P y)) x n hx
  simp only [hP, ind_true] at this
  exact this

theorem labUV_valid (n a b : Nat) (hn : 3 ≤ n) (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    Valid3 n (labUV a b) := by
  refine ⟨fun y _ => by unfold labUV; split <;> (try split) <;> omega, ?_⟩
  intro c hc
  have t : ∃ t, t < 3 ∧ t ≠ a ∧ t ≠ b := by
    by_cases h0 : 0 ≠ a ∧ 0 ≠ b
    · exact ⟨0, by omega, h0.1, h0.2⟩
    · by_cases h1 : 1 ≠ a ∧ 1 ≠ b
      · exact ⟨1, by omega, h1.1, h1.2⟩
      · exact ⟨2, by omega, by omega, by omega⟩
  obtain ⟨t, ht, hta, htb⟩ := t
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with h | h | h <;> subst h
  · exact cnt_pos n _ a ha (by simp [part, labUV])
  · exact cnt_pos n _ b hb (by simp [part, labUV, Ne.symm hab])
  · exact cnt_pos n _ t (by omega) (by simp [part, labUV, hta, htb])

/-- Perturbing the pair weights by a vector z orthogonal to the coefficient vector F' leaves the
    weighted pair sum unchanged. -/
theorem pair_perturb (n K : Nat) (z : Nat → Int) (y2 : Nat → Nat)
    (hy2 : ∀ j, ((y2 j : Nat) : Int) = K + z j) (F' : Nat → Nat)
    (h0 : isum (n * n) (fun j => (if Zf n j then 0 else ((F' j : Nat) : Int)) * z j) = 0) :
    lsum (List.range (n * n)) (fun j => ind (!Zf n j) * F' j * y2 j)
      = lsum (List.range (n * n)) (fun j => ind (!Zf n j) * F' j * K) := by
  apply Int.ofNat_inj.mp
  rw [lsum_cast, lsum_cast]
  have hpt : ∀ j, (((ind (!Zf n j) * F' j * y2 j : Nat)) : Int)
      = (((ind (!Zf n j) * F' j * K : Nat)) : Int)
        + (if Zf n j then 0 else ((F' j : Nat) : Int)) * z j := by
    intro j
    cases hz : Zf n j
    · simp only [Bool.not_false, ind_true, Nat.one_mul, Int.ofNat_mul, hy2, ite_false, Bool.false_eq_true]
      rw [Int.mul_add]
    · simp [ind]
  rw [isum_congr _ _ (n * n) (fun j _ => hpt j), isum_add, h0, Int.add_zero]

theorem weighted_lb_core (n K : Nat) (hn : 3 ≤ n) (hK : bnd (n * n) 1 < K) (A : Alg Nat)
    (hA : ∀ w, PosComplete n w → IsMin3 n w (Alg.run (q n w) A)) :
    free (Zf n) (n * n) ≤ Alg.cost (q n (W n (fun _ => K))) A + n := by
  apply Classical.byContradiction
  intro hlt
  have hlt : Alg.cost (q n (W n (fun _ => K))) A + n < free (Zf n) (n * n) := by omega
  have pos1 : PosComplete n (W n (fun _ => K)) := by
    refine ⟨W_symm n _, W_loop n _, fun x y _ _ hxy => ?_⟩
    rw [W_const]; simp [wK, hxy, ind]; omega
  generalize hO1 : q n (W n (fun _ => K)) = O1 at hlt
  generalize hc : Alg.cost O1 A = c at hlt
  let S : Nat → (Nat → Bool) := fun i => (trace O1 A).getD i (fun _ => false)
  let E : Nat → Nat → Int := fun i j =>
    if Zf n j then 0 else
    if i < c then ((ind (S i (j / n) != S i (j % n)) : Nat) : Int)
    else ((ind (j / n == i - c || j % n == i - c) : Nat) : Int)
  have hE : ∀ i j, (E i j).natAbs ≤ 1 := by
    intro i j; simp only [E]
    split
    · simp
    · split <;> (unfold ind; split <;> simp)
  obtain ⟨x, ⟨j0, hj0, hz0, hx0⟩, hxZ, hxb, hx⟩ := homogB (n * n) (c + n) 1 E (Zf n) hlt hE
  have hsgn : ∃ z : Nat → Int, 0 < z j0 ∧ (∀ j, (z j).natAbs ≤ bnd (n * n) 1) ∧
      ∀ i, i < c + n → isum (n * n) (fun j => E i j * z j) = 0 := by
    by_cases hp : 0 < x j0
    · exact ⟨x, hp, hxb, hx⟩
    · refine ⟨fun j => - x j, by show 0 < - x j0; omega, fun j => by rw [Int.natAbs_neg]; exact hxb j, ?_⟩
      intro i hi
      rw [show (fun j => E i j * -x j) = (fun j => (-1) * (E i j * x j)) from by
        funext j; rw [Int.neg_mul, Int.one_mul, Int.mul_neg], isum_mul, hx i hi, Int.mul_zero]
  obtain ⟨z, hzpos, hzb, hz⟩ := hsgn
  let y2 : Nat → Nat := fun j => (K + z j).toNat
  have hy2 : ∀ j, ((y2 j : Nat) : Int) = K + z j := by
    intro j; simp only [y2]
    have := hzb j
    exact Int.toNat_of_nonneg (by omega)
  have pos2 : PosComplete n (W n y2) := by
    refine ⟨W_symm n _, W_loop n _, fun u v _ _ huv => ?_⟩
    have h1 : ∀ j, 1 ≤ y2 j := by
      intro j; have := hy2 j; have := hzb j; omega
    unfold W; split
    · exact h1 _
    · split
      · exact h1 _
      · omega
  -- every recorded query has the same answer
  have hq : ∀ i, i < c → q n (W n y2) (S i) = O1 (S i) := by
    intro i hi
    rw [← hO1]
    unfold q
    have hF : ∀ u v, ind (S i u != S i v) = ind (S i v != S i u) := by
      intro u v; cases S i u <;> cases S i v <;> rfl
    rw [pair_sum n y2 _ hF, pair_sum n _ _ hF]
    congr 1
    apply pair_perturb n K z y2 hy2
    refine (isum_congr _ _ _ (fun j _ => ?_)).trans (hz i (by omega))
    simp only [E, hi, ite_true]
  have hrun := trace_agree O1 (q n (W n y2)) A (by
    intro i hi
    rw [trace_length, hc] at hi
    exact hq i hi)
  -- all weighted degrees are unchanged
  have hdeg : ∀ v, v < n → deg n (W n y2) v = deg n (W n (fun _ => K)) v := by
    intro v hv
    rw [deg_pairs n y2 v hv, deg_pairs n _ v hv]
    apply pair_perturb n K z y2 hy2
    refine (isum_congr _ _ _ (fun j _ => ?_)).trans (hz (c + v) (by omega))
    simp only [E, show ¬ (c + v < c) by omega, show c + v - c = v by omega, ite_false]
  -- the pair carrying a positive perturbation
  have hn0 : 0 < n := by omega
  have hab : j0 / n < j0 % n := by simpa [Zf] using hz0
  have hb : j0 % n < n := Nat.mod_lt _ hn0
  have ha : j0 / n < n := by omega
  generalize hav : j0 / n = a at hab ha
  generalize hbv : j0 % n = b at hab hb
  have hj : n * a + b = j0 := by rw [← hav, ← hbv]; exact Nat.div_add_mod j0 n
  have hw2 : W n y2 a b = y2 j0 := by simp [W, hab, hj]
  have hw1 : W n (fun _ => K) a b = K := by simp [W, hab]
  have t2 := two_singleton_value n (W n y2) (W_symm n _) (W_loop n _) a b ha hb (by omega)
  have t1 := two_singleton_value n (W n (fun _ => K)) (W_symm n _) (W_loop n _) a b ha hb (by omega)
  rw [hdeg a ha, hdeg b hb, hw2] at t2
  rw [hw1] at t1
  have hy0 := hy2 j0
  have c1 : cost n (W n (fun _ => K)) (labUV a b) = 2 * (2 * n - 3) * K := by
    rw [cost_const, kn_labUV n a b ha hb (by omega)]
  -- correctness on both inputs
  obtain ⟨⟨lab1, hv1, hm1⟩, _⟩ := hA _ pos1
  obtain ⟨_, hm2⟩ := hA _ pos2
  have hle2 := hm2 (labUV a b) (labUV_valid n a b hn ha hb (by omega))
  rw [hrun.1] at hle2
  rw [hO1] at hm1
  have hlow : 2 * (2 * n - 3) * K ≤ cost n (W n (fun _ => K)) lab1 := by
    rw [cost_const]
    exact Nat.mul_le_mul_right K (kn_lambda3 n lab1 hv1.1 hv1.2)
  generalize cost n (W n (fun _ => K)) (labUV a b) = C1 at *
  generalize cost n (W n y2) (labUV a b) = C2 at *
  generalize cost n (W n (fun _ => K)) lab1 = L1 at *
  generalize 2 * (2 * n - 3) * K = T at *
  omega

/-- Proposition 29 (weighted deterministic lower bound). Let n ≥ 3. A deterministic adaptive
    cut-query algorithm that returns the minimum 3-cut value of every complete graph on n vertices
    with positive integer edge weights asks at least C(n,2) - n queries on some such graph
    (in fact on the uniformly weighted K_n with weight bnd (n²) 1 + 1). -/
theorem weighted_lb (n : Nat) (hn : 3 ≤ n) (A : Alg Nat)
    (hA : ∀ w, PosComplete n w → IsMin3 n w (Alg.run (q n w) A)) :
    ∃ w, PosComplete n w ∧ n * (n - 1) ≤ 2 * (Alg.cost (q n w) A + n) := by
  refine ⟨W n (fun _ => bnd (n * n) 1 + 1), ⟨W_symm n _, W_loop n _, fun x y _ _ hxy => ?_⟩, ?_⟩
  · rw [W_const]; simp [wK, hxy, ind]
  · have := weighted_lb_core n (bnd (n * n) 1 + 1) hn (by omega) A hA
    have := free_pairs n
    omega


end MinKCut
