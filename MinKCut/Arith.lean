import MinKCut.Basic
/-! # Parts B–E: potential argument, exchange inequalities, Li's gadget arithmetic, complete graphs -/

namespace MinKCut

/-! ## Part B: the potential argument (Lemma 13)

  With q = αD and α = 1/c, an atom of size x contributes φ(x) = max(⌊x/q⌋ - 1, 0) =
  ⌊cx/D⌋ - 1 (truncated subtraction). A child "meets a relevant part in at least q vertices"
  exactly when c·x ≥ D. -/

def phi (c Dg x : Nat) : Nat := c * x / Dg - 1

/-- Number of children of size at least q. -/
def big (c Dg : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => (if Dg ≤ c * x then 1 else 0) + big c Dg l

def total : List Nat → Nat
  | [] => 0
  | x :: l => x + total l

def Phi (c Dg : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => phi c Dg x + Phi c Dg l

def fl (c Dg : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => c * x / Dg + fl c Dg l

theorem div_add_le (a b Dg : Nat) : a / Dg + b / Dg ≤ (a + b) / Dg := by
  rcases Nat.eq_zero_or_pos Dg with h | h
  · subst h; simp
  · apply (Nat.le_div_iff_mul_le h).mpr
    rw [Nat.add_mul]
    have h1 := Nat.div_mul_le_self a Dg
    have h2 := Nat.div_mul_le_self b Dg
    omega

/-- Floor subadditivity. -/
theorem fl_le (c Dg : Nat) (l : List Nat) : fl c Dg l ≤ c * total l / Dg := by
  induction l with
  | nil => simp [fl, total]
  | cons x l ih =>
    simp only [fl, total, Nat.mul_add]
    have := div_add_le (c * x) (c * total l) Dg
    omega

/-- φ(x) + [x ≥ q] = ⌊cx/D⌋, summed over the children. -/
theorem Phi_big (c Dg : Nat) (hD : 0 < Dg) (l : List Nat) : Phi c Dg l + big c Dg l = fl c Dg l := by
  induction l with
  | nil => simp [Phi, big, fl]
  | cons x l ih =>
    simp only [Phi, big, fl, phi]
    by_cases h : Dg ≤ c * x
    · have : 1 ≤ c * x / Dg := (Nat.le_div_iff_mul_le hD).mpr (by omega)
      simp [h]; omega
    · have : c * x / Dg = 0 := Nat.div_eq_of_lt (by omega)
      simp [h, this]; omega

theorem Phi_zero (c Dg : Nat) (_hD : 0 < Dg) (l : List Nat) :
    Phi c Dg l = 0 ∨ 1 ≤ big c Dg l := by
  induction l with
  | nil => simp [Phi]
  | cons x l ih =>
    simp only [Phi, big, phi]
    by_cases h : Dg ≤ c * x
    · right; simp [h]
    · have : c * x / Dg = 0 := Nat.div_eq_of_lt (by omega)
      simp [h, this]
      omega

/-- Refining an atom never increases the potential. -/
theorem refine_le (c Dg : Nat) (hD : 0 < Dg) (l : List Nat) :
    Phi c Dg l ≤ phi c Dg (total l) := by
  have h1 := Phi_big c Dg hD l
  have h2 := fl_le c Dg l
  have h3 := Phi_zero c Dg hD l
  unfold phi
  omega

/-- Splitting an atom into pieces of which at least two have size ≥ q decreases it by one. -/
theorem refine_lt (c Dg : Nat) (hD : 0 < Dg) (l : List Nat) (h2 : 2 ≤ big c Dg l) :
    Phi c Dg l + 1 ≤ phi c Dg (total l) := by
  have h1 := Phi_big c Dg hD l
  have h3 := fl_le c Dg l
  unfold phi
  omega

/-- One round of Algorithm 1: every current atom (a list of atom sizes) is replaced by its
    pieces. `step old new` says that `new` lists, for each atom of `old`, the sizes of its
    pieces. -/
def Phis (c Dg : Nat) : List (List Nat) → Nat
  | [] => 0
  | l :: ls => Phi c Dg l + Phis c Dg ls

def PhiA (c Dg : Nat) : List Nat → Nat := Phi c Dg

theorem round_le (c Dg : Nat) (hD : 0 < Dg) (pieces : List (List Nat)) :
    Phis c Dg pieces ≤ Phi c Dg (pieces.map total) := by
  induction pieces with
  | nil => simp [Phis, Phi]
  | cons l ls ih =>
    simp only [Phis, List.map, Phi]
    have := refine_le c Dg hD l
    omega

/-- A selection round: some atom (the witness atom) has two pieces of size ≥ q. -/
theorem round_lt (c Dg : Nat) (hD : 0 < Dg) (pieces : List (List Nat))
    (hw : ∃ l, l ∈ pieces ∧ 2 ≤ big c Dg l) :
    Phis c Dg pieces + 1 ≤ Phi c Dg (pieces.map total) := by
  induction pieces with
  | nil => simp at hw
  | cons l ls ih =>
    simp only [Phis, List.map, Phi]
    rcases hw with ⟨l', hl', hb⟩
    rcases List.mem_cons.mp hl' with h | h
    · subst h
      have := refine_lt c Dg hD l' hb
      have := round_le c Dg hD ls
      omega
    · have := ih ⟨l', h, hb⟩
      have := refine_le c Dg hD l
      omega

theorem Phi_append (c Dg : Nat) (l₁ l₂ : List Nat) :
    Phi c Dg (l₁ ++ l₂) = Phi c Dg l₁ + Phi c Dg l₂ := by
  induction l₁ with
  | nil => simp [Phi]
  | cons x l ih =>
    rw [List.cons_append]
    simp only [Phi]
    rw [ih]
    omega

/-- The new atom family after a round is the concatenation of the pieces. -/
theorem Phi_join (c Dg : Nat) (pieces : List (List Nat)) :
    Phi c Dg (pieces.flatten) = Phis c Dg pieces := by
  induction pieces with
  | nil => simp [Phi, Phis]
  | cons l ls ih =>
    rw [List.flatten_cons, Phi_append, ih]
    simp only [Phis]

/-- Lemma 13 (number of selected partitions). Let atoms₀ = [n] be the initial family and let
    every later family be obtained from the previous one by a selection round, in which every
    atom is split into pieces and some atom has two pieces of size at least q = D/c. Then the
    number of rounds m satisfies m ≤ ⌊cn/D⌋ - 1 < cn/D = n/(αD). -/
theorem selection_bound (c Dg n : Nat) (hD : 0 < Dg) :
    ∀ (m : Nat) (fam : Nat → List Nat),
      fam 0 = [n] →
      (∀ j, j < m → ∃ pieces : List (List Nat),
          pieces.map total = fam j ∧ fam (j + 1) = pieces.flatten ∧
          ∃ l, l ∈ pieces ∧ 2 ≤ big c Dg l) →
      m + Phi c Dg (fam m) ≤ c * n / Dg - 1 := by
  intro m fam h0 hstep
  induction m with
  | zero => simp [h0, Phi, phi]
  | succ m ih =>
    have ih' := ih (fun j hj => hstep j (by omega))
    rcases hstep m (by omega) with ⟨pieces, hmap, hnext, hw⟩
    have := round_lt c Dg hD pieces hw
    rw [hnext, Phi_join]
    rw [hmap] at this
    omega

/-- With α = 1/32: the number of selections m satisfies m < n/(αD) = 32n/D, i.e. m·D < 32n. -/
theorem selection_count (Dg n m : Nat) (hD : 0 < Dg) (hn : 0 < n) (fam : Nat → List Nat)
    (h0 : fam 0 = [n])
    (hstep : ∀ j, j < m → ∃ pieces : List (List Nat),
          pieces.map total = fam j ∧ fam (j + 1) = pieces.flatten ∧
          ∃ l, l ∈ pieces ∧ 2 ≤ big 32 Dg l) :
    m * Dg < 32 * n := by
  have h := selection_bound 32 Dg n hD m fam h0 hstep
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; omega
  · have h2 : m + 1 ≤ 32 * n / Dg := by omega
    have h3 := Nat.mul_le_mul_right Dg h2
    have h4 := Nat.div_mul_le_self (32 * n) Dg
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega

/-! ## Part C: exchange inequalities and the sparsifier constant -/

/-- Lemma 11 with γ = 1/256: τ = 257/255 and (τ² - 1)·λ₃ ≤ (τ² - 1)·2D < D/8.
    In integers: (257² - 255²)·2D·8 < 255²·D. -/
theorem candidate_constant (Dg : Nat) (hD : 0 < Dg) :
    (257 * 257 - 255 * 255) * (2 * Dg) * 8 < 255 * 255 * Dg := by
  omega

/-- Lemma 14 (no-singleton cover), the decrease when u moves: a < αd + αD (α = 1/32) and
    d ≥ D give (d - 3a)/2 > 13D/32 > D/8. -/
theorem exchange_no_singleton (d Dg a : Int) (hD : 0 < Dg) (hd : Dg ≤ d) (ha : 32 * a < d + Dg) :
    16 * (d - 3 * a) > 13 * Dg ∧ 13 * Dg * 8 > Dg * 32 := by
  omega

/-- Lemma 15 (one-singleton cover): with e ∈ {0,1} for the possible edge us, D ≥ 2,
    d - 2a - e > 7D/8 - 1 > D/8. -/
theorem exchange_one_singleton (d Dg a e : Int) (hD : 2 ≤ Dg) (hd : Dg ≤ d)
    (ha : 32 * a < d + Dg) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    8 * (d - 2 * a - e) > Dg := by
  omega

/-- Theorem 18 (at most two singleton parts): with α = η = 1/(16k), a < 2αd (that is,
    8ka < d), t ≤ k nonsingleton parts, s ≤ 2 singleton parts, D > 2k and d ≥ D, the cost
    decrease (d - ta - s)/(t - 1) exceeds ηD = D/(16k). Stated without division:
    (t - 1)·D + 16k·(ta + s) < 16k·d. -/
theorem exchange_general_k (k t s d Dg a : Nat) (ht2 : 2 ≤ t) (htk : t ≤ k) (hs : s ≤ 2)
    (hD : 2 * k < Dg) (hd : Dg ≤ d) (ha : 8 * k * a < d) :
    (t - 1) * Dg + 16 * k * (t * a + s) < 16 * k * d := by
  -- 8(ta) < d
  have h1 : t * a ≤ k * a := Nat.mul_le_mul_right a htk
  have h2 : 8 * k * a = 8 * (k * a) := by rw [Nat.mul_assoc]
  have h3 : 8 * (t * a) < d := by omega
  -- 16k(ta) ≤ 2kd
  have h4 : k * (8 * (t * a)) ≤ k * d := Nat.mul_le_mul_left k (Nat.le_of_lt h3)
  have h5a : 16 * k * (t * a) = 16 * (k * (t * a)) := by rw [Nat.mul_assoc]
  have h5b : k * (8 * (t * a)) = 8 * (k * (t * a)) := Nat.mul_left_comm _ _ _
  -- (t-1)D ≤ (k-1)d
  have h6 : (t - 1) * Dg ≤ (k - 1) * d :=
    Nat.mul_le_mul (by omega) hd
  have h7 : (k - 1) * d + d = k * d := by
    have hk : 1 ≤ k := by omega
    have := Nat.sub_add_cancel hk
    calc (k - 1) * d + d = (k - 1 + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
      _ = k * d := by rw [this]
  -- 16ks ≤ 32k
  have h8 : 16 * k * s ≤ 16 * k * 2 := Nat.mul_le_mul_left _ hs
  -- 13kd ≥ 39k > 32k since d ≥ 3
  have h9 : k * 3 ≤ k * d := Nat.mul_le_mul_left k (by omega)
  have h10 : 16 * k * (t * a + s) = 16 * k * (t * a) + 16 * k * s := Nat.mul_add _ _ _
  have h11 : 16 * k * d = 16 * (k * d) := by rw [Nat.mul_assoc]
  have h12 : 16 * k * 2 = 32 * k := by omega
  have hk1 : 1 ≤ k := by omega
  omega

/-! ## Part D: Li's gadget (Lemma 25)

  c2 x = x(x-1) = 2·C(x,2). -/

def c2 (x : Nat) : Nat := x * (x - 1)

/-- C(a,2) + C(b,2) ≤ C(a+b-1,2) for a, b ≥ 1. -/
theorem c2_merge (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : c2 a + c2 b ≤ c2 (a + b - 1) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  unfold c2
  have e1 : a' + 1 + (b' + 1) - 1 = a' + b' + 1 := by omega
  rw [e1]
  simp only [Nat.add_sub_cancel]
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  have : 0 ≤ a' * b' := Nat.zero_le _
  have : a' * b' = b' * a' := Nat.mul_comm _ _
  omega

/-- Convexity: m ≥ 1 positive part sizes with total r satisfy Σ C(rᵢ,2) ≤ C(r-m+1,2). -/
theorem convexity : ∀ (l : List Nat), l ≠ [] → (∀ x, x ∈ l → 1 ≤ x) →
    lsum l c2 ≤ c2 (total l + 1 - l.length) := by
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons x l ih =>
    intro _ hpos
    have hx := hpos x (by simp)
    cases l with
    | nil => simp [lsum, total]
    | cons y l' =>
      have ih' := ih (by simp) (fun z hz => hpos z (by simp [hz]))
      simp only [lsum] at ih' ⊢
      simp only [total, List.length_cons] at ih' ⊢
      -- total (y :: l') ≥ length (y :: l')
      have hge : ∀ (m : List Nat), (∀ z, z ∈ m → 1 ≤ z) → m.length ≤ total m := by
        intro m hm
        induction m with
        | nil => simp [total]
        | cons z m ihm =>
          simp only [total, List.length_cons]
          have := hm z (by simp)
          have := ihm (fun w hw => hm w (by simp [hw]))
          omega
      have hl := hge l' (fun z hz => hpos z (by simp [hz]))
      have hy := hpos y (by simp)
      have hm := c2_merge x (y + total l' + 1 - (l'.length + 1)) hx (by omega)
      have e : x + (y + total l' + 1 - (l'.length + 1)) - 1
          = x + (y + total l') + 1 - (l'.length + 1 + 1) := by omega
      rw [e] at hm
      omega

/-- The exact identity behind (li-lower), with T = (k-1)p - C(k-1,2):
    2pr - 2C(r,2) - 2C(r-k+2,2) = 2T + 2(r-k+1)(p-r), over the integers. -/
theorem li_identity (p r k : Int) :
    (p * r + p * r) - r * (r - 1) - (r - k + 1 + 1) * (r - k + 1)
      = ((k - 1) * p + (k - 1) * p) - (k - 1) * (k - 1 - 1)
        + ((r - k + 1) * (p - r) + (r - k + 1) * (p - r)) := by
  simp only [Int.mul_add, Int.add_mul, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul]
  simp only [Int.mul_comm, Int.mul_left_comm]
  omega

/-- (li-lower): if the doubled number Y = 2(2Σ e(Sᵢ) + Σ e(Sᵢ,Sⱼ)) of edges saved satisfies
    Y ≤ 2C(r,2) + 2C(r-k+2,2), then the doubled cost 2pr - Y is at least
    2T + 2(r-k+1)(p-r) ≥ 2T. -/
theorem li_lower (p r k Y : Int) (_hk : 2 ≤ k) (hr1 : k - 1 ≤ r) (hr2 : r ≤ p)
    (hY : Y ≤ r * (r - 1) + (r - k + 1 + 1) * (r - k + 1)) :
    (p * r + p * r) - Y ≥ ((k - 1) * p + (k - 1) * p) - (k - 1) * (k - 1 - 1)
        + ((r - k + 1) * (p - r) + (r - k + 1) * (p - r))
    ∧ (r - k + 1) * (p - r) ≥ 0 := by
  have hid := li_identity p r k
  have hnn : (r - k + 1) * (p - r) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
  constructor
  · omega
  · exact hnn

/-- Equality case: cost = T forces r = k-1 or r = p. -/
theorem li_equality (p r k : Int) (_hr1 : k - 1 ≤ r) (_hr2 : r ≤ p)
    (h0 : (r - k + 1) * (p - r) = 0) : r = k - 1 ∨ r = p := by
  rcases Int.mul_eq_zero.mp h0 with h | h
  · left; omega
  · right; omega

/-! ## Part E: complete graphs and parameter arithmetic -/

/-- A 3-partition of K_n with part sizes a,b,c costs ab+ac+bc ≥ 2n-3 (pattern (1,1,n-2));
    in particular λ₃(K_m) = 2m - 3. -/
theorem kn_three_parts (a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    2 * (a + b + c) ≤ a * b + a * c + b * c + 3 := by
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 1 := ⟨a - 1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = y + 1 := ⟨b - 1, by omega⟩
  obtain ⟨z, rfl⟩ : ∃ z, c = z + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- Every other size pattern (at least two parts of size ≥ 2) costs at least 3n - 7,
    leaving a gap of n - 4 (Proposition 29). -/
theorem kn_next_pattern (a b c : Nat) (ha : 1 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    3 * (a + b + c) ≤ a * b + a * c + b * c + 7 := by
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 1 := ⟨a - 1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = y + 2 := ⟨b - 2, by omega⟩
  obtain ⟨z, rfl⟩ : ∃ z, c = z + 2 := ⟨c - 2, by omega⟩
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- Splitting a clique on m vertices into nonempty sides of sizes a and m - a cuts
    a(m-a) ≥ m - 1 edges. -/
theorem kn_two_parts (a b : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) : a + b - 1 ≤ a * b := by
  obtain ⟨x, rfl⟩ : ∃ x, a = x + 1 := ⟨a - 1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = y + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- Switching lower bound: a non-(A,B) shore cuts ≥ 2t-1 edges of H₀, each of the |x| ≤ t/4
    switches removes at most two crossing edges, so the cut exceeds 2|x| by at least t - 1. -/
theorem switching_gap (t w cutH0 : Nat) (hw : 4 * w ≤ t) (h : 2 * t - 1 ≤ cutH0) (ht : 1 ≤ t) :
    2 * w + (t - 1) ≤ cutH0 - 2 * w := by
  omega

/-- Parameters of Lemma 27: p = ⌊n/(k²+1)⌋ and M = n - p satisfy M ≥ k²p. -/
theorem li_params (n k : Nat) : k * k * (n / (k * k + 1)) ≤ n - n / (k * k + 1) := by
  have h := Nat.div_mul_le_self n (k * k + 1)
  have e : n / (k * k + 1) * (k * k + 1) = k * k * (n / (k * k + 1)) + n / (k * k + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm]
  omega

/-- Parameters of Corollary 28: with n - q² ≥ (3k+5)p and k = q + 4,
    M = n - (1+3q)p - q² satisfies M ≥ 16p, and the total size is p + M + q(3p+q) = n. -/
theorem three_singleton_params (n q p : Nat) (h : (3 * (q + 4) + 5) * p + q * q ≤ n) :
    16 * p ≤ n - (1 + 3 * q) * p - q * q ∧
    p + (n - (1 + 3 * q) * p - q * q) + q * (3 * p + q) = n := by
  have e1 : (3 * (q + 4) + 5) * p = 3 * (q * p) + 17 * p := by
    simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]; omega
  have e2 : (1 + 3 * q) * p = p + 3 * (q * p) := by
    simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have e3 : q * (3 * p + q) = 3 * (q * p) + q * q := by
    rw [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm q p]
  omega




end MinKCut
