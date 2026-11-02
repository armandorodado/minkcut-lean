import MinKCut.Arith
/-! # Part F: graph-level covering lemmas, Lemma 12, λ₃(K_m), strict monotonicity, Li's gadget, Theorem 20 bridge -/

namespace MinKCut

/-! ## Part F: graph-level covering lemmas (Lemmas 14 and 15)

  Here the graph is simple: `wt` is symmetric, has zero diagonal and values at most 1. -/

section Cover

variable (n : Nat) (wt : Nat → Nat → Nat)

/-- Picking out one term of a sum over 0..n-1. -/
theorem pick (h : Nat → Nat) (u : Nat) : ∀ n, u < n →
    lsum (List.range n) (fun x => ind (x == u) * h x) = h u := by
  intro n
  induction n with
  | zero => intro hu; omega
  | succ n ih =>
    intro hu
    rw [List.range_succ, lsum_append]
    simp only [lsum]
    by_cases hun : u = n
    · subst hun
      have h0 : lsum (List.range u) (fun x => ind (x == u) * h x) = 0 := by
        rw [lsum_congr _ _ (fun _ => 0) (fun x hx => by
          have := List.mem_range.mp hx
          have hne : (x == u) = false := by simp; omega
          simp [hne, ind])]
        exact lsum_zero _
      rw [h0]; simp [ind]
    · have hne : (n == u) = false := by simp; omega
      rw [ih (by omega)]
      simp [hne, ind]

/-- Exchange of the order of summation. -/
theorem lsum_swap (l m : List Nat) (f : Nat → Nat → Nat) :
    lsum l (fun x => lsum m (fun y => f x y)) = lsum m (fun y => lsum l (fun x => f x y)) := by
  induction l with
  | nil => simp only [lsum]; exact (lsum_zero m).symm
  | cons a l ih =>
    simp only [lsum]
    rw [ih, ← lsum_add]

theorem lsum_mul_left (l : List Nat) (f : Nat → Nat) (c : Nat) :
    lsum l (fun a => c * f a) = c * lsum l f := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih => simp only [lsum, ih, Nat.mul_add]

theorem ind_true : ind true = 1 := rfl
theorem ind_false : ind false = 0 := rfl

theorem ind_pair (a b : Nat) : ind (a != b) + ind (b == a) = 1 := by
  by_cases h : a = b
  · subst h; simp [ind]
  · have h' : b ≠ a := fun e => h e.symm
    simp [ind, h, h']

theorem ind_pair2 (a b : Nat) : ind (a != b) + ind (a == b) = 1 := by
  by_cases h : a = b
  · subst h; simp [ind]
  · simp [ind, h]

theorem D_zero : D n (fun _ _ => 0) = 0 := by
  unfold D
  rw [lsum_congr _ _ (fun _ => 0) (fun _ _ => lsum_zero _), lsum_zero]

/-- Weighted number of neighbours of u in P. -/
def row (u : Nat) (P : Nat → Bool) : Nat := lsum (List.range n) (fun y => ind (P y) * wt u y)

def deg (u : Nat) : Nat := row n wt u (fun _ => true)

/-- Number of vertices in P. -/
def cnt (P : Nat → Bool) : Nat := lsum (List.range n) (fun y => ind (P y))

/-- Move vertex u to part j. -/
def upd (lab : Nat → Nat) (u j : Nat) : Nat → Nat := fun x => if x == u then j else lab x

theorem D_left (u : Nat) (hu : u < n) (g : Nat → Nat → Nat) :
    D n (fun x y => ind (x == u) * g x y) = lsum (List.range n) (fun y => g u y) := by
  unfold D
  rw [lsum_congr _ _ (fun x => ind (x == u) * lsum (List.range n) (fun y => g x y))
    (fun x _ => lsum_mul_left _ _ _)]
  exact pick (fun x => lsum (List.range n) (fun y => g x y)) u n hu

theorem D_right (u : Nat) (hu : u < n) (g : Nat → Nat → Nat) :
    D n (fun x y => ind (y == u) * g x y) = lsum (List.range n) (fun x => g x u) := by
  unfold D
  rw [lsum_swap]
  rw [lsum_congr _ _ (fun y => ind (y == u) * lsum (List.range n) (fun x => g x y))
    (fun y _ => lsum_mul_left _ _ _)]
  exact pick (fun y => lsum (List.range n) (fun x => g x y)) u n hu

/-- Moving u from part i = lab u to part j changes the (doubled) cost by
    2·(neighbours in P_i) - 2·(neighbours in P_j). -/
theorem move (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (lab : Nat → Nat) (u j : Nat) (hu : u < n) :
    cost n wt (upd lab u j) + 2 * row n wt u (part lab j)
      = cost n wt lab + 2 * row n wt u (part lab (lab u)) := by
  have hL : ∀ c, row n wt u (part lab c)
      = D n (fun x y => ind (x == u) * (ind (lab y == c) * wt x y)) := by
    intro c
    rw [D_left n u hu]
    rfl
  have hR : ∀ c, row n wt u (part lab c)
      = D n (fun x y => ind (y == u) * (ind (lab x == c) * wt x y)) := by
    intro c
    rw [D_right n u hu]
    unfold row part
    apply lsum_congr
    intro x _
    rw [hsym x u]
  have key : D n (fun x y => ind (upd lab u j x != upd lab u j y) * wt x y)
      + D n (fun x y => ind (x == u) * (ind (lab y == j) * wt x y))
      + D n (fun x y => ind (y == u) * (ind (lab x == j) * wt x y))
      = D n (fun x y => ind (lab x != lab y) * wt x y)
      + D n (fun x y => ind (x == u) * (ind (lab y == lab u) * wt x y))
      + D n (fun x y => ind (y == u) * (ind (lab x == lab u) * wt x y)) := by
    rw [← D_add, ← D_add, ← D_add, ← D_add]
    apply D_congr
    intro x y _ _
    unfold upd
    by_cases hx : x = u <;> by_cases hy : y = u
    · subst hx; subst hy; simp [hloop]
    · subst hx
      have : (y == x) = false := by simp; omega
      simp only [this, beq_self_eq_true, ite_true, ite_false]
      generalize lab x = a
      generalize lab y = b
      generalize wt x y = w
      clear hL hR
      have e1 := ind_pair j b
      have e2 := ind_pair a b
      have f1 : ind (j != b) * w + ind (b == j) * w = w := by rw [← Nat.add_mul, e1, Nat.one_mul]
      have f2 : ind (a != b) * w + ind (b == a) * w = w := by rw [← Nat.add_mul, e2, Nat.one_mul]
      have e3 := ind_pair2 a j
      have e4 := ind_pair2 a b
      have f3 : ind (a != j) * w + ind (a == j) * w = w := by rw [← Nat.add_mul, e3, Nat.one_mul]
      have f4 : ind (a != b) * w + ind (a == b) * w = w := by rw [← Nat.add_mul, e4, Nat.one_mul]
      simp only [Bool.false_eq_true, ite_false, ite_true, ind_true, ind_false, Nat.one_mul,
        Nat.zero_mul, Nat.add_zero]
      omega
    · subst hy
      have : (x == y) = false := by simp; omega
      simp only [this, beq_self_eq_true, ite_true, ite_false]
      generalize lab x = a
      generalize lab y = b
      generalize wt x y = w
      clear hL hR
      have e1 := ind_pair j b
      have e2 := ind_pair a b
      have f1 : ind (j != b) * w + ind (b == j) * w = w := by rw [← Nat.add_mul, e1, Nat.one_mul]
      have f2 : ind (a != b) * w + ind (b == a) * w = w := by rw [← Nat.add_mul, e2, Nat.one_mul]
      have e3 := ind_pair2 a j
      have e4 := ind_pair2 a b
      have f3 : ind (a != j) * w + ind (a == j) * w = w := by rw [← Nat.add_mul, e3, Nat.one_mul]
      have f4 : ind (a != b) * w + ind (a == b) * w = w := by rw [← Nat.add_mul, e4, Nat.one_mul]
      simp only [Bool.false_eq_true, ite_false, ite_true, ind_true, ind_false, Nat.one_mul,
        Nat.zero_mul, Nat.add_zero]
      omega
    · have h1 : (x == u) = false := by simp; omega
      have h2 : (y == u) = false := by simp; omega
      simp [h1, h2, ind]
  rw [← hL j, ← hR j, ← hL (lab u), ← hR (lab u)] at key
  unfold cost
  omega

theorem lsum_le_of_pt (l : List Nat) (f g : Nat → Nat) (h : ∀ a, a ∈ l → f a ≤ g a) :
    lsum l f ≤ lsum l g := lsum_mono l f g h

/-- The neighbours of u split over the three parts of a 3-partition. -/
theorem row_three (lab : Nat → Nat) (u : Nat) (h3 : ∀ y, y < n → lab y < 3) :
    row n wt u (part lab 0) + row n wt u (part lab 1) + row n wt u (part lab 2) = deg n wt u := by
  unfold deg row part
  rw [← lsum_add, ← lsum_add]
  apply lsum_congr
  intro y hy
  have := h3 y (List.mem_range.mp hy)
  rcases (by omega : lab y = 0 ∨ lab y = 1 ∨ lab y = 2) with h | h | h <;> simp [h, ind]

/-- Inside/outside-atom count: the neighbours of u in its own part P_i are u's other vertices of
    R ∩ P_i plus edges leaving the atom R of u (the F-edges at u). -/
theorem own_bound (hloop : ∀ x, wt x x = 0) (hle1 : ∀ x y, wt x y ≤ 1)
    (lab : Nat → Nat) (u : Nat) (R : Nat → Bool) (hu : u < n) (hR : R u = true) :
    row n wt u (part lab (lab u)) + 1
      ≤ cnt n (fun y => R y && (lab y == lab u)) + row n wt u (fun y => !R y) := by
  have h1 : lsum (List.range n) (fun y => ind (y == u) * 1) = 1 := pick (fun _ => 1) u n hu
  unfold row cnt part
  rw [← h1, ← lsum_add, ← lsum_add]
  apply lsum_mono
  intro y _
  by_cases hy : y = u
  · subst hy; simp [hloop, hR, ind]
  · have hne : (y == u) = false := by simp [hy]
    have hw := hle1 u y
    by_cases hRy : R y = true <;> by_cases hl : lab y = lab u <;> simp [ind, hne, hRy, hl] <;>
      omega

/-- Lemma 14 (no-singleton cover), graph-level core. Let P be a 3-partition in which every part
    has a vertex other than u, of cost below λ₃ + D/8 (doubled: 4·cost < 4·λ + D). Let R be
    the atom of u, F the edges leaving atoms. If u is not exceptional (deg_F(u) < d(u)/32), has
    degree at least D, and its own part meets R in fewer than D/32 vertices, we get a
    contradiction. So every vertex outside X ∪ W of a candidate edge meets its own part of the
    final atom in at least αD vertices, which is what the proof of Lemma 14 uses. -/
theorem cover_no_singleton (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1)
    (lab : Nat → Nat) (u : Nat) (R : Nat → Bool) (Dg lam : Nat)
    (hu : u < n) (hlab : ∀ y, y < n → lab y < 3)
    (hother : ∀ c, c < 3 → ∃ v, v < n ∧ v ≠ u ∧ lab v = c)
    (hR : R u = true)
    (hpiece : 32 * cnt n (fun y => R y && (lab y == lab u)) < Dg)
    (hX : 32 * row n wt u (fun y => !R y) < deg n wt u)
    (hdeg : Dg ≤ deg n wt u)
    (hopt : ∀ lab' : Nat → Nat, (∀ y, y < n → lab' y < 3) →
      (∀ c, c < 3 → ∃ v, v < n ∧ lab' v = c) → lam ≤ cost n wt lab')
    (hslack : 4 * cost n wt lab < 4 * lam + Dg) : False := by
  have hown := own_bound n wt hloop hle1 lab u R hu hR
  have hsum := row_three n wt lab u hlab
  have hiu := hlab u hu
  -- moving u to part t (t ≠ lab u, t < 3) gives an admissible partition
  have hmove : ∀ t, t < 3 → t ≠ lab u →
      lam + 2 * row n wt u (part lab t) ≤ cost n wt lab + 2 * row n wt u (part lab (lab u)) := by
    intro t ht _
    have hm := move n wt hsym hloop lab u t hu
    have hadm := hopt (upd lab u t)
      (by intro y hy; unfold upd; by_cases h : y = u <;> simp [h, ht, hlab y hy])
      (by
        intro c hc
        obtain ⟨v, hv, hvu, hvc⟩ := hother c hc
        refine ⟨v, hv, ?_⟩
        have : (v == u) = false := by simp [hvu]
        simp [upd, this, hvc])
    omega
  rcases (by omega : lab u = 0 ∨ lab u = 1 ∨ lab u = 2) with h | h | h
  · have h1 := hmove 1 (by omega) (by omega)
    have h2 := hmove 2 (by omega) (by omega)
    rw [h] at hown h1 h2 hpiece
    omega
  · have h1 := hmove 0 (by omega) (by omega)
    have h2 := hmove 2 (by omega) (by omega)
    rw [h] at hown h1 h2 hpiece
    omega
  · have h1 := hmove 0 (by omega) (by omega)
    have h2 := hmove 1 (by omega) (by omega)
    rw [h] at hown h1 h2 hpiece
    omega

/-- Lemma 15 (one-singleton residual cover), graph-level core. Part 0 is the singleton {s},
    u lies in a nonsingleton part i ∈ {1,2} that has another vertex, D ≥ 2, and the remaining
    hypotheses are as in `cover_no_singleton`. Moving u to the other nonsingleton part gives a
    contradiction; the possible edge us is the only loss, which is where simplicity is used. -/
theorem cover_one_singleton (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1)
    (lab : Nat → Nat) (u s : Nat) (R : Nat → Bool) (Dg lam : Nat)
    (hu : u < n) (hs : s < n) (hlab : ∀ y, y < n → lab y < 3)
    (hsing : ∀ y, y < n → (lab y = 0 ↔ y = s)) (hi : lab u ≠ 0)
    (hother : ∃ v, v < n ∧ v ≠ u ∧ lab v = lab u)
    (hthird : ∃ v, v < n ∧ lab v = 3 - lab u)
    (hR : R u = true)
    (hpiece : 32 * cnt n (fun y => R y && (lab y == lab u)) < Dg)
    (hX : 32 * row n wt u (fun y => !R y) < deg n wt u)
    (hdeg : Dg ≤ deg n wt u) (hD : 2 ≤ Dg)
    (hopt : ∀ lab' : Nat → Nat, (∀ y, y < n → lab' y < 3) →
      (∀ c, c < 3 → ∃ v, v < n ∧ lab' v = c) → lam ≤ cost n wt lab')
    (hslack : 4 * cost n wt lab < 4 * lam + Dg) : False := by
  have hown := own_bound n wt hloop hle1 lab u R hu hR
  have hsum := row_three n wt lab u hlab
  have hiu := hlab u hu
  have hus : u ≠ s := fun e => hi ((hsing u hu).mpr e)
  -- the singleton part contributes at most the one edge us
  have hN0 : row n wt u (part lab 0) ≤ 1 := by
    have hp : lsum (List.range n) (fun y => ind (y == s) * wt u y) = wt u s :=
      pick (fun y => wt u y) s n hs
    have hle : row n wt u (part lab 0) ≤ lsum (List.range n) (fun y => ind (y == s) * wt u y) := by
      unfold row part
      apply lsum_mono
      intro y hy
      by_cases h : lab y = 0
      · have := (hsing y (List.mem_range.mp hy)).mp h
        subst this; simp [h, ind]
      · simp [h, ind]
    have := hle1 u s
    omega
  -- move u to the other nonsingleton part t = 3 - i
  have ht : 3 - lab u < 3 := by omega
  have hm := move n wt hsym hloop lab u (3 - lab u) hu
  have hadm := hopt (upd lab u (3 - lab u))
    (by intro y hy; unfold upd; by_cases h : y = u <;> simp [h, ht, hlab y hy])
    (by
      intro c hc
      rcases (by omega : c = 0 ∨ c = lab u ∨ c = 3 - lab u) with h | h | h
      · refine ⟨s, hs, ?_⟩
        have : (s == u) = false := by simp; omega
        simp [upd, this, h, (hsing s hs).mpr rfl]
      · obtain ⟨v, hv, hvu, hvc⟩ := hother
        refine ⟨v, hv, ?_⟩
        have : (v == u) = false := by simp [hvu]
        simp [upd, this, hvc, h]
      · refine ⟨u, hu, ?_⟩
        simp [upd, h])
  rcases (by omega : lab u = 1 ∨ lab u = 2) with h | h
  · rw [h] at hown hm hadm hpiece
    simp only [show 3 - 1 = 2 from rfl] at hm hadm
    omega
  · rw [h] at hown hm hadm hpiece
    simp only [show 3 - 2 = 1 from rfl] at hm hadm
    omega

/-- Mask bound: the edges separated by at least one selected partition number at most the sum
    of the costs of the selected partitions (used for |F₀| ≤ |K₀|·(λ₃ + D/8)). -/
theorem mask_le_sum_cost (K : List (Nat → Nat)) :
    D n (fun x y => ind (K.any (fun P => P x != P y)) * wt x y)
      ≤ (K.map (fun P => cost n wt P)).foldr (· + ·) 0 := by
  induction K with
  | nil =>
    apply Nat.le_of_eq
    rw [D_congr n _ (fun _ _ => 0) (fun _ _ _ _ => by simp [ind]), D_zero]
    rfl
  | cons P K ih =>
    simp only [List.map, List.foldr]
    have h := D_add n (fun x y => ind (P x != P y) * wt x y)
      (fun x y => ind (K.any (fun P => P x != P y)) * wt x y)
    have hm : D n (fun x y => ind ((P :: K).any (fun P => P x != P y)) * wt x y)
        ≤ D n (fun x y => ind (P x != P y) * wt x y + ind (K.any (fun P => P x != P y)) * wt x y) := by
      apply D_mono
      intro x y _ _
      simp only [List.any_cons]
      cases (P x != P y) <;> cases (K.any (fun P => P x != P y)) <;> simp [ind]
    have hP : cost n wt P = D n (fun x y => ind (P x != P y) * wt x y) := rfl
    omega

/-- Exceptional volume: if X = {v : d(v) ≤ 32·deg_F(v)} then Σ_{v∈X} d(v) ≤ 32 Σ_v deg_F(v)
    = 64|F| (doubled), which gives Σ_{v∈X} d(v) ≤ 2|F|/α. -/
theorem exceptional_volume (dg dF : Nat → Nat) :
    lsum (List.range n) (fun v => ind (decide (dg v ≤ 32 * dF v)) * dg v)
      ≤ 32 * lsum (List.range n) dF := by
  rw [← lsum_mul_left]
  apply lsum_mono
  intro v _
  by_cases h : dg v ≤ 32 * dF v <;> simp [h, ind]

/-! ### The two-singleton optimum (Lemma 12) -/

theorem q_sing (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0) (u : Nat) (hu : u < n) :
    q n wt (sing u) = 2 * deg n wt u := by
  have hl := D_left n u hu (fun x y => ind true * wt x y)
  have hr := D_right n u hu (fun x y => ind true * wt x y)
  have hd : lsum (List.range n) (fun x => ind true * wt x u) = deg n wt u := by
    unfold deg row
    apply lsum_congr
    intro x _
    rw [hsym x u]
  have hd' : lsum (List.range n) (fun y => ind true * wt u y) = deg n wt u := rfl
  have hsplit : q n wt (sing u) = D n (fun x y => ind (x == u) * (ind true * wt x y))
      + D n (fun x y => ind (y == u) * (ind true * wt x y)) := by
    unfold q sing
    rw [← D_add]
    apply D_congr
    intro x y _ _
    by_cases hx : x = u <;> by_cases hy : y = u
    · subst hx; subst hy; simp [hloop, ind]
    · subst hx
      have : (y == x) = false := by simp; omega
      simp [this, ind]
    · subst hy
      have : (x == y) = false := by simp; omega
      simp [this, ind]
    · have h1 : (x == u) = false := by simp; omega
      have h2 : (y == u) = false := by simp; omega
      simp [h1, h2, ind]
  rw [hsplit, hl, hr, hd, hd']
  omega

theorem e_sing (hsym : ∀ x y, wt x y = wt y x) (u v : Nat) (hu : u < n) (hv : v < n)
    (huv : u ≠ v) : e n wt (sing u) (sing v) = 2 * wt u v := by
  have hl := D_left n u hu (fun x y => ind (y == v) * wt x y)
  have hr := D_right n u hu (fun x y => ind (x == v) * wt x y)
  have p1 : lsum (List.range n) (fun y => ind (y == v) * wt u y) = wt u v :=
    pick (fun y => wt u y) v n hv
  have p2 : lsum (List.range n) (fun x => ind (x == v) * wt x u) = wt v u :=
    pick (fun x => wt x u) v n hv
  have hsplit : e n wt (sing u) (sing v) = D n (fun x y => ind (x == u) * (ind (y == v) * wt x y))
      + D n (fun x y => ind (y == u) * (ind (x == v) * wt x y)) := by
    unfold e sing
    rw [← D_add]
    apply D_congr
    intro x y _ _
    have hx := beq_excl x u v huv
    have hy := beq_excl y u v huv
    revert hx hy
    cases (x == u) <;> cases (x == v) <;> cases (y == u) <;> cases (y == v) <;> simp [ind]
  rw [hsplit, hl, hr, p1, p2, hsym v u]
  omega

/-- Equation (4) in undoubled form: cost(P_{u,v}) = d(u) + d(v) - w(u,v) (the doubled cost is
    twice this). -/
theorem two_singleton_value (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (u v : Nat) (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    cost n wt (labUV u v) + 2 * wt u v = 2 * (deg n wt u + deg n wt v) := by
  have h := two_singleton n wt u v huv
  rw [q_sing n wt hsym hloop u hu, q_sing n wt hsym hloop v hv, e_sing n wt hsym u v hu hv huv] at h
  omega

/-- Lemma 12. In a simple graph, let L be the least degree sum of two distinct vertices. Every
    two-singleton partition costs at least L - 1, and at least L unless its two singletons are
    adjacent and have degree sum exactly L (doubled costs). So the optimum is L - 1 when an
    edge joins a pair of degree sum L, and L otherwise. -/
theorem two_singleton_opt (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) (L : Nat)
    (hL : ∀ u v, u < n → v < n → u ≠ v → L ≤ deg n wt u + deg n wt v)
    (u v : Nat) (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    2 * (L - 1) ≤ cost n wt (labUV u v) ∧
    (cost n wt (labUV u v) < 2 * L → wt u v = 1 ∧ deg n wt u + deg n wt v = L) := by
  have h := two_singleton_value n wt hsym hloop u v hu hv huv
  have h1 := hL u v hu hv huv
  have h2 := hle1 u v
  constructor
  · omega
  · intro hlt
    omega

/-! ### Complete graphs: λ₃(K_m) = 2m - 3 -/

/-- The complete graph on 0..n-1. -/
def wK : Nat → Nat → Nat := fun x y => ind (x != y)

theorem cnt_compl (X : Nat → Bool) : cnt n X + cnt n (fun y => !X y) = n := by
  unfold cnt
  rw [← lsum_add]
  have : lsum (List.range n) (fun y => ind (X y) + ind (!X y)) = lsum (List.range n) (fun _ => 1) := by
    apply lsum_congr; intro y _; cases X y <;> rfl
  rw [this]
  clear this
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, lsum_append, ih]; rfl

/-- In K_n, a shore X with |X| = a has cut value a(n-a) (doubled: 2a(n-a)). -/
theorem kn_cut (X : Nat → Bool) :
    q n wK X = cnt n X * cnt n (fun y => !X y) + cnt n (fun y => !X y) * cnt n X := by
  unfold q D wK
  have inner : ∀ x, lsum (List.range n) (fun y => ind (X x != X y) * ind (x != y))
      = ind (X x) * cnt n (fun y => !X y) + ind (!X x) * cnt n X := by
    intro x
    unfold cnt
    rw [← lsum_mul_left, ← lsum_mul_left, ← lsum_add]
    apply lsum_congr
    intro y _
    by_cases hxy : x = y
    · subst hxy; cases hx : X x <;> simp [ind, hx]
    · have : (x != y) = true := by simp [hxy]
      rw [this]
      cases hx : X x <;> cases hy : X y <;> simp [ind, hx, hy]
  rw [lsum_congr _ _ _ (fun x _ => inner x), lsum_add, lsum_mul, lsum_mul]
  rfl

/-- λ₃(K_m) ≥ 2m - 3: every 3-partition of K_n costs at least 2n - 3 (doubled: 2(2n - 3)).
    Isolating two vertices costs exactly 2n - 3 (by `two_singleton_value`), so λ₃(K_n) = 2n - 3. -/
theorem kn_lambda3 (lab : Nat → Nat) (hlab : ∀ y, y < n → lab y < 3)
    (hne : ∀ c, c < 3 → 1 ≤ cnt n (part lab c)) :
    2 * (2 * n - 3) ≤ cost n wK lab := by
  have hs := shore_sum n wK 3 lab hlab
  simp only [List.range, List.range.loop, lsum] at hs
  rw [kn_cut, kn_cut, kn_cut] at hs
  have c0 := cnt_compl n (part lab 0)
  have c1 := cnt_compl n (part lab 1)
  have c2 := cnt_compl n (part lab 2)
  -- the three parts cover the vertices
  have htot : cnt n (part lab 0) + cnt n (part lab 1) + cnt n (part lab 2) = n := by
    unfold cnt part
    rw [← lsum_add, ← lsum_add]
    have : lsum (List.range n) (fun y => ind (lab y == 0) + ind (lab y == 1) + ind (lab y == 2))
        = lsum (List.range n) (fun _ => 1) := by
      apply lsum_congr
      intro y hy
      have := hlab y (List.mem_range.mp hy)
      rcases (by omega : lab y = 0 ∨ lab y = 1 ∨ lab y = 2) with h | h | h <;> simp [h, ind]
    rw [this]
    have := cnt_compl n (fun _ => true)
    unfold cnt at this
    simp only [Bool.not_true] at this
    have z : lsum (List.range n) (fun _ => ind false) = 0 := lsum_zero _
    simp only [ind_true] at this
    omega
  have n0 := hne 0 (by omega)
  have n1 := hne 1 (by omega)
  have n2 := hne 2 (by omega)
  generalize cnt n (part lab 0) = a at *
  generalize cnt n (part lab 1) = b at *
  generalize cnt n (part lab 2) = c at *
  generalize cnt n (fun y => !part lab 0 y) = a' at *
  generalize cnt n (fun y => !part lab 1 y) = b' at *
  generalize cnt n (fun y => !part lab 2 y) = c' at *
  have ha' : a' = b + c := by omega
  have hb' : b' = a + c := by omega
  have hc' : c' = a + b := by omega
  subst ha' hb' hc'
  have k := kn_three_parts a b c n0 n1 n2
  simp only [Nat.mul_add, Nat.add_mul] at hs
  have e1 : b * a = a * b := Nat.mul_comm _ _
  have e2 : c * a = a * c := Nat.mul_comm _ _
  have e3 : c * b = b * c := Nat.mul_comm _ _
  omega

/-! ### Strict monotonicity of λ_k on connected graphs (used in Corollary 28) -/

def merge (lab : Nat → Nat) (j c : Nat) : Nat → Nat := fun z => if lab z == j then c else lab z

theorem D_ge_two (f : Nat → Nat → Nat) (x y : Nat) (hx : x < n) (hy : y < n) (hxy : x ≠ y) :
    f x y + f y x ≤ D n f := by
  have hl := D_left n x hx (fun x' y' => ind (y' == y) * f x' y')
  have hr := D_right n x hx (fun x' y' => ind (x' == y) * f x' y')
  have p1 : lsum (List.range n) (fun y' => ind (y' == y) * f x y') = f x y := pick (fun y' => f x y') y n hy
  have p2 : lsum (List.range n) (fun x' => ind (x' == y) * f x' x) = f y x := pick (fun x' => f x' x) y n hy
  have hle : D n (fun x' y' => ind (x' == x) * (ind (y' == y) * f x' y'))
      + D n (fun x' y' => ind (y' == x) * (ind (x' == y) * f x' y')) ≤ D n f := by
    rw [← D_add]
    apply D_mono
    intro x' y' _ _
    by_cases h1 : x' = x <;> by_cases h2 : y' = y <;> by_cases h3 : y' = x <;> by_cases h4 : x' = y <;>
      simp_all [ind] <;> omega
  rw [hl, hr, p1, p2] at hle
  exact hle

theorem D_pos (f : Nat → Nat → Nat) (h : 1 ≤ D n f) : ∃ x y, x < n ∧ y < n ∧ 1 ≤ f x y := by
  have aux : ∀ (l : List Nat) (g : Nat → Nat), 1 ≤ lsum l g → ∃ a, a ∈ l ∧ 1 ≤ g a := by
    intro l g hg
    induction l with
    | nil => simp [lsum] at hg
    | cons a l ih =>
      simp only [lsum] at hg
      by_cases ha : 1 ≤ g a
      · exact ⟨a, by simp, ha⟩
      · obtain ⟨b, hb, hb1⟩ := ih (by omega)
        exact ⟨b, by simp [hb], hb1⟩
  unfold D at h
  obtain ⟨x, hx, hx1⟩ := aux _ _ h
  obtain ⟨y, hy, hy1⟩ := aux _ _ hx1
  exact ⟨x, y, List.mem_range.mp hx, List.mem_range.mp hy, hy1⟩

theorem pt_merge (a b j c w : Nat) (hcj : c ≠ j) :
    ind ((if a == j then c else a) != (if b == j then c else b)) * w
      + ind ((a == j && b == c) || (a == c && b == j)) * w = ind (a != b) * w := by
  simp only [ind, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  repeat' split
  all_goals omega

/-- Merging part j into part c removes every edge between them. -/
theorem merge_step (hsym : ∀ x y, wt x y = wt y x) (lab : Nat → Nat) (j c : Nat) (hcj : c ≠ j)
    (x y : Nat) (hx : x < n) (hy : y < n) (hxj : lab x = j) (hyc : lab y = c)
    (hw : 1 ≤ wt x y) : cost n wt (merge lab j c) + 2 ≤ cost n wt lab := by
  have hxy : x ≠ y := by intro h; subst h; omega
  have hsplit : cost n wt (merge lab j c)
      + D n (fun x' y' => ind ((lab x' == j && lab y' == c) || (lab x' == c && lab y' == j)) * wt x' y')
      = cost n wt lab := by
    unfold cost merge
    rw [← D_add]
    apply D_congr
    intro x' y' _ _
    exact pt_merge (lab x') (lab y') j c (wt x' y') hcj
  have hge := D_ge_two n (fun x' y' => ind ((lab x' == j && lab y' == c) || (lab x' == c && lab y' == j)) * wt x' y')
    x y hx hy hxy
  dsimp only at hge
  have hcj' : (c == j) = false := by simp [hcj]
  have fx : ind ((lab x == j && lab y == c) || (lab x == c && lab y == j)) = 1 := by
    simp [hxj, hyc, ind]
  have fy : ind ((lab y == j && lab x == c) || (lab y == c && lab x == j)) = 1 := by
    simp [hxj, hyc, ind]
  rw [fx, fy, hsym y x] at hge
  omega

/-- λ_{j+1} ≥ λ_j + 1 on connected graphs (inequality (strict-k-monotonicity) of the paper):
    from every (j+1)-partition with nonempty parts one gets a j-partition with nonempty parts
    whose (doubled) cost is smaller by at least 2. Connectivity is stated as: every nonempty
    proper vertex set has a crossing edge. -/
theorem strict_mono (hsym : ∀ x y, wt x y = wt y x)
    (hconn : ∀ X : Nat → Bool, (∃ x, x < n ∧ X x = true) → (∃ y, y < n ∧ X y = false) →
      1 ≤ q n wt X)
    (j : Nat) (hj : 1 ≤ j) (lab : Nat → Nat) (hlab : ∀ y, y < n → lab y < j + 1)
    (hne : ∀ c, c < j + 1 → ∃ v, v < n ∧ lab v = c) :
    ∃ lab' : Nat → Nat, (∀ y, y < n → lab' y < j) ∧ (∀ c, c < j → ∃ v, v < n ∧ lab' v = c) ∧
      cost n wt lab' + 2 ≤ cost n wt lab := by
  obtain ⟨xj, hxj, hxjl⟩ := hne j (by omega)
  obtain ⟨x0, hx0, hx0l⟩ := hne 0 (by omega)
  have hq := hconn (part lab j) ⟨xj, hxj, by simp [part, hxjl]⟩
    ⟨x0, hx0, by simp [part, hx0l]; omega⟩
  unfold q at hq
  obtain ⟨x, y, hx, hy, hpos⟩ := D_pos n _ hq
  have hcross : (part lab j x != part lab j y) = true ∧ 1 ≤ wt x y := by
    by_cases h : (part lab j x != part lab j y) = true
    · refine ⟨h, ?_⟩
      simp [h, ind] at hpos
      exact hpos
    · simp [ind] at hpos
      exact absurd hpos (by simp_all)
  obtain ⟨hc1, hw⟩ := hcross
  -- one endpoint is in part j, the other in a part c < j
  have key : ∃ x' y', x' < n ∧ y' < n ∧ lab x' = j ∧ lab y' ≠ j ∧ 1 ≤ wt x' y' := by
    by_cases hxjj : lab x = j
    · have : lab y ≠ j := by
        intro h; simp [part, hxjj, h] at hc1
      exact ⟨x, y, hx, hy, hxjj, this, hw⟩
    · have : lab y = j := by
        by_cases h : lab y = j
        · exact h
        · exfalso
          have e1 : (lab x == j) = false := by simp [hxjj]
          have e2 : (lab y == j) = false := by simp [h]
          simp [part, e1, e2] at hc1
      exact ⟨y, x, hy, hx, this, hxjj, by rw [hsym]; exact hw⟩
  obtain ⟨x', y', hx', hy', hx'j, hy'j, hw'⟩ := key
  have hyc : lab y' < j := by have := hlab y' hy'; omega
  refine ⟨merge lab j (lab y'), ?_, ?_, ?_⟩
  · intro z hz
    unfold merge
    by_cases h : lab z = j
    · simp [h, hyc]
    · have := hlab z hz
      simp [h]; omega
  · intro c hc
    obtain ⟨v, hv, hvc⟩ := hne c (by omega)
    refine ⟨v, hv, ?_⟩
    have hvj : lab v ≠ j := by omega
    unfold merge
    rw [if_neg (by simp [hvj]), hvc]
  · exact merge_step n wt hsym lab j (lab y') hy'j x' y' hx' hy' hx'j rfl hw'

/-! ### Theorem 18: the covering argument for fixed k with at most two singleton parts -/

theorem lsum_ones (k : Nat) : lsum (List.range k) (fun _ => 1) = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.range_succ, lsum_append, ih]; rfl

theorem count_eq (a k : Nat) (h : a < k) : lsum (List.range k) (fun i => ind (a == i)) = 1 := by
  have := count_one a true k
  simp only [Bool.and_true] at this
  rw [this]; simp [h, ind]

theorem lsum_ge_term (f : Nat → Nat) (c k : Nat) (hc : c < k) : f c ≤ lsum (List.range k) f := by
  have hp := pick f c k hc
  have hle : lsum (List.range k) (fun x => ind (x == c) * f x) ≤ lsum (List.range k) f := by
    apply lsum_mono
    intro x _
    by_cases h : x = c <;> simp [h, ind]
  omega

/-- The neighbours of u split over the k parts. -/
theorem row_k (k : Nat) (lab : Nat → Nat) (u : Nat) (hk : ∀ y, y < n → lab y < k) :
    lsum (List.range k) (fun c => row n wt u (part lab c)) = deg n wt u := by
  unfold row deg part
  rw [lsum_swap]
  apply lsum_congr
  intro y hy
  rw [lsum_mul, count_eq (lab y) k (hk y (List.mem_range.mp hy))]
  simp [ind]

/-- The arithmetic of Theorem 18 (with K = 8k). -/
theorem general_k_arith (K m d Dg a S cost lam : Nat)
    (h1 : m * lam + 2 * S ≤ m * cost + 2 * (m * a))
    (h2 : d ≤ S + a + 2)
    (h3 : K * cost < K * lam + Dg)
    (h4 : 2 * (K * a) + 2 * K < Dg + d)
    (h5 : 1 ≤ m) (h5' : 8 * (m + 1) ≤ K)
    (h6 : K < 4 * Dg) (h7 : Dg ≤ d) : False := by
  have s1 := Nat.mul_le_mul_left K h1
  rw [Nat.mul_add, Nat.mul_add] at s1
  have q1 : K * (2 * S) = 2 * (K * S) := Nat.mul_left_comm _ _ _
  have q2 : K * (2 * (m * a)) = 2 * (K * (m * a)) := Nat.mul_left_comm _ _ _
  have s2 : m * (K * cost + 1) ≤ m * (K * lam + Dg) := Nat.mul_le_mul_left m (by omega)
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at s2
  have q3 : m * (K * cost) = K * (m * cost) := Nat.mul_left_comm _ _ _
  have q4 : m * (K * lam) = K * (m * lam) := Nat.mul_left_comm _ _ _
  have s3 : m * (2 * (K * a) + 2 * K + 1) ≤ m * (Dg + d) := Nat.mul_le_mul_left m (by omega)
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one] at s3
  have q5 : m * (2 * (K * a)) = 2 * (K * (m * a)) := by
    rw [Nat.mul_left_comm, Nat.mul_left_comm m K]
  have q6 : m * (2 * K) = 2 * (K * m) := by rw [Nat.mul_left_comm, Nat.mul_comm m K]
  have s4 := Nat.mul_le_mul_left K h2
  rw [Nat.mul_add, Nat.mul_add] at s4
  have q7 : K * 2 = 2 * K := Nat.mul_comm _ _
  have s5 : m * Dg ≤ m * d := Nat.mul_le_mul_left m h7
  have s6 := Nat.mul_le_mul_right d h5'
  have q8 : 8 * (m + 1) * d = 8 * (m * d) + 8 * d := by
    rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul, Nat.mul_add]
  have s7 : K * 2 ≤ K * d := Nat.mul_le_mul_left K (by omega)
  have hKm : K ≤ K * m := by
    have := Nat.mul_le_mul_left K h5
    rw [Nat.mul_one] at this; exact this
  omega

/-- Theorem 18 (at most two singleton parts), graph-level core of the covering argument. The
    k-partition `lab` has parts flagged `sg c` (singleton parts, each with at most one vertex),
    at most two of them; u lies in a nonsingleton part i that has another vertex, and some other
    part is nonsingleton. With α = η = 1/(16k): the candidate has cost below λ_k + ηD
    (doubled: 8k·cost < 8k·λ + D), u is not exceptional (16k·deg_F(u) < d(u)), d(u) ≥ D > 2k,
    and u's own part meets the atom R of u in fewer than αD vertices. This is impossible. -/
theorem cover_general_k (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1)
    (k : Nat) (lab : Nat → Nat) (sg : Nat → Bool) (u : Nat) (R : Nat → Bool) (Dg lam : Nat)
    (hu : u < n) (hlab : ∀ y, y < n → lab y < k)
    (hne : ∀ c, c < k → ∃ v, v < n ∧ lab v = c)
    (hins : sg (lab u) = false)
    (hother : ∃ v, v < n ∧ v ≠ u ∧ lab v = lab u)
    (hsg : ∀ c, c < k → sg c = true → ∀ y z, y < n → z < n → lab y = c → lab z = c → y = z)
    (hs2 : lsum (List.range k) (fun c => ind (sg c)) ≤ 2)
    (hm : ∃ c, c < k ∧ sg c = false ∧ c ≠ lab u)
    (hR : R u = true)
    (hpiece : 16 * k * cnt n (fun y => R y && (lab y == lab u)) < Dg)
    (hX : 16 * k * row n wt u (fun y => !R y) < deg n wt u)
    (hdeg : Dg ≤ deg n wt u) (hD : 2 * k < Dg)
    (hopt : ∀ lab' : Nat → Nat, (∀ y, y < n → lab' y < k) →
      (∀ c, c < k → ∃ v, v < n ∧ lab' v = c) → lam ≤ cost n wt lab')
    (hslack : 8 * k * cost n wt lab < 8 * k * lam + Dg) : False := by
  have hik := hlab u hu
  -- notation
  have hrow := row_k n wt k lab u hlab
  -- (A) the parts split into: u's part, singleton parts, other nonsingleton parts
  have hA : lsum (List.range k) (fun c => ind (!sg c && c != lab u) * row n wt u (part lab c))
      + lsum (List.range k) (fun c => ind (sg c) * row n wt u (part lab c))
      + row n wt u (part lab (lab u)) = deg n wt u := by
    rw [← pick (fun c => row n wt u (part lab c)) (lab u) k hik, ← lsum_add, ← lsum_add, ← hrow]
    apply lsum_congr
    intro c _
    by_cases h1 : c = lab u
    · subst h1; simp [hins, ind]
    · have h2 : (c == lab u) = false := by simp [h1]
      cases hs : sg c <;> simp [h1, h2, hs, ind]
  -- (B) each singleton part holds at most one neighbour of u
  have hB : lsum (List.range k) (fun c => ind (sg c) * row n wt u (part lab c)) ≤ 2 := by
    have : lsum (List.range k) (fun c => ind (sg c) * row n wt u (part lab c))
        ≤ lsum (List.range k) (fun c => ind (sg c)) := by
      apply lsum_mono
      intro c hc
      have hck := List.mem_range.mp hc
      cases hs : sg c
      · simp [ind]
      · obtain ⟨z, hz, hzc⟩ := hne c hck
        have hp : lsum (List.range n) (fun y => ind (y == z) * wt u y) = wt u z :=
          pick (fun y => wt u y) z n hz
        have hle : row n wt u (part lab c) ≤ lsum (List.range n) (fun y => ind (y == z) * wt u y) := by
          unfold row part
          apply lsum_mono
          intro y hy
          by_cases h : lab y = c
          · have := hsg c hck hs y z (List.mem_range.mp hy) hz h hzc
            subst this; simp [h, ind]
          · simp [h, ind]
        have := hle1 u z
        simp [ind]; omega
    omega
  -- (C) moving u into any other nonsingleton part does not beat λ
  have hC : lsum (List.range k) (fun c => ind (!sg c && c != lab u) * lam
        + 2 * (ind (!sg c && c != lab u) * row n wt u (part lab c)))
      ≤ lsum (List.range k) (fun c => ind (!sg c && c != lab u) * cost n wt lab
        + 2 * (ind (!sg c && c != lab u) * row n wt u (part lab (lab u)))) := by
    apply lsum_mono
    intro c hc
    have hck := List.mem_range.mp hc
    by_cases hns : (!sg c && c != lab u) = true
    · simp only [hns, ind_true, ite_true, Nat.one_mul]
      have hcu : c ≠ lab u := by
        intro h; subst h; simp at hns
      have hmv := move n wt hsym hloop lab u c hu
      have hadm := hopt (upd lab u c)
        (by intro y hy; unfold upd; by_cases h : y = u <;> simp [h, hck, hlab y hy])
        (by
          intro c' hc'
          by_cases h : c' = lab u
          · obtain ⟨v, hv, hvu, hvc⟩ := hother
            refine ⟨v, hv, ?_⟩
            have : (v == u) = false := by simp [hvu]
            simp [upd, this, hvc, h]
          · obtain ⟨v, hv, hvc⟩ := hne c' hc'
            refine ⟨v, hv, ?_⟩
            have hvu : v ≠ u := by intro e; subst e; exact h hvc.symm
            have : (v == u) = false := by simp [hvu]
            simp [upd, this, hvc])
      have : ind true = 1 := rfl
      simp only [ind] at *
      omega
    · have : (!sg c && c != lab u) = false := by simpa using hns
      simp [this, ind]
  rw [lsum_add, lsum_add, lsum_mul, lsum_mul, lsum_mul_left, lsum_mul_left, lsum_mul] at hC
  -- counting the other nonsingleton parts: 1 ≤ m and m + 1 ≤ k
  have hm1 : 1 ≤ lsum (List.range k) (fun c => ind (!sg c && c != lab u)) := by
    obtain ⟨c, hck, hs, hcu⟩ := hm
    have := lsum_ge_term (fun c => ind (!sg c && c != lab u)) c k hck
    have h1 : (!sg c && c != lab u) = true := by simp [hs, hcu]
    simp only [h1, ind_true] at this
    exact this
  have hm2 : lsum (List.range k) (fun c => ind (!sg c && c != lab u)) + 1 ≤ k := by
    have hp := pick (fun _ => 1) (lab u) k hik
    dsimp only at hp
    have hle : lsum (List.range k) (fun c => ind (!sg c && c != lab u))
        + lsum (List.range k) (fun c => ind (c == lab u) * 1) ≤ lsum (List.range k) (fun _ => 1) := by
      rw [← lsum_add]
      apply lsum_mono
      intro c _
      by_cases h : c = lab u
      · subst h; simp [ind]
      · have : (c == lab u) = false := by simp [h]
        cases sg c <;> simp [this, h, ind]
    have hk := lsum_ones k
    omega
  -- own-part bound and the final arithmetic
  have hown := own_bound n wt hloop hle1 lab u R hu hR
  have h16 : 16 * k * (row n wt u (part lab (lab u)) + 1)
      ≤ 16 * k * (cnt n (fun y => R y && (lab y == lab u)) + row n wt u (fun y => !R y)) :=
    Nat.mul_le_mul_left _ hown
  have hR16 : 16 * k * (cnt n (fun y => R y && (lab y == lab u)) + row n wt u (fun y => !R y))
      = 16 * k * cnt n (fun y => R y && (lab y == lab u)) + 16 * k * row n wt u (fun y => !R y) :=
    Nat.mul_add _ _ _
  have h16' : 16 * k * (row n wt u (part lab (lab u)) + 1)
      = 2 * (8 * k * row n wt u (part lab (lab u))) + 2 * (8 * k) := by
    rw [Nat.mul_add, Nat.mul_one, show 16 * k = 2 * (8 * k) by omega, Nat.mul_assoc]
  exact general_k_arith (8 * k) (lsum (List.range k) (fun c => ind (!sg c && c != lab u)))
    (deg n wt u) Dg (row n wt u (part lab (lab u)))
    (lsum (List.range k) (fun c => ind (!sg c && c != lab u) * row n wt u (part lab c)))
    (cost n wt lab) lam hC (by omega) hslack (by omega) hm1 (by omega) (by omega) hdeg

/-! ### Lemma 25 (Li's gadget) at graph level: the lower bound λ_k ≥ T

  Base vertices R (all of degree p, in parts 1, ..., k-1) and everything else, including the
  clique W, in part 0. The cost identity is equation (li-cost) of the paper; the two bounds use
  simplicity; convexity and the identity of Part D finish the proof. -/

def own (lab : Nat → Nat) (R : Nat → Bool) : Nat :=
  D n (fun x y => ind (R x && (lab x == lab y)) * wt x y)

def inner (R : Nat → Bool) : Nat := D n (fun x y => ind (R x && R y) * wt x y)

theorem pt_li (Rx Ry : Bool) (lx ly w : Nat) (hx : lx = 0 ↔ Rx = false) (hy : ly = 0 ↔ Ry = false) :
    ind (lx != ly) * w + ind (Rx && (lx == ly)) * w + ind (Rx && Ry) * w
      = ind Rx * w + ind Ry * w := by
  cases Rx <;> cases Ry <;> simp at hx hy <;>
    simp only [ind, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, beq_iff_eq,
      bne_iff_ne, ne_eq] <;> repeat' split
  all_goals simp_all <;> omega

theorem sum_R_deg (hsym : ∀ x y, wt x y = wt y x) (R : Nat → Bool) (p : Nat)
    (hdeg : ∀ x, x < n → R x = true → deg n wt x = p) :
    D n (fun x y => ind (R x) * wt x y) = p * cnt n R ∧
    D n (fun x y => ind (R y) * wt x y) = p * cnt n R := by
  have hrow : ∀ x, x < n → lsum (List.range n) (fun y => wt x y) = deg n wt x := by
    intro x _; unfold deg row; apply lsum_congr; intro y _; simp [ind]
  have h1 : D n (fun x y => ind (R x) * wt x y) = lsum (List.range n) (fun x => ind (R x) * p) := by
    unfold D
    apply lsum_congr
    intro x hx
    rw [lsum_mul_left, hrow x (List.mem_range.mp hx)]
    cases hR : R x
    · simp [ind]
    · simp [ind, hdeg x (List.mem_range.mp hx) hR]
  constructor
  · rw [h1, lsum_mul]; unfold cnt; exact Nat.mul_comm _ _
  · unfold D
    rw [lsum_swap]
    have : lsum (List.range n) (fun y => lsum (List.range n) (fun x => ind (R y) * wt x y))
        = lsum (List.range n) (fun x => ind (R x) * p) := by
      apply lsum_congr
      intro y hy
      rw [lsum_mul_left]
      have : lsum (List.range n) (fun x => wt x y) = deg n wt y := by
        rw [← hrow y (List.mem_range.mp hy)]; apply lsum_congr; intro x _; exact hsym x y
      rw [this]
      cases hR : R y
      · simp [ind]
      · simp [ind, hdeg y (List.mem_range.mp hy) hR]
    rw [this, lsum_mul]; unfold cnt; exact Nat.mul_comm _ _

/-- Equation (li-cost): cost + (doubled saved edges) = 2pr, where the saved edges are those
    inside the parts S_i (counted in `own`) and inside R (counted in `inner`). -/
theorem li_cost_identity (hsym : ∀ x y, wt x y = wt y x) (lab : Nat → Nat) (R : Nat → Bool)
    (p : Nat) (hR : ∀ x, x < n → (lab x = 0 ↔ R x = false))
    (hdeg : ∀ x, x < n → R x = true → deg n wt x = p) :
    cost n wt lab + own n wt lab R + inner n wt R = 2 * (p * cnt n R) := by
  obtain ⟨h1, h2⟩ := sum_R_deg n wt hsym R p hdeg
  have : cost n wt lab + own n wt lab R + inner n wt R
      = D n (fun x y => ind (R x) * wt x y) + D n (fun x y => ind (R y) * wt x y) := by
    unfold cost own inner
    rw [← D_add, ← D_add, ← D_add]
    apply D_congr
    intro x y hx hy
    exact pt_li (R x) (R y) (lab x) (lab y) (wt x y) (hR x hx) (hR y hy)
  omega

/-- Σ_y [P y ∧ y ≠ x] = |P| - 1 for x ∈ P. -/
theorem cnt_minus (P : Nat → Bool) (x : Nat) (hx : x < n) (hP : P x = true) :
    lsum (List.range n) (fun y => ind (P y && (y != x))) + 1 = cnt n P := by
  have hp := pick (fun _ => 1) x n hx
  dsimp only at hp
  rw [← hp]
  unfold cnt
  rw [← lsum_add]
  apply lsum_congr
  intro y _
  by_cases h : y = x
  · subst h; simp [hP, ind]
  · simp [h, ind]

/-- In a simple graph the edges inside R number at most C(r,2) (doubled: r(r-1)). -/
theorem inner_le (hloop : ∀ x, wt x x = 0) (hle1 : ∀ x y, wt x y ≤ 1) (R : Nat → Bool) :
    inner n wt R ≤ c2 (cnt n R) := by
  have step : inner n wt R ≤ lsum (List.range n) (fun x => ind (R x) * (cnt n R - 1)) := by
    unfold inner D
    apply lsum_mono
    intro x hx
    dsimp only
    have hxn := List.mem_range.mp hx
    cases hRx : R x
    · rw [lsum_congr _ _ (fun _ => 0) (fun y _ => by simp [ind]), lsum_zero]; exact Nat.zero_le _
    · have hc := cnt_minus n R x hxn hRx
      have : lsum (List.range n) (fun y => ind (true && R y) * wt x y)
          ≤ lsum (List.range n) (fun y => ind (R y && (y != x))) := by
        apply lsum_mono
        intro y _
        have := hle1 x y
        by_cases h : y = x
        · subst h; simp [hloop, ind]
        · cases R y <;> simp [h, ind] <;> omega
      have e : ind true * (cnt n R - 1) = cnt n R - 1 := by simp [ind]
      rw [e]; omega
  rw [lsum_mul] at step
  unfold c2
  have : lsum (List.range n) (fun x => ind (R x)) = cnt n R := rfl
  rw [this] at step
  exact step

theorem pick_alt (b : Bool) (a k : Nat) (g : Nat → Nat) (h : a < k) :
    ind b * g a = lsum (List.range k) (fun i => ind (b && (a == i)) * g i) := by
  cases b
  · rw [lsum_congr _ _ (fun _ => 0) (fun i _ => by simp [ind]), lsum_zero]; simp [ind]
  · rw [show ind true * g a = g a by simp [ind], ← pick g a k h]
    apply lsum_congr
    intro i _
    by_cases hi : i = a
    · subst hi; simp [ind]
    · have h1 : a ≠ i := fun e => hi e.symm
      simp [ind, hi, h1]

/-- Grouping a sum over R by part: Σ_{x∈R} g(lab x) = Σ_{i<k} |R ∩ P_i|·g(i). -/
theorem group_by_part (k : Nat) (lab : Nat → Nat) (hk : ∀ y, y < n → lab y < k) (R : Nat → Bool)
    (g : Nat → Nat) :
    lsum (List.range n) (fun x => ind (R x) * g (lab x))
      = lsum (List.range k) (fun i => cnt n (fun x => R x && (lab x == i)) * g i) := by
  have : lsum (List.range n) (fun x => ind (R x) * g (lab x))
      = lsum (List.range n) (fun x => lsum (List.range k) (fun i => ind (R x && (lab x == i)) * g i)) := by
    apply lsum_congr
    intro x hx
    have hxk := hk x (List.mem_range.mp hx)
    rw [pick_alt]
    · exact hxk
  rw [this, lsum_swap]
  apply lsum_congr
  intro i _
  rw [lsum_mul]; rfl

/-- The edges inside the parts: Σ_x [x ∈ R] (|P_{lab x}| - 1). -/
theorem own_le (hloop : ∀ x, wt x x = 0) (hle1 : ∀ x y, wt x y ≤ 1) (lab : Nat → Nat)
    (R : Nat → Bool) :
    own n wt lab R ≤ lsum (List.range n) (fun x => ind (R x) * (cnt n (part lab (lab x)) - 1)) := by
  unfold own D
  apply lsum_mono
  intro x hx
  dsimp only
  have hxn := List.mem_range.mp hx
  cases hRx : R x
  · rw [lsum_congr _ _ (fun _ => 0) (fun y _ => by simp [ind]), lsum_zero]; exact Nat.zero_le _
  · have hc := cnt_minus n (part lab (lab x)) x hxn (by simp [part])
    have : lsum (List.range n) (fun y => ind (true && (lab x == lab y)) * wt x y)
        ≤ lsum (List.range n) (fun y => ind (part lab (lab x) y && (y != x))) := by
      apply lsum_mono
      intro y _
      have := hle1 x y
      by_cases h : y = x
      · subst h; simp [hloop, ind]
      · by_cases hl : lab x = lab y
        · simp [h, hl, part, ind]; omega
        · have hl' : lab y ≠ lab x := fun e => hl e.symm
          simp [hl, hl', part, ind]
    have e : ind true * (cnt n (part lab (lab x)) - 1) = cnt n (part lab (lab x)) - 1 := by simp [ind]
    rw [e]; omega

theorem lsum_map (l : List Nat) (f g : Nat → Nat) : lsum (l.map f) g = lsum l (fun x => g (f x)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map, lsum, ih]

theorem total_eq (l : List Nat) : total l = lsum l (fun x => x) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [total, lsum, ih]

/-- The identity of Part D over the naturals, with k = m + 2, r = m + 1 + a, p = r + b. -/
theorem li_nat (m a b : Nat) :
    2 * ((m + 1 + a + b) * (m + 1 + a)) + c2 (m + 1)
      = c2 (m + 1 + a) + c2 (a + 1) + 2 * ((m + 1) * (m + 1 + a + b)) + 2 * (a * b) := by
  unfold c2
  simp only [Nat.add_sub_cancel, show m + 1 + a - 1 = m + a by omega]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.two_mul]
  simp only [Nat.mul_comm, Nat.mul_left_comm]
  omega

/-- Lemma 25, lower bound: every k-partition of Li's gadget that keeps the clique W (and every
    other non-base vertex) in part 0, with nonempty parts 1, ..., k-1 made of base vertices of
    degree p, costs at least T = (k-1)p - C(k-1,2). Doubled: cost + (k-1)(k-2) ≥ 2(k-1)p.
    Moreover the excess is at least 2(r-k+1)(p-r) (equation (li-lower)). -/
theorem li_gadget_lower (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) (k p : Nat) (hk2 : 2 ≤ k) (lab : Nat → Nat) (R : Nat → Bool)
    (hlab : ∀ y, y < n → lab y < k)
    (hne : ∀ i, 1 ≤ i → i < k → ∃ v, v < n ∧ lab v = i)
    (hR : ∀ x, x < n → (lab x = 0 ↔ R x = false))
    (hdeg : ∀ x, x < n → R x = true → deg n wt x = p)
    (hrp : cnt n R ≤ p) :
    k - 1 ≤ cnt n R ∧
    2 * ((k - 1) * p) + 2 * ((cnt n R - (k - 1)) * (p - cnt n R)) + (c2 (cnt n R) - inner n wt R)
      ≤ cost n wt lab + c2 (k - 1) := by
  have hid := li_cost_identity n wt hsym lab R p hR hdeg
  have hin := inner_le n wt hloop hle1 R
  have hown := own_le n wt hloop hle1 lab R
  -- group the own-part bound by parts: Σ_{i<k} |R ∩ P_i|(|P_i| - 1)
  have hg := group_by_part n k lab hlab R (fun i => cnt n (part lab i) - 1)
  have hRi : ∀ i, 1 ≤ i → cnt n (fun x => R x && (lab x == i)) = cnt n (part lab i) := by
    intro i hi
    unfold cnt part
    apply lsum_congr
    intro x hx
    have := hR x (List.mem_range.mp hx)
    by_cases h : lab x = i
    · have : R x = true := by
        cases hRx : R x
        · have := (hR x (List.mem_range.mp hx)).mpr hRx; omega
        · rfl
      simp [h, this]
    · have e : (lab x == i) = false := by simp [h]
      simp [e]
  have hR0 : cnt n (fun x => R x && (lab x == 0)) = 0 := by
    unfold cnt
    rw [lsum_congr _ _ (fun _ => 0) (fun x hx => by
      have := hR x (List.mem_range.mp hx)
      by_cases h : lab x = 0
      · simp [h, this.mp h, ind]
      · simp [h, ind])]
    exact lsum_zero _
  -- the list of part sizes r_1, ..., r_{k-1}
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  let L := (List.range (m + 1)).map (fun i => cnt n (part lab (i + 1)))
  have hsplit : ∀ (f : Nat → Nat), lsum (List.range (m + 2)) f = f 0 + lsum (List.range (m + 1)) (fun i => f (i + 1)) := by
    intro f
    rw [List.range_succ_eq_map]
    simp only [lsum]
    rw [lsum_map]
  have hown2 : own n wt lab R ≤ lsum L c2 := by
    rw [hg, hsplit, hR0, Nat.zero_mul, Nat.zero_add] at hown
    have : lsum (List.range (m + 1)) (fun i => cnt n (fun x => R x && (lab x == i + 1)) * (cnt n (part lab (i + 1)) - 1))
        = lsum L c2 := by
      show _ = lsum ((List.range (m + 1)).map _) c2
      rw [lsum_map]
      apply lsum_congr
      intro i _
      rw [hRi (i + 1) (by omega)]
      rfl
    omega
  have htotal : total L = cnt n R := by
    have hg1 := group_by_part n (m + 2) lab hlab R (fun _ => 1)
    rw [hsplit, hR0] at hg1
    have e1 : lsum (List.range n) (fun x => ind (R x) * 1) = cnt n R := by
      unfold cnt; apply lsum_congr; intro x _; simp
    rw [e1] at hg1
    rw [hg1, total_eq]
    show lsum ((List.range (m + 1)).map _) (fun x => x) = _
    rw [lsum_map]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.mul_one]
    apply lsum_congr
    intro i _
    rw [hRi (i + 1) (by omega)]
  have hlen : L.length = m + 1 := by simp [L]
  have hpos : ∀ x, x ∈ L → 1 ≤ x := by
    intro x hx
    simp only [L, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    obtain ⟨v, hv, hvl⟩ := hne (i + 1) (by omega) (by omega)
    have := lsum_ge_term (fun y => ind (part lab (i + 1) y)) v n hv
    have e : ind (part lab (i + 1) v) = 1 := by simp [part, hvl, ind]
    dsimp only at this
    rw [e] at this
    unfold cnt
    exact this
  have hconv := convexity L (by simp [L]) hpos
  rw [htotal, hlen] at hconv
  -- r ≥ k - 1 because the k - 1 parts are nonempty and disjoint
  have hr : m + 1 ≤ cnt n R := by
    have : L.length ≤ total L := by
      have aux : ∀ (l : List Nat), (∀ z, z ∈ l → 1 ≤ z) → l.length ≤ total l := by
        intro l hl
        induction l with
        | nil => simp [total]
        | cons z l ihl =>
          simp only [total, List.length_cons]
          have := hl z (by simp)
          have := ihl (fun w hw => hl w (by simp [hw]))
          omega
      exact aux L hpos
    omega
  obtain ⟨a, ha⟩ : ∃ a, cnt n R = m + 1 + a := ⟨cnt n R - (m + 1), by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, p = m + 1 + a + b := ⟨p - cnt n R, by omega⟩
  have hc : cnt n R + 1 - (m + 1) = a + 1 := by omega
  rw [hc] at hconv
  have hnat := li_nat m a b
  rw [ha, hb] at hid
  rw [ha] at hin
  simp only [show m + 2 - 1 = m + 1 from by omega]
  refine ⟨by omega, ?_⟩
  rw [ha, hb, show m + 1 + a - (m + 1) = a from by omega, show m + 1 + a + b - (m + 1 + a) = b from by omega]
  have e1 : (m + 1 + a + b) * (m + 1 + a) = (m + 1 + a) * (m + 1 + a + b) := Nat.mul_comm _ _
  omega

theorem lsum_tight (l : List Nat) (f g : Nat → Nat) (hle : ∀ a, a ∈ l → f a ≤ g a)
    (heq : lsum l f = lsum l g) : ∀ a, a ∈ l → f a = g a := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons b l ih =>
    simp only [lsum] at heq
    have h1 := hle b (by simp)
    have h2 := lsum_mono l f g (fun a ha => hle a (by simp [ha]))
    have hb : f b = g b := by omega
    have hl : lsum l f = lsum l g := by omega
    intro a ha
    rcases List.mem_cons.mp ha with h | h
    · subst h; exact hb
    · exact ih (fun a ha => hle a (by simp [ha])) hl a h

/-- If the inner-edge bound is tight, R is a clique. -/
theorem inner_tight (hloop : ∀ x, wt x x = 0) (hle1 : ∀ x y, wt x y ≤ 1) (R : Nat → Bool)
    (heq : inner n wt R = c2 (cnt n R)) :
    ∀ x y, x < n → y < n → R x = true → R y = true → x ≠ y → wt x y = 1 := by
  intro x y hx hy hRx hRy hxy
  -- per-vertex bounds
  have hpt : ∀ z, z ∈ List.range n →
      lsum (List.range n) (fun v => ind (R z && R v) * wt z v) ≤ ind (R z) * (cnt n R - 1) := by
    intro z hz
    have hzn := List.mem_range.mp hz
    cases hRz : R z
    · rw [lsum_congr _ _ (fun _ => 0) (fun v _ => by simp [ind]), lsum_zero]; exact Nat.zero_le _
    · have hc := cnt_minus n R z hzn hRz
      have : lsum (List.range n) (fun v => ind (true && R v) * wt z v)
          ≤ lsum (List.range n) (fun v => ind (R v && (v != z))) := by
        apply lsum_mono
        intro v _
        have := hle1 z v
        by_cases h : v = z
        · subst h; simp [hloop, ind]
        · cases R v <;> simp [h, ind] <;> omega
      have e : ind true * (cnt n R - 1) = cnt n R - 1 := by simp [ind]
      rw [e]; omega
  have hsum : lsum (List.range n) (fun z => lsum (List.range n) (fun v => ind (R z && R v) * wt z v))
      = lsum (List.range n) (fun z => ind (R z) * (cnt n R - 1)) := by
    have : lsum (List.range n) (fun z => ind (R z) * (cnt n R - 1)) = c2 (cnt n R) := by
      rw [lsum_mul]; rfl
    rw [this, ← heq]; rfl
  have hx' := lsum_tight _ _ _ hpt hsum x (List.mem_range.mpr hx)
  rw [hRx] at hx'
  have hc := cnt_minus n R x hx hRx
  have hpt2 : ∀ v, v ∈ List.range n → ind (true && R v) * wt x v ≤ ind (R v && (v != x)) := by
    intro v _
    have := hle1 x v
    by_cases h : v = x
    · subst h; simp [hloop, ind]
    · cases R v <;> simp [h, ind] <;> omega
  have hsum2 : lsum (List.range n) (fun v => ind (true && R v) * wt x v)
      = lsum (List.range n) (fun v => ind (R v && (v != x))) := by
    have e : ind true * (cnt n R - 1) = cnt n R - 1 := by simp [ind]
    rw [e] at hx'; omega
  have hy' := lsum_tight _ _ _ hpt2 hsum2 y (List.mem_range.mpr hy)
  have hyx : (y != x) = true := by simp; omega
  simp [hRy, hyx, ind] at hy'
  exact hy'

/-- Lemma 25, equality case: if a partition keeping W in part 0 has cost exactly T, then
    r = k - 1 or r = p, and the base vertices R in parts 1, ..., k-1 form a clique with at least
    k - 1 vertices. Hence F contains a (k-1)-clique. -/
theorem li_gadget_equality (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) (k p : Nat) (hk2 : 2 ≤ k) (lab : Nat → Nat) (R : Nat → Bool)
    (hlab : ∀ y, y < n → lab y < k)
    (hne : ∀ i, 1 ≤ i → i < k → ∃ v, v < n ∧ lab v = i)
    (hR : ∀ x, x < n → (lab x = 0 ↔ R x = false))
    (hdeg : ∀ x, x < n → R x = true → deg n wt x = p)
    (hrp : cnt n R ≤ p)
    (heq : cost n wt lab + c2 (k - 1) = 2 * ((k - 1) * p)) :
    (cnt n R = k - 1 ∨ cnt n R = p) ∧ k - 1 ≤ cnt n R ∧
    ∀ x y, x < n → y < n → R x = true → R y = true → x ≠ y → wt x y = 1 := by
  obtain ⟨hr, h⟩ := li_gadget_lower n wt hsym hloop hle1 k p hk2 lab R hlab hne hR hdeg hrp
  have hin := inner_le n wt hloop hle1 R
  have h0 : (cnt n R - (k - 1)) * (p - cnt n R) = 0 := by omega
  refine ⟨?_, hr, inner_tight n wt hloop hle1 R (by omega)⟩
  rcases Nat.mul_eq_zero.mp h0 with h1 | h1
  · left; omega
  · right; omega

/-- Lemma 25, attainment: if the parts 1, ..., k-1 are singletons whose vertices form a clique,
    the cost is exactly 2pr - r(r-1), i.e. T when r = k - 1. -/
theorem li_gadget_attain (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (lab : Nat → Nat) (R : Nat → Bool) (p : Nat)
    (hR : ∀ x, x < n → (lab x = 0 ↔ R x = false))
    (hdeg : ∀ x, x < n → R x = true → deg n wt x = p)
    (hsingle : ∀ x y, x < n → y < n → R x = true → lab x = lab y → x = y)
    (hclique : ∀ x y, x < n → y < n → R x = true → R y = true → x ≠ y → wt x y = 1) :
    cost n wt lab + c2 (cnt n R) = 2 * (p * cnt n R) := by
  have hid := li_cost_identity n wt hsym lab R p hR hdeg
  have hown : own n wt lab R = 0 := by
    unfold own D
    rw [lsum_congr _ _ (fun _ => 0) (fun x hx => by
      rw [lsum_congr _ _ (fun _ => 0) (fun y hy => by
        by_cases hRx : R x = true
        · by_cases hl : lab x = lab y
          · have := hsingle x y (List.mem_range.mp hx) (List.mem_range.mp hy) hRx hl
            subst this; simp [hloop]
          · simp [hl, ind]
        · simp [hRx, ind])]
      exact lsum_zero _)]
    exact lsum_zero _
  have hinner : inner n wt R = lsum (List.range n) (fun x => ind (R x) * (cnt n R - 1)) := by
    unfold inner D
    apply lsum_congr
    intro x hx
    dsimp only
    have hxn := List.mem_range.mp hx
    cases hRx : R x
    · rw [lsum_congr _ _ (fun _ => 0) (fun v _ => by simp [ind]), lsum_zero]; simp [ind]
    · have hc := cnt_minus n R x hxn hRx
      have : lsum (List.range n) (fun y => ind (true && R y) * wt x y)
          = lsum (List.range n) (fun y => ind (R y && (y != x))) := by
        apply lsum_congr
        intro y hy
        by_cases h : y = x
        · subst h; simp [hloop, ind]
        · cases hRy : R y
          · simp [ind]
          · have := hclique x y hxn (List.mem_range.mp hy) hRx hRy (fun e => h e.symm)
            simp [h, this, ind]
      rw [this, show ind true * (cnt n R - 1) = cnt n R - 1 by simp [ind]]; omega
  rw [lsum_mul] at hinner
  have e : lsum (List.range n) (fun x => ind (R x)) * (cnt n R - 1) = c2 (cnt n R) := rfl
  omega

/-- Partitions that split a clique W cut at least |W| - 1 of its edges (doubled: 2(|W| - 1));
    in Li's gadget these cost at least M - 1 > (k-1)p and are never optimal. -/
theorem clique_split (lab : Nat → Nat) (W : Nat → Bool)
    (hW : ∀ x y, x < n → y < n → W x = true → W y = true → x ≠ y → 1 ≤ wt x y)
    (x0 y0 : Nat) (hx0 : x0 < n) (hy0 : y0 < n) (hWx : W x0 = true) (hWy : W y0 = true)
    (hl : lab x0 ≠ lab y0) :
    2 * (cnt n W - 1) ≤ cost n wt lab := by
  have hq := shore_le_cost n wt lab (lab x0)
  generalize hX : part lab (lab x0) = X at hq
  -- q(X) ≥ 2 |W ∩ X| |W ∖ X|
  have hlow : D n (fun x y => ind (W x && W y && (X x != X y))) ≤ q n wt X := by
    unfold q
    apply D_mono
    intro x y hx hy
    by_cases h : (W x && W y && (X x != X y)) = true
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have hxy : x ≠ y := by intro e; subst e; exact h3 rfl
      have := hW x y hx hy h1 h2 hxy
      have e1 : (X x != X y) = true := by simp [h3]
      simp [h1, h2, e1, ind]; omega
    · simp only [Bool.not_eq_true] at h
      rw [h]; simp [ind]
  have inner_eq : ∀ x, lsum (List.range n) (fun y => ind (W x && W y && (X x != X y)))
      = ind (W x && X x) * cnt n (fun y => W y && !X y) + ind (W x && !X x) * cnt n (fun y => W y && X y) := by
    intro x
    unfold cnt
    rw [← lsum_mul_left, ← lsum_mul_left, ← lsum_add]
    apply lsum_congr
    intro y _
    cases h1 : W x <;> cases h2 : X x <;> cases h3 : W y <;> cases h4 : X y <;> simp [ind, h1, h2, h3, h4]
  have hD : D n (fun x y => ind (W x && W y && (X x != X y)))
      = cnt n (fun y => W y && X y) * cnt n (fun y => W y && !X y)
        + cnt n (fun y => W y && !X y) * cnt n (fun y => W y && X y) := by
    unfold D
    rw [lsum_congr _ _ _ (fun x _ => inner_eq x), lsum_add, lsum_mul, lsum_mul]
    rfl
  have hsplit : cnt n (fun y => W y && X y) + cnt n (fun y => W y && !X y) = cnt n W := by
    unfold cnt; rw [← lsum_add]; apply lsum_congr; intro y _
    cases h1 : W y <;> cases h2 : X y <;> simp [ind, h1, h2]
  have ha : 1 ≤ cnt n (fun y => W y && X y) := by
    have := lsum_ge_term (fun y => ind (W y && X y)) x0 n hx0
    have e : ind (W x0 && X x0) = 1 := by rw [← hX]; simp [part, hWx, ind]
    dsimp only at this; rw [e] at this; exact this
  have hb : 1 ≤ cnt n (fun y => W y && !X y) := by
    have := lsum_ge_term (fun y => ind (W y && !X y)) y0 n hy0
    have hne : (lab y0 == lab x0) = false := by simp; omega
    have e : ind (W y0 && !X y0) = 1 := by rw [← hX]; simp [part, hWy, hne, ind]
    dsimp only at this; rw [e] at this; exact this
  have k2 := kn_two_parts _ _ ha hb
  have e1 : cnt n (fun y => W y && !X y) * cnt n (fun y => W y && X y)
      = cnt n (fun y => W y && X y) * cnt n (fun y => W y && !X y) := Nat.mul_comm _ _
  omega

/-! ### Theorem 20: three parts of H_x, and the bridge graph G_x

  These lemmas take the minimum-cut facts of H_x and J = K_{2k} as hypotheses (the facts are
  proved in the paper by `switching_gap` and checked by computation), and derive equations
  (Hx-three-parts) and (bridge-min3). -/

/-- (Hx-three-parts): if every shore other than A and its complement costs at least L + 2 and
    every shore at least L (doubled, L = 2λ ≥ 4), every 3-partition costs at least L + 4,
    i.e. λ₃ ≥ λ₂ + 2. -/
theorem three_parts_unique (lab : Nat → Nat) (hlab : ∀ y, y < n → lab y < 3)
    (hne : ∀ c, c < 3 → ∃ v, v < n ∧ lab v = c) (L : Nat) (A : Nat → Bool)
    (hmin : ∀ X : Nat → Bool, (∃ x, x < n ∧ X x = true) → (∃ y, y < n ∧ X y = false) →
      L ≤ q n wt X)
    (huniq : ∀ X : Nat → Bool, (∃ x, x < n ∧ X x = true) → (∃ y, y < n ∧ X y = false) →
      (∃ x, x < n ∧ X x ≠ A x) → (∃ y, y < n ∧ X y = A y) → L + 2 ≤ q n wt X)
    (hL : 4 ≤ L) : L + 4 ≤ cost n wt lab := by
  have hs := shore_sum n wt 3 lab hlab
  simp only [List.range, List.range.loop, lsum] at hs
  -- each part is a proper shore
  have proper : ∀ c, c < 3 → (∃ x, x < n ∧ part lab c x = true) ∧ (∃ y, y < n ∧ part lab c y = false) := by
    intro c hc
    obtain ⟨v, hv, hvc⟩ := hne c hc
    obtain ⟨w, hw, hwc⟩ := hne ((c + 1) % 3) (by omega)
    refine ⟨⟨v, hv, by simp [part, hvc]⟩, ⟨w, hw, by simp [part, hwc]; omega⟩⟩
  -- a part is special if it equals A or its complement
  let special := fun c => (∀ x, x < n → part lab c x = A x) ∨ (∀ x, x < n → part lab c x = !A x)
  have bound : ∀ c, c < 3 → L ≤ q n wt (part lab c) ∧ (special c ∨ L + 2 ≤ q n wt (part lab c)) := by
    intro c hc
    obtain ⟨h1, h2⟩ := proper c hc
    refine ⟨hmin _ h1 h2, ?_⟩
    by_cases hA : ∀ x, x < n → part lab c x = A x
    · exact Or.inl (Or.inl hA)
    · by_cases hB : ∀ x, x < n → part lab c x = !A x
      · exact Or.inl (Or.inr hB)
      · right
        apply huniq _ h1 h2
        · apply Classical.byContradiction
          intro hc'
          exact hA (fun x hx => by
            apply Classical.byContradiction; intro hne'; exact hc' ⟨x, hx, hne'⟩)
        · apply Classical.byContradiction
          intro hc'
          exact hB (fun x hx => by
            apply Classical.byContradiction; intro hne'
            apply hc'; refine ⟨x, hx, ?_⟩
            cases h : part lab c x <;> cases h' : A x <;> simp_all)
  -- two different parts cannot both be special
  have notboth : ∀ c c', c < 3 → c' < 3 → c ≠ c' → special c → special c' → False := by
    intro c c' hc hc' hcc' h1 h2
    obtain ⟨v, hv, hvc⟩ := hne c hc
    obtain ⟨c'', hc''⟩ : ∃ c'', c'' < 3 ∧ c'' ≠ c ∧ c'' ≠ c' := ⟨3 - c - c', by omega⟩
    obtain ⟨w, hw, hwc⟩ := hne c'' hc''.1
    have pv : part lab c v = true := by simp [part, hvc]
    have pv' : part lab c' v = false := by simp [part, hvc]; omega
    have pw : part lab c w = false := by simp [part, hwc]; omega
    have pw' : part lab c' w = false := by simp [part, hwc]; omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · have := h1 v hv; have := h2 v hv; simp_all
    · have := h1 w hw; have := h2 w hw; simp_all
    · have := h1 w hw; have := h2 w hw; simp_all
    · have := h1 v hv; have := h2 v hv; simp_all
  obtain ⟨b0, s0⟩ := bound 0 (by omega)
  obtain ⟨b1, s1⟩ := bound 1 (by omega)
  obtain ⟨b2, s2⟩ := bound 2 (by omega)
  have n01 := notboth 0 1 (by omega) (by omega) (by omega)
  have n02 := notboth 0 2 (by omega) (by omega) (by omega)
  have n12 := notboth 1 2 (by omega) (by omega) (by omega)
  rcases s0 with s0 | s0 <;> rcases s1 with s1 | s1 <;> rcases s2 with s2 | s2
  all_goals first
    | exact absurd (n01 s0 s1) id
    | exact absurd (n02 s0 s2) id
    | exact absurd (n12 s1 s2) id
    | omega

/-- The bridge edge h–j. -/
def bridge (h j : Nat) : Nat → Nat → Nat := fun x y => ind ((x == h && y == j) || (x == j && y == h))

theorem cost_bridge (lab : Nat → Nat) (h j : Nat) (hh : h < n) (hj : j < n) (hhj : h ≠ j) :
    cost n (bridge h j) lab = 2 * ind (lab h != lab j) := by
  have hl := D_left n h hh (fun x y => ind (y == j) * ind (lab x != lab y))
  have hr := D_right n h hh (fun x y => ind (x == j) * ind (lab x != lab y))
  have p1 : lsum (List.range n) (fun y => ind (y == j) * ind (lab h != lab y)) = ind (lab h != lab j) :=
    pick (fun y => ind (lab h != lab y)) j n hj
  have p2 : lsum (List.range n) (fun x => ind (x == j) * ind (lab x != lab h)) = ind (lab j != lab h) :=
    pick (fun x => ind (lab x != lab h)) j n hj
  have hsplit : cost n (bridge h j) lab = D n (fun x y => ind (x == h) * (ind (y == j) * ind (lab x != lab y)))
      + D n (fun x y => ind (y == h) * (ind (x == j) * ind (lab x != lab y))) := by
    unfold cost bridge
    rw [← D_add]
    apply D_congr
    intro x y _ _
    have hx := beq_excl x h j hhj
    have hy := beq_excl y h j hhj
    revert hx hy
    cases (x == h) <;> cases (x == j) <;> cases (y == h) <;> cases (y == j) <;> simp [ind] <;> omega
  rw [hsplit, hl, hr, p1, p2]
  have : ind (lab j != lab h) = ind (lab h != lab j) := by
    by_cases e : lab h = lab j
    · rw [e]
    · have e' : lab j ≠ lab h := fun z => e z.symm
      simp [ind, e, e']
  omega

/-- (bridge-min3): G = H ∪ J ∪ {hj}. If H and J have (doubled) minimum cuts 2λ_H, 2λ_J ≥ 2,
    and every 3-partition using all three labels on H (resp. J) costs at least 2(1 + min) there,
    then every 3-partition of G costs at least 2(1 + min(λ_H, λ_J)). -/
theorem bridge_lower (VH : Nat → Bool) (wH wJ : Nat → Nat → Nat) (h j : Nat)
    (hh : h < n) (hj : j < n) (hVh : VH h = true) (hVj : VH j = false)
    (lamH lamJ : Nat) (hH1 : 1 ≤ lamH)
    (hH2 : ∀ X : Nat → Bool, (∃ x, x < n ∧ VH x = true ∧ X x = true) →
      (∃ y, y < n ∧ VH y = true ∧ X y = false) → 2 * lamH ≤ q n wH X)
    (hJ2 : ∀ X : Nat → Bool, (∃ x, x < n ∧ VH x = false ∧ X x = true) →
      (∃ y, y < n ∧ VH y = false ∧ X y = false) → 2 * lamJ ≤ q n wJ X)
    (hH3 : ∀ lab : Nat → Nat, (∀ c, c < 3 → ∃ x, x < n ∧ VH x = true ∧ lab x = c) →
      2 * (1 + min lamH lamJ) ≤ cost n wH lab)
    (hJ3 : ∀ lab : Nat → Nat, (∀ c, c < 3 → ∃ x, x < n ∧ VH x = false ∧ lab x = c) →
      2 * (1 + min lamH lamJ) ≤ cost n wJ lab)
    (lab : Nat → Nat) (hne : ∀ c, c < 3 → ∃ v, v < n ∧ lab v = c) :
    2 * (1 + min lamH lamJ) ≤ cost n (fun x y => wH x y + wJ x y + bridge h j x y) lab := by
  have hhj : h ≠ j := by intro e; subst e; simp_all
  have hdec : cost n (fun x y => wH x y + wJ x y + bridge h j x y) lab
      = cost n wH lab + cost n wJ lab + cost n (bridge h j) lab := by
    unfold cost
    rw [← D_add, ← D_add]
    apply D_congr
    intro x y _ _
    simp only [Nat.mul_add]
  rw [hdec, cost_bridge n lab h j hh hj hhj]
  -- a split of H (resp. J) costs at least 2λ_H (resp. 2λ_J)
  have splitH : (∃ x y, x < n ∧ y < n ∧ VH x = true ∧ VH y = true ∧ lab x ≠ lab y) →
      2 * lamH ≤ cost n wH lab := by
    rintro ⟨x, y, hx, hy, hVx, hVy, hxy⟩
    have := shore_le_cost n wH lab (lab x)
    have := hH2 (part lab (lab x)) ⟨x, hx, hVx, by simp [part]⟩ ⟨y, hy, hVy, by simp [part]; omega⟩
    omega
  have splitJ : (∃ x y, x < n ∧ y < n ∧ VH x = false ∧ VH y = false ∧ lab x ≠ lab y) →
      2 * lamJ ≤ cost n wJ lab := by
    rintro ⟨x, y, hx, hy, hVx, hVy, hxy⟩
    have := shore_le_cost n wJ lab (lab x)
    have := hJ2 (part lab (lab x)) ⟨x, hx, hVx, by simp [part]⟩ ⟨y, hy, hVy, by simp [part]; omega⟩
    omega
  have hmin1 : min lamH lamJ ≤ lamH := Nat.min_le_left _ _
  have hmin2 : min lamH lamJ ≤ lamJ := Nat.min_le_right _ _
  by_cases sH : ∃ x y, x < n ∧ y < n ∧ VH x = true ∧ VH y = true ∧ lab x ≠ lab y
  · have cH := splitH sH
    by_cases sJ : ∃ x y, x < n ∧ y < n ∧ VH x = false ∧ VH y = false ∧ lab x ≠ lab y
    · have := splitJ sJ; omega
    · -- J is monochromatic
      have monoJ : ∀ x, x < n → VH x = false → lab x = lab j := by
        intro x hx hVx
        apply Classical.byContradiction
        intro hne'
        exact sJ ⟨x, j, hx, hj, hVx, hVj, hne'⟩
      by_cases all3 : ∀ c, c < 3 → ∃ x, x < n ∧ VH x = true ∧ lab x = c
      · have := hH3 lab all3; omega
      · -- some label c is missing on H; it occurs on J, so lab j = c ≠ lab h
        have : ∃ c, c < 3 ∧ ∀ x, x < n → VH x = true → lab x ≠ c := by
          apply Classical.byContradiction
          intro hc
          apply all3
          intro c hc3
          apply Classical.byContradiction
          intro hnone
          apply hc
          refine ⟨c, hc3, fun x hx hVx hxc => hnone ⟨x, hx, hVx, hxc⟩⟩
        obtain ⟨c, hc3, hmiss⟩ := this
        obtain ⟨v, hv, hvc⟩ := hne c hc3
        have hVv : VH v = false := by
          cases e : VH v
          · rfl
          · exact absurd hvc (hmiss v hv e)
        have hjc : lab j = c := by rw [← monoJ v hv hVv, hvc]
        have hhc : lab h ≠ c := hmiss h hh hVh
        have : ind (lab h != lab j) = 1 := by
          have : lab h ≠ lab j := by omega
          simp [ind, this]
        omega
  · have monoH : ∀ x, x < n → VH x = true → lab x = lab h := by
      intro x hx hVx
      apply Classical.byContradiction
      intro hne'
      exact sH ⟨x, h, hx, hh, hVx, hVh, hne'⟩
    by_cases sJ : ∃ x y, x < n ∧ y < n ∧ VH x = false ∧ VH y = false ∧ lab x ≠ lab y
    · have cJ := splitJ sJ
      by_cases all3 : ∀ c, c < 3 → ∃ x, x < n ∧ VH x = false ∧ lab x = c
      · have := hJ3 lab all3; omega
      · have : ∃ c, c < 3 ∧ ∀ x, x < n → VH x = false → lab x ≠ c := by
          apply Classical.byContradiction
          intro hc
          apply all3
          intro c hc3
          apply Classical.byContradiction
          intro hnone
          apply hc
          refine ⟨c, hc3, fun x hx hVx hxc => hnone ⟨x, hx, hVx, hxc⟩⟩
        obtain ⟨c, hc3, hmiss⟩ := this
        obtain ⟨v, hv, hvc⟩ := hne c hc3
        have hVv : VH v = true := by
          cases e : VH v
          · exact absurd hvc (hmiss v hv e)
          · rfl
        have hhc : lab h = c := by rw [← monoH v hv hVv, hvc]
        have hjc : lab j ≠ c := hmiss j hj hVj
        have : ind (lab h != lab j) = 1 := by
          have : lab h ≠ lab j := by omega
          simp [ind, this]
        omega
    · exfalso
      have monoJ : ∀ x, x < n → VH x = false → lab x = lab j := by
        intro x hx hVx
        apply Classical.byContradiction
        intro hne'
        exact sJ ⟨x, j, hx, hj, hVx, hVj, hne'⟩
      have : ∃ c, c < 3 ∧ c ≠ lab h ∧ c ≠ lab j := by
        rcases (by omega : (0 ≠ lab h ∧ 0 ≠ lab j) ∨ (1 ≠ lab h ∧ 1 ≠ lab j) ∨
          (2 ≠ lab h ∧ 2 ≠ lab j)) with e | e | e
        · exact ⟨0, by omega, e⟩
        · exact ⟨1, by omega, e⟩
        · exact ⟨2, by omega, e⟩
      obtain ⟨c, hc3, h1, h2⟩ := this
      obtain ⟨v, hv, hvc⟩ := hne c hc3
      cases e : VH v
      · have := monoJ v hv e; omega
      · have := monoH v hv e; omega

/-- Upper bound in (bridge-min3), H side: splitting H along a shore X and keeping J whole costs
    q_H(X) + 1 (doubled: q_H(X) + 2). -/
theorem bridge_upper_H (VH : Nat → Bool) (wH wJ : Nat → Nat → Nat) (h j : Nat)
    (hh : h < n) (hj : j < n) (hVh : VH h = true) (hVj : VH j = false)
    (hwH : ∀ x y, wH x y ≠ 0 → VH x = true ∧ VH y = true)
    (hwJ : ∀ x y, wJ x y ≠ 0 → VH x = false ∧ VH y = false) (X : Nat → Bool) :
    cost n (fun x y => wH x y + wJ x y + bridge h j x y)
        (fun x => if VH x then (if X x then 0 else 1) else 2) = q n wH X + 2 := by
  have hhj : h ≠ j := by intro e; subst e; simp_all
  let lab := fun x => if VH x then (if X x then 0 else 1) else 2
  have hdec : cost n (fun x y => wH x y + wJ x y + bridge h j x y) lab
      = cost n wH lab + cost n wJ lab + cost n (bridge h j) lab := by
    unfold cost; rw [← D_add, ← D_add]; apply D_congr; intro x y _ _; simp only [Nat.mul_add]
  have c1 : cost n wH lab = q n wH X := by
    unfold cost q; apply D_congr; intro x y _ _
    by_cases hw : wH x y = 0
    · simp [hw]
    · obtain ⟨hx, hy⟩ := hwH x y hw
      simp only [lab, hx, hy, ite_true]
      cases X x <;> cases X y <;> simp [ind]
  have c2 : cost n wJ lab = 0 := by
    unfold cost
    rw [D_congr n _ (fun _ _ => 0) (fun x y _ _ => by
      by_cases hw : wJ x y = 0
      · simp [hw]
      · obtain ⟨hx, hy⟩ := hwJ x y hw
        simp [lab, hx, hy, ind]), D_zero]
  have c3 : cost n (bridge h j) lab = 2 := by
    rw [cost_bridge n lab h j hh hj hhj]
    have : lab h ≠ lab j := by
      simp only [lab, hVh, hVj, ite_true]; split <;> simp
    simp [ind, this]
  show cost n _ lab = _
  omega

/-- Upper bound in (bridge-min3), J side. -/
theorem bridge_upper_J (VH : Nat → Bool) (wH wJ : Nat → Nat → Nat) (h j : Nat)
    (hh : h < n) (hj : j < n) (hVh : VH h = true) (hVj : VH j = false)
    (hwH : ∀ x y, wH x y ≠ 0 → VH x = true ∧ VH y = true)
    (hwJ : ∀ x y, wJ x y ≠ 0 → VH x = false ∧ VH y = false) (Y : Nat → Bool) :
    cost n (fun x y => wH x y + wJ x y + bridge h j x y)
        (fun x => if VH x then 0 else (if Y x then 1 else 2)) = q n wJ Y + 2 := by
  have hhj : h ≠ j := by intro e; subst e; simp_all
  let lab := fun x => if VH x then 0 else (if Y x then 1 else 2)
  have hdec : cost n (fun x y => wH x y + wJ x y + bridge h j x y) lab
      = cost n wH lab + cost n wJ lab + cost n (bridge h j) lab := by
    unfold cost; rw [← D_add, ← D_add]; apply D_congr; intro x y _ _; simp only [Nat.mul_add]
  have c1 : cost n wJ lab = q n wJ Y := by
    unfold cost q; apply D_congr; intro x y _ _
    by_cases hw : wJ x y = 0
    · simp [hw]
    · obtain ⟨hx, hy⟩ := hwJ x y hw
      simp only [lab, hx, hy]
      cases Y x <;> cases Y y <;> simp [ind]
  have c2 : cost n wH lab = 0 := by
    unfold cost
    rw [D_congr n _ (fun _ _ => 0) (fun x y _ _ => by
      by_cases hw : wH x y = 0
      · simp [hw]
      · obtain ⟨hx, hy⟩ := hwH x y hw
        simp [lab, hx, hy, ind]), D_zero]
  have c3 : cost n (bridge h j) lab = 2 := by
    rw [cost_bridge n lab h j hh hj hhj]
    have : lab h ≠ lab j := by
      simp only [lab, hVh, hVj, ite_true, Bool.false_eq_true, ite_false]
      cases Y j <;> simp
    simp [ind, this]
  show cost n _ lab = _
  omega

end Cover


end MinKCut
