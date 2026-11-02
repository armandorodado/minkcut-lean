import MinKCut.Cover
/-! # Part H: the switching graphs H_x of Theorem 20 -/

namespace MinKCut

/-! ## Part H: the switching graphs H_x of Theorem 20

  Vertices are 0, ..., 4t-1, in four blocks of size t: a⁰_i = i, a¹_j = t + j, b⁰_j = 2t + j,
  b¹_i = 3t + i. H₀ is the disjoint union of the cliques on A = blocks 0,1 and B = blocks 2,3.
  For every marked coordinate (i,j) (x i j = true) the switch removes a⁰_i a¹_j and b⁰_j b¹_i and
  adds a⁰_i b⁰_j and a¹_j b¹_i. We prove, for every t ≥ 1 and every x with 4|x| ≤ t:
  the graph is simple, q(A) = 2|x| (doubled: 4|x|), every other proper shore except B costs at
  least 2|x| + 1 (doubled: 4|x| + 2), and hence λ₃(H_x) ≥ λ₂(H_x) + 2 (equation (Hx-three-parts)).
-/

section Switching

theorem lsum_range_add (a : Nat) (f : Nat → Nat) : ∀ b,
    lsum (List.range (a + b)) f = lsum (List.range a) f + lsum (List.range b) (fun i => f (a + i)) := by
  intro b
  induction b with
  | zero => simp [lsum]
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, lsum_append, ih, List.range_succ, lsum_append]
    simp only [lsum]
    omega

theorem lsum_blocks (t : Nat) (g : Nat → Nat) : ∀ m,
    lsum (List.range (t * m)) g = lsum (List.range m) (fun c => lsum (List.range t) (fun i => g (t * c + i))) := by
  intro m
  induction m with
  | zero => simp [lsum]
  | succ m ih =>
    rw [Nat.mul_succ, lsum_range_add, ih, List.range_succ, lsum_append]
    simp only [lsum]
    omega

def blk (t v : Nat) : Nat := v / t
def idx (t v : Nat) : Nat := v % t

theorem blk_eq (t c i : Nat) (ht : 0 < t) (hi : i < t) : blk t (t * c + i) = c := by
  unfold blk; rw [Nat.mul_add_div ht, Nat.div_eq_of_lt hi]; rfl

theorem idx_eq (t c i : Nat) (hi : i < t) : idx t (t * c + i) = i := by
  unfold idx; rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hi

def remB (t : Nat) (x : Nat → Nat → Bool) (u v : Nat) : Bool :=
  (blk t u == 0 && blk t v == 1 && x (idx t u) (idx t v)) ||
  (blk t u == 1 && blk t v == 0 && x (idx t v) (idx t u)) ||
  (blk t u == 2 && blk t v == 3 && x (idx t v) (idx t u)) ||
  (blk t u == 3 && blk t v == 2 && x (idx t u) (idx t v))

def addB (t : Nat) (x : Nat → Nat → Bool) (u v : Nat) : Bool :=
  (blk t u == 0 && blk t v == 2 && x (idx t u) (idx t v)) ||
  (blk t u == 2 && blk t v == 0 && x (idx t v) (idx t u)) ||
  (blk t u == 1 && blk t v == 3 && x (idx t v) (idx t u)) ||
  (blk t u == 3 && blk t v == 1 && x (idx t u) (idx t v))

/-- The half A (blocks 0 and 1). -/
def halfA (t v : Nat) : Bool := decide (blk t v < 2)

/-- H₀: two disjoint cliques on A and B. -/
def w0 (t : Nat) (u v : Nat) : Nat := ind (u != v && (halfA t u == halfA t v))

/-- H_x. -/
def wx (t : Nat) (x : Nat → Nat → Bool) (u v : Nat) : Nat :=
  ind (u != v && (halfA t u == halfA t v) && !remB t x u v) + ind (addB t x u v)

/-- |x| = number of marked coordinates. -/
def weight (t : Nat) (x : Nat → Nat → Bool) : Nat :=
  lsum (List.range t) (fun i => lsum (List.range t) (fun j => ind (x i j)))

theorem D_blocks (t : Nat) (f : Nat → Nat → Nat) :
    D (t * 4) f = lsum (List.range 4) (fun c => lsum (List.range t) (fun i =>
      lsum (List.range 4) (fun c' => lsum (List.range t) (fun j => f (t * c + i) (t * c' + j))))) := by
  unfold D
  rw [lsum_blocks t _ 4]
  apply lsum_congr; intro c _
  apply lsum_congr; intro i _
  exact lsum_blocks t _ 4

theorem addB_blk (t c c' i j : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (hi : i < t) (hj : j < t) :
    addB t x (t * c + i) (t * c' + j) =
      ((c == 0 && c' == 2 && x i j) || (c == 2 && c' == 0 && x j i) ||
       (c == 1 && c' == 3 && x j i) || (c == 3 && c' == 1 && x i j)) := by
  simp only [addB, blk_eq t c i ht hi, blk_eq t c' j ht hj, idx_eq t c i hi, idx_eq t c' j hj]

theorem remB_blk (t c c' i j : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (hi : i < t) (hj : j < t) :
    remB t x (t * c + i) (t * c' + j) =
      ((c == 0 && c' == 1 && x i j) || (c == 1 && c' == 0 && x j i) ||
       (c == 2 && c' == 3 && x j i) || (c == 3 && c' == 2 && x i j)) := by
  simp only [remB, blk_eq t c i ht hi, blk_eq t c' j ht hj, idx_eq t c i hi, idx_eq t c' j hj]

theorem range4 (f : Nat → Nat) : lsum (List.range 4) f = f 0 + f 1 + f 2 + f 3 := by
  simp [List.range, List.range.loop, lsum]; omega

theorem ind_false_fun (t : Nat) : lsum (List.range t) (fun _ => ind false) = 0 := lsum_zero _

theorem zz (t : Nat) : lsum (List.range t) (fun _ => lsum (List.range t) (fun _ => ind false)) = 0 := by
  have h : ∀ i, i ∈ List.range t → lsum (List.range t) (fun _ => ind false) = 0 :=
    fun _ _ => ind_false_fun t
  rw [lsum_congr _ _ (fun _ => 0) h, lsum_zero]

theorem weight_swap (t : Nat) (x : Nat → Nat → Bool) :
    lsum (List.range t) (fun i => lsum (List.range t) (fun j => ind (x j i))) = weight t x := by
  unfold weight; rw [lsum_swap]

/-- The added edges, counted over ordered pairs, number 4|x|. -/
theorem D_addB (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) :
    D (t * 4) (fun u v => ind (addB t x u v)) = 4 * weight t x := by
  rw [D_blocks]
  have hrw : ∀ c c', lsum (List.range t) (fun i => lsum (List.range t) (fun j => ind (addB t x (t * c + i) (t * c' + j))))
      = lsum (List.range t) (fun i => lsum (List.range t) (fun j =>
          ind ((c == 0 && c' == 2 && x i j) || (c == 2 && c' == 0 && x j i) ||
               (c == 1 && c' == 3 && x j i) || (c == 3 && c' == 1 && x i j)))) := by
    intro c c'
    apply lsum_congr; intro i hi
    apply lsum_congr; intro j hj
    rw [addB_blk t c c' i j x ht (List.mem_range.mp hi) (List.mem_range.mp hj)]
  rw [lsum_congr _ _ (fun c => lsum (List.range 4) (fun c' => lsum (List.range t) (fun i =>
      lsum (List.range t) (fun j => ind (addB t x (t * c + i) (t * c' + j)))))) (fun c _ => lsum_swap _ _ _)]
  simp only [hrw, range4]
  simp
  simp only [zz]
  have hw := weight_swap t x
  unfold weight at hw ⊢
  omega

theorem D_remB (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) :
    D (t * 4) (fun u v => ind (remB t x u v)) = 4 * weight t x := by
  rw [D_blocks]
  have hrw : ∀ c c', lsum (List.range t) (fun i => lsum (List.range t) (fun j => ind (remB t x (t * c + i) (t * c' + j))))
      = lsum (List.range t) (fun i => lsum (List.range t) (fun j =>
          ind ((c == 0 && c' == 1 && x i j) || (c == 1 && c' == 0 && x j i) ||
               (c == 2 && c' == 3 && x j i) || (c == 3 && c' == 2 && x i j)))) := by
    intro c c'
    apply lsum_congr; intro i hi
    apply lsum_congr; intro j hj
    rw [remB_blk t c c' i j x ht (List.mem_range.mp hi) (List.mem_range.mp hj)]
  rw [lsum_congr _ _ (fun c => lsum (List.range 4) (fun c' => lsum (List.range t) (fun i =>
      lsum (List.range t) (fun j => ind (remB t x (t * c + i) (t * c' + j)))))) (fun c _ => lsum_swap _ _ _)]
  simp only [hrw, range4]
  simp
  simp only [zz]
  have hw := weight_swap t x
  unfold weight at hw ⊢
  omega

/-- Added edges join the two halves. -/
theorem addB_cross (t : Nat) (x : Nat → Nat → Bool) (u v : Nat) (h : addB t x u v = true) :
    halfA t u ≠ halfA t v := by
  unfold addB at h
  unfold halfA
  generalize blk t u = a at *
  generalize blk t v = b at *
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  intro e
  simp only [decide_eq_decide] at e
  omega

theorem addB_irrefl (t : Nat) (x : Nat → Nat → Bool) (u : Nat) : addB t x u u = false := by
  cases h : addB t x u u
  · rfl
  · exact absurd rfl (addB_cross t x u u h)

/-- H_x is a simple graph. -/
theorem wx_simple (t : Nat) (x : Nat → Nat → Bool) :
    (∀ u v, wx t x u v = wx t x v u) ∧ (∀ u, wx t x u u = 0) ∧ (∀ u v, wx t x u v ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v
    have hr : remB t x u v = remB t x v u := by
      unfold remB
      generalize blk t u = a
      generalize blk t v = b
      generalize x (idx t u) (idx t v) = p
      generalize x (idx t v) (idx t u) = p'
      rw [Bool.eq_iff_iff]
      cases p <;> cases p' <;> simp <;> omega
    have ha : addB t x u v = addB t x v u := by
      unfold addB
      generalize blk t u = a
      generalize blk t v = b
      generalize x (idx t u) (idx t v) = p
      generalize x (idx t v) (idx t u) = p'
      rw [Bool.eq_iff_iff]
      cases p <;> cases p' <;> simp <;> omega
    have hb : (u != v) = (v != u) := by
      by_cases e : u = v
      · subst e; rfl
      · have h1 : (u != v) = true := by simpa using e
        have h2 : (v != u) = true := by simpa using (fun z => e z.symm)
        rw [h1, h2]
    have hh : (halfA t u == halfA t v) = (halfA t v == halfA t u) := by
      cases halfA t u <;> cases halfA t v <;> rfl
    unfold wx; rw [hr, ha, hb, hh]
  · intro u
    unfold wx; simp [addB_irrefl, ind]
  · intro u v
    unfold wx
    cases h : addB t x u v
    · cases (u != v && (halfA t u == halfA t v) && !remB t x u v) <;> simp [ind]
    · have := addB_cross t x u v h
      have e : (halfA t u == halfA t v) = false := by
        cases hu : halfA t u <;> cases hv : halfA t v <;> simp_all
      simp [e, ind]

/-- The cut of A in H_x consists exactly of the added edges: q(A) = 2|x| (doubled: 4|x|). -/
theorem q_halfA (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) :
    q (t * 4) (wx t x) (halfA t) = 4 * weight t x := by
  rw [← D_addB t x ht]
  unfold q
  apply D_congr
  intro u v _ _
  unfold wx
  cases h : addB t x u v
  · cases e : (halfA t u != halfA t v)
    · simp [ind]
    · have : (halfA t u == halfA t v) = false := by
        cases hu : halfA t u <;> cases hv : halfA t v <;> simp_all
      simp [this, ind]
  · have hc := addB_cross t x u v h
    have e1 : (halfA t u != halfA t v) = true := by simp [hc]
    have e2 : (halfA t u == halfA t v) = false := by simp [hc]
    simp [e1, e2, ind]

theorem q_compl (n : Nat) (wt : Nat → Nat → Nat) (X : Nat → Bool) :
    q n wt (fun u => !X u) = q n wt X := by
  unfold q; apply D_congr; intro u v _ _
  dsimp only
  cases h1 : X u <;> cases h2 : X v <;> simp [h1, h2]

/-- Every shore loses at most the removed edges: q_x(S) + 4|x| ≥ q_0(S). -/
theorem q_switch (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (S : Nat → Bool) :
    q (t * 4) (w0 t) S ≤ q (t * 4) (wx t x) S + 4 * weight t x := by
  rw [← D_remB t x ht]
  unfold q
  rw [← D_add]
  apply D_mono
  intro u v _ _
  unfold w0 wx
  generalize (u != v && (halfA t u == halfA t v)) = e
  generalize remB t x u v = r
  generalize addB t x u v = a
  generalize (S u != S v) = s
  cases e <;> cases r <;> cases a <;> cases s <;> simp [ind]

/-- Shores that split a clique: q(X) ≥ 2(|W| - 1) (doubled). -/
theorem clique_shore (n : Nat) (wt : Nat → Nat → Nat) (W X : Nat → Bool)
    (hW : ∀ x y, x < n → y < n → W x = true → W y = true → x ≠ y → 1 ≤ wt x y)
    (x0 y0 : Nat) (hx0 : x0 < n) (hy0 : y0 < n) (hWx : W x0 = true) (hWy : W y0 = true)
    (hX0 : X x0 = true) (hY0 : X y0 = false) :
    2 * (cnt n W - 1) ≤ q n wt X := by
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
    have e : ind (W x0 && X x0) = 1 := by simp [hWx, hX0, ind]
    dsimp only at this; rw [e] at this; exact this
  have hb : 1 ≤ cnt n (fun y => W y && !X y) := by
    have := lsum_ge_term (fun y => ind (W y && !X y)) y0 n hy0
    have e : ind (W y0 && !X y0) = 1 := by simp [hWy, hY0, ind]
    dsimp only at this; rw [e] at this; exact this
  have k2 := kn_two_parts _ _ ha hb
  have e1 : cnt n (fun y => W y && !X y) * cnt n (fun y => W y && X y)
      = cnt n (fun y => W y && X y) * cnt n (fun y => W y && !X y) := Nat.mul_comm _ _
  omega

theorem halfA_blk (t c i : Nat) (ht : 0 < t) (hi : i < t) : halfA t (t * c + i) = decide (c < 2) := by
  unfold halfA; rw [blk_eq t c i ht hi]

/-- Each half has 2t vertices. -/
theorem cnt_halves (t : Nat) (ht : 0 < t) :
    cnt (t * 4) (halfA t) = 2 * t ∧ cnt (t * 4) (fun v => !halfA t v) = 2 * t := by
  constructor
  · unfold cnt
    rw [lsum_blocks t _ 4]
    rw [lsum_congr _ _ (fun c => lsum (List.range t) (fun _ => ind (decide (c < 2)))) (fun c _ => by
      apply lsum_congr; intro i hi; rw [halfA_blk t c i ht (List.mem_range.mp hi)])]
    simp only [range4]
    simp [ind, lsum_ones, lsum_zero]
    omega
  · unfold cnt
    rw [lsum_blocks t _ 4]
    rw [lsum_congr _ _ (fun c => lsum (List.range t) (fun _ => ind (!decide (c < 2)))) (fun c _ => by
      apply lsum_congr; intro i hi; dsimp only; rw [halfA_blk t c i ht (List.mem_range.mp hi)])]
    simp only [range4]
    simp [ind, lsum_ones, lsum_zero]
    omega

/-- Theorem 20, minimum cuts of H_x: if 4|x| ≤ t, every proper shore other than A and B costs at
    least 2|x| + 1 (doubled: 4|x| + 2), while A and B cost exactly 2|x|. -/
theorem Hx_cuts (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (hw : 4 * weight t x ≤ t)
    (S : Nat → Bool) (hS1 : ∃ u, u < t * 4 ∧ S u = true) (hS2 : ∃ v, v < t * 4 ∧ S v = false)
    (hA : ∃ u, u < t * 4 ∧ S u ≠ halfA t u) (hB : ∃ v, v < t * 4 ∧ S v = halfA t v) :
    4 * weight t x + 2 ≤ q (t * 4) (wx t x) S := by
  have hsw := q_switch t x ht S
  obtain ⟨cA, cB⟩ := cnt_halves t ht
  have hw0A : ∀ u v, u < t * 4 → v < t * 4 → halfA t u = true → halfA t v = true → u ≠ v →
      1 ≤ w0 t u v := by
    intro u v _ _ hu hv huv; simp [w0, hu, hv, huv, ind]
  have hw0B : ∀ u v, u < t * 4 → v < t * 4 → (!halfA t u) = true → (!halfA t v) = true → u ≠ v →
      1 ≤ w0 t u v := by
    intro u v _ _ hu hv huv
    simp only [Bool.not_eq_true'] at hu hv
    simp [w0, hu, hv, huv, ind]
  -- S splits A or splits B
  have split : (∃ u v, u < t * 4 ∧ v < t * 4 ∧ halfA t u = true ∧ halfA t v = true ∧ S u = true ∧ S v = false) ∨
      (∃ u v, u < t * 4 ∧ v < t * 4 ∧ halfA t u = false ∧ halfA t v = false ∧ S u = true ∧ S v = false) := by
    apply Classical.byContradiction
    intro hno
    have nA : ∀ u v, u < t * 4 → v < t * 4 → halfA t u = true → halfA t v = true → S u = S v := by
      intro u v hu hv h1 h2
      cases e1 : S u <;> cases e2 : S v
      · rfl
      · exact absurd (Or.inl ⟨v, u, hv, hu, h2, h1, e2, e1⟩) hno
      · exact absurd (Or.inl ⟨u, v, hu, hv, h1, h2, e1, e2⟩) hno
      · rfl
    have nB : ∀ u v, u < t * 4 → v < t * 4 → halfA t u = false → halfA t v = false → S u = S v := by
      intro u v hu hv h1 h2
      cases e1 : S u <;> cases e2 : S v
      · rfl
      · exact absurd (Or.inr ⟨v, u, hv, hu, h2, h1, e2, e1⟩) hno
      · exact absurd (Or.inr ⟨u, v, hu, hv, h1, h2, e1, e2⟩) hno
      · rfl
    obtain ⟨u1, hu1, hS1'⟩ := hS1
    obtain ⟨v1, hv1, hS2'⟩ := hS2
    obtain ⟨u2, hu2, hA'⟩ := hA
    obtain ⟨v2, hv2, hB'⟩ := hB
    cases ha1 : halfA t u1 <;> cases hb1 : halfA t v1
    · have := nB u1 v1 hu1 hv1 ha1 hb1; simp_all
    · -- u1 ∈ B, v1 ∈ A: S is the complement of A
      cases hc : halfA t v2
      · have := nB v2 u1 hv2 hu1 hc ha1; simp_all
      · have := nA v2 v1 hv2 hv1 hc hb1; simp_all
    · -- u1 ∈ A, v1 ∈ B: S = A
      cases hc : halfA t u2
      · have := nB u2 v1 hu2 hv1 hc hb1; simp_all
      · have := nA u2 u1 hu2 hu1 hc ha1; simp_all
    · have := nA u1 v1 hu1 hv1 ha1 hb1; simp_all
  rcases split with ⟨u, v, hu, hv, hau, hav, hsu, hsv⟩ | ⟨u, v, hu, hv, hau, hav, hsu, hsv⟩
  · have := clique_shore (t * 4) (w0 t) (halfA t) S hw0A u v hu hv hau hav hsu hsv
    omega
  · have := clique_shore (t * 4) (w0 t) (fun z => !halfA t z) S hw0B u v hu hv
      (by simp [hau]) (by simp [hav]) hsu hsv
    omega

/-- Equation (Hx-three-parts) for the actual graphs H_x: if 1 ≤ |x| and 4|x| ≤ t, every
    3-partition of H_x costs at least 2|x| + 2 = λ₂(H_x) + 2 (doubled: 4|x| + 4). -/
theorem Hx_three_parts (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (hw1 : 1 ≤ weight t x)
    (hw : 4 * weight t x ≤ t) (lab : Nat → Nat) (hlab : ∀ y, y < t * 4 → lab y < 3)
    (hne : ∀ c, c < 3 → ∃ v, v < t * 4 ∧ lab v = c) :
    4 * weight t x + 4 ≤ cost (t * 4) (wx t x) lab := by
  apply three_parts_unique (t * 4) (wx t x) lab hlab hne (4 * weight t x) (halfA t)
  · intro X h1 h2
    by_cases hA : ∃ u, u < t * 4 ∧ X u ≠ halfA t u
    · by_cases hB : ∃ v, v < t * 4 ∧ X v = halfA t v
      · have := Hx_cuts t x ht hw X h1 h2 hA hB; omega
      · -- X is the complement of A
        have : q (t * 4) (wx t x) X = q (t * 4) (wx t x) (fun u => !halfA t u) := by
          unfold q; apply D_congr; intro u v hu hv
          have e1 : X u = !halfA t u := by
            cases h : X u <;> cases h' : halfA t u
            · exact absurd ⟨u, hu, by rw [h, h']⟩ hB
            · rfl
            · rfl
            · exact absurd ⟨u, hu, by rw [h, h']⟩ hB
          have e2 : X v = !halfA t v := by
            cases h : X v <;> cases h' : halfA t v
            · exact absurd ⟨v, hv, by rw [h, h']⟩ hB
            · rfl
            · rfl
            · exact absurd ⟨v, hv, by rw [h, h']⟩ hB
          rw [e1, e2]
        rw [this, q_compl, q_halfA t x ht]
        exact Nat.le_refl _
    · have : q (t * 4) (wx t x) X = q (t * 4) (wx t x) (halfA t) := by
        unfold q; apply D_congr; intro u v hu hv
        have e1 : X u = halfA t u := by
          apply Classical.byContradiction; intro h; exact hA ⟨u, hu, h⟩
        have e2 : X v = halfA t v := by
          apply Classical.byContradiction; intro h; exact hA ⟨v, hv, h⟩
        rw [e1, e2]
      rw [this, q_halfA t x ht]
      exact Nat.le_refl _
  · intro X h1 h2 hA hB
    exact Hx_cuts t x ht hw X h1 h2 hA hB
  · omega

/-- λ₂(H_x) = 2|x|, attained exactly by the shores A and B (doubled: 4|x|). -/
theorem Hx_mincut (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (hw : 4 * weight t x ≤ t) :
    q (t * 4) (wx t x) (halfA t) = 4 * weight t x ∧
    ∀ S : Nat → Bool, (∃ u, u < t * 4 ∧ S u = true) → (∃ v, v < t * 4 ∧ S v = false) →
      4 * weight t x ≤ q (t * 4) (wx t x) S ∧
      (q (t * 4) (wx t x) S = 4 * weight t x →
        (∀ u, u < t * 4 → S u = halfA t u) ∨ (∀ u, u < t * 4 → S u = !halfA t u)) := by
  refine ⟨q_halfA t x ht, ?_⟩
  intro S h1 h2
  by_cases hA : ∃ u, u < t * 4 ∧ S u ≠ halfA t u
  · by_cases hB : ∃ v, v < t * 4 ∧ S v = halfA t v
    · have := Hx_cuts t x ht hw S h1 h2 hA hB
      exact ⟨by omega, fun h => by omega⟩
    · have hc : ∀ u, u < t * 4 → S u = !halfA t u := by
        intro u hu
        cases h : S u <;> cases h' : halfA t u
        · exact absurd ⟨u, hu, by rw [h, h']⟩ hB
        · rfl
        · rfl
        · exact absurd ⟨u, hu, by rw [h, h']⟩ hB
      have : q (t * 4) (wx t x) S = q (t * 4) (wx t x) (fun u => !halfA t u) := by
        unfold q; apply D_congr; intro u v hu hv; rw [hc u hu, hc v hv]
      rw [this, q_compl, q_halfA t x ht]
      exact ⟨Nat.le_refl _, fun _ => Or.inr hc⟩
  · have hc : ∀ u, u < t * 4 → S u = halfA t u := by
      intro u hu
      apply Classical.byContradiction; intro h; exact hA ⟨u, hu, h⟩
    have : q (t * 4) (wx t x) S = q (t * 4) (wx t x) (halfA t) := by
      unfold q; apply D_congr; intro u v hu hv; rw [hc u hu, hc v hv]
    rw [this, q_halfA t x ht]
    exact ⟨Nat.le_refl _, fun _ => Or.inl hc⟩

theorem remB_base (t : Nat) (x : Nat → Nat → Bool) (u v : Nat) (h : remB t x u v = true) :
    (u != v && (halfA t u == halfA t v)) = true := by
  unfold remB at h
  have hne : u ≠ v := by
    intro e; subst e
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    omega
  have hh : halfA t u = halfA t v := by
    unfold halfA
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ((⟨⟨h1, h2⟩, _⟩ | ⟨⟨h1, h2⟩, _⟩) | ⟨⟨h1, h2⟩, _⟩) | ⟨⟨h1, h2⟩, _⟩ <;>
      rw [h1, h2] <;> rfl
  simp [hne, hh]

theorem vertex_split (t u : Nat) : u = t * blk t u + idx t u := by
  unfold blk idx; exact (Nat.div_add_mod u t).symm

theorem block_ne (t c c' i j : Nat) (ht : 0 < t) (hi : i < t) (hj : j < t) (hcc : c ≠ c') :
    t * c + i ≠ t * c' + j := by
  intro e
  have := blk_eq t c i ht hi
  rw [e, blk_eq t c' j ht hj] at this
  exact hcc this.symm

theorem row_block_self (t c i : Nat) (hi : i < t) :
    lsum (List.range t) (fun j => ind ((t * c + i) != (t * c + j))) + 1 = t := by
  have hp := pick (fun _ => 1) i t hi
  dsimp only at hp
  have hones := lsum_ones t
  have h : lsum (List.range t) (fun j => ind ((t * c + i) != (t * c + j)))
      + lsum (List.range t) (fun j => ind (j == i) * 1) = lsum (List.range t) (fun _ => 1) := by
    rw [← lsum_add]
    apply lsum_congr
    intro j _
    by_cases h : j = i
    · subst h; simp [ind]
    · have h1 : (t * c + i) ≠ (t * c + j) := by omega
      simp [h1, h, ind]
  omega

theorem row_block_other (t c c' i : Nat) (ht : 0 < t) (hi : i < t) (hcc : c ≠ c') :
    lsum (List.range t) (fun j => ind ((t * c + i) != (t * c' + j))) = t := by
  calc lsum (List.range t) (fun j => ind ((t * c + i) != (t * c' + j)))
      = lsum (List.range t) (fun _ => 1) := by
        apply lsum_congr
        intro j hj
        have := block_ne t c c' i j ht hi (List.mem_range.mp hj) hcc
        simp [this, ind]
    _ = t := lsum_ones t

/-- Every vertex of H_x has degree 2t - 1 (so the supplied degree sequence does not depend on x). -/
theorem Hx_regular (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (u : Nat) (hu : u < t * 4) :
    lsum (List.range (t * 4)) (fun v => wx t x u v) = 2 * t - 1 := by
  -- wx + rem = w0 + add, pointwise
  have hpt : ∀ v, wx t x u v + ind (remB t x u v) = w0 t u v + ind (addB t x u v) := by
    intro v
    unfold wx w0
    cases hr : remB t x u v
    · simp [ind]
    · have := remB_base t x u v hr
      simp [this, ind, Nat.add_comm]
  have hsum : lsum (List.range (t * 4)) (fun v => wx t x u v)
      + lsum (List.range (t * 4)) (fun v => ind (remB t x u v))
      = lsum (List.range (t * 4)) (fun v => w0 t u v)
      + lsum (List.range (t * 4)) (fun v => ind (addB t x u v)) := by
    rw [← lsum_add, ← lsum_add]; apply lsum_congr; intro v _; exact hpt v
  -- write u = t c + i
  have hsplit := vertex_split t u
  generalize hc : blk t u = c at hsplit
  generalize hi : idx t u = i at hsplit
  have hit : i < t := by rw [← hi]; exact Nat.mod_lt _ ht
  have hc4 : c < 4 := by
    have : t * c < t * 4 := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  subst hsplit
  -- the three row sums, block by block
  have hrem : lsum (List.range (t * 4)) (fun v => ind (remB t x (t * c + i) v))
      = lsum (List.range 4) (fun c' => lsum (List.range t) (fun j =>
          ind ((c == 0 && c' == 1 && x i j) || (c == 1 && c' == 0 && x j i) ||
               (c == 2 && c' == 3 && x j i) || (c == 3 && c' == 2 && x i j)))) := by
    rw [lsum_blocks t _ 4]
    apply lsum_congr; intro c' _; apply lsum_congr; intro j hj
    rw [remB_blk t c c' i j x ht hit (List.mem_range.mp hj)]
  have hadd : lsum (List.range (t * 4)) (fun v => ind (addB t x (t * c + i) v))
      = lsum (List.range 4) (fun c' => lsum (List.range t) (fun j =>
          ind ((c == 0 && c' == 2 && x i j) || (c == 2 && c' == 0 && x j i) ||
               (c == 1 && c' == 3 && x j i) || (c == 3 && c' == 1 && x i j)))) := by
    rw [lsum_blocks t _ 4]
    apply lsum_congr; intro c' _; apply lsum_congr; intro j hj
    rw [addB_blk t c c' i j x ht hit (List.mem_range.mp hj)]
  have hw0 : lsum (List.range (t * 4)) (fun v => w0 t (t * c + i) v)
      = lsum (List.range 4) (fun c' => lsum (List.range t) (fun j =>
          ind ((t * c + i) != (t * c' + j)) * ind (decide (c < 2) == decide (c' < 2)))) := by
    rw [lsum_blocks t _ 4]
    apply lsum_congr; intro c' _; apply lsum_congr; intro j hj
    unfold w0
    rw [halfA_blk t c i ht hit, halfA_blk t c' j ht (List.mem_range.mp hj)]
    cases ((t * c + i) != (t * c' + j)) <;> cases (decide (c < 2) == decide (c' < 2)) <;> simp [ind]
  rw [hrem, hadd, hw0] at hsum
  simp only [range4] at hsum
  have s0 := row_block_self t c i hit
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with h | h | h | h <;> subst h
  · have o1 := row_block_other t 0 1 i ht hit (by omega)
    simp at hsum s0 o1
    try simp only [ind_true, ind_false, Nat.mul_one, Nat.mul_zero, lsum_zero] at hsum
    try simp only [zz, lsum_zero, ind_false_fun] at hsum
    try simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    omega
  · have o0 := row_block_other t 1 0 i ht hit (by omega)
    simp at hsum s0 o0
    try simp only [ind_true, ind_false, Nat.mul_one, Nat.mul_zero, lsum_zero] at hsum
    try simp only [zz, lsum_zero, ind_false_fun] at hsum
    try simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    omega
  · have o3 := row_block_other t 2 3 i ht hit (by omega)
    simp at hsum s0 o3
    try simp only [ind_true, ind_false, Nat.mul_one, Nat.mul_zero, lsum_zero] at hsum
    try simp only [zz, lsum_zero, ind_false_fun] at hsum
    try simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    omega
  · have o2 := row_block_other t 3 2 i ht hit (by omega)
    simp at hsum s0 o2
    try simp only [ind_true, ind_false, Nat.mul_one, Nat.mul_zero, lsum_zero] at hsum
    try simp only [zz, lsum_zero, ind_false_fun] at hsum
    try simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]
    omega

end Switching


end MinKCut
