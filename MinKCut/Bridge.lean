import MinKCut.Truncation
/-! # Part R: Theorem 20 on the concrete graphs G_x (equation (bridge-min3) and the optima) -/

namespace MinKCut


/-! ## Part R: Theorem 20 on the concrete graphs G_x = H_x + K_m + bridge

  Vertices 0..4t-1 carry H_x, vertices 4t..4t+m-1 carry the clique J = K_m, and one bridge
  joins vertex 0 ∈ A to vertex 4t ∈ J. We prove equation (bridge-min3),
  λ₃(G_x) = 1 + min{λ₂(H_x), m - 1}, and the structure of the optima used in the proof. -/

def wHr (t : Nat) (x : Nat → Nat → Bool) (u v : Nat) : Nat := if u < t * 4 ∧ v < t * 4 then wx t x u v else 0
def wJk (t m : Nat) (u v : Nat) : Nat :=
  ind (decide (t * 4 ≤ u) && decide (u < t * 4 + m) && decide (t * 4 ≤ v) && decide (v < t * 4 + m) && u != v)
def Gx (t m : Nat) (x : Nat → Nat → Bool) (u v : Nat) : Nat := wHr t x u v + wJk t m u v + bridge 0 (t * 4) u v

theorem D_shift (N m : Nat) (f : Nat → Nat → Nat)
    (hf : ∀ u v, ¬ (N ≤ u ∧ u < N + m ∧ N ≤ v ∧ v < N + m) → f u v = 0) :
    D (N + m) f = D m (fun u v => f (N + u) (N + v)) := by
  unfold D
  rw [lsum_range_add N, lsum_congr (List.range N) _ (fun _ => 0) (fun u hu => by
    have hu := List.mem_range.mp hu
    rw [lsum_congr _ _ (fun _ => 0) (fun v _ => hf _ _ (by omega)), lsum_zero]), lsum_zero, Nat.zero_add]
  apply lsum_congr; intro i hi
  have hi := List.mem_range.mp hi
  rw [lsum_range_add N, lsum_congr (List.range N) _ (fun _ => 0) (fun v hv => hf _ _ (by
    have := List.mem_range.mp hv; omega)), lsum_zero, Nat.zero_add]

theorem wJk_shift (t m u v : Nat) (hu : u < m) (hv : v < m) : wJk t m (t * 4 + u) (t * 4 + v) = wK u v := by
  unfold wJk wK
  by_cases h : u = v
  · subst h; simp
  · have : t * 4 + u ≠ t * 4 + v := by omega
    have e1 : (t * 4 + u != t * 4 + v) = true := by simp [this]
    have e2 : (u != v) = true := by simp [h]
    simp only [show t * 4 ≤ t * 4 + u by omega, show t * 4 + u < t * 4 + m by omega,
      show t * 4 ≤ t * 4 + v by omega, show t * 4 + v < t * 4 + m by omega, decide_true, Bool.true_and, e1, e2]

theorem wJk_supp (t m u v : Nat) (h : ¬ (t * 4 ≤ u ∧ u < t * 4 + m ∧ t * 4 ≤ v ∧ v < t * 4 + m)) :
    wJk t m u v = 0 := by
  unfold wJk ind; split
  · rename_i hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; omega
  · rfl

theorem costJ (t m : Nat) (lab : Nat → Nat) :
    cost (t * 4 + m) (wJk t m) lab = cost m wK (fun u => lab (t * 4 + u)) := by
  unfold cost
  rw [D_shift (t * 4) m _ (fun u v h => by rw [wJk_supp t m u v h, Nat.mul_zero])]
  apply D_congr; intro u v hu hv; rw [wJk_shift t m u v hu hv]

theorem costH (t m : Nat) (x : Nat → Nat → Bool) (lab : Nat → Nat) :
    cost (t * 4 + m) (wHr t x) lab = cost (t * 4) (wx t x) lab := by
  unfold cost
  rw [D_restrict (t * 4) (t * 4 + m) (by omega) _ (fun u v h => by simp [wHr, h])]
  apply D_congr; intro u v hu hv; simp [wHr, hu, hv]

theorem cost_Gx (t m : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (hm : 1 ≤ m) (lab : Nat → Nat) :
    cost (t * 4 + m) (Gx t m x) lab = cost (t * 4) (wx t x) lab + cost m wK (fun u => lab (t * 4 + u)) +
      2 * ind (lab 0 != lab (t * 4)) := by
  unfold Gx
  rw [cost_add3, costH, costJ, cost_bridge (t * 4 + m) lab 0 (t * 4) (by omega) (by omega) (by omega)]

/-- A split of H costs at least λ₂(H) = 2|x| (doubled 4|x|). -/
theorem H_split (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (hw : 4 * weight t x ≤ t) (lab : Nat → Nat)
    (u v : Nat) (hu : u < t * 4) (hv : v < t * 4) (hne : lab u ≠ lab v) :
    4 * weight t x ≤ cost (t * 4) (wx t x) lab := by
  have h1 := shore_le_cost (t * 4) (wx t x) lab (lab u)
  have h2 := ((Hx_mincut t x ht hw).2 (part lab (lab u)) ⟨u, hu, by simp [part]⟩
    ⟨v, hv, by simp [part]; omega⟩).1
  omega

/-- A split of J = K_m costs at least m - 1 (doubled 2(m - 1)). -/
theorem J_split (m : Nat) (lab : Nat → Nat) (u v : Nat) (hu : u < m) (hv : v < m) (hne : lab u ≠ lab v) :
    2 * (m - 1) ≤ cost m wK lab := by
  have h1 := shore_le_cost m wK lab (lab u)
  rw [kn_cut] at h1
  have ha := cnt_pos m (part lab (lab u)) u hu (by simp [part])
  have hb := cnt_pos m (fun y => !part lab (lab u) y) v hv (by simp [part]; omega)
  have hc := cnt_compl m (part lab (lab u))
  have := kn_two_parts _ _ ha hb
  rw [Nat.mul_comm (cnt m fun y => !part lab (lab u) y)] at h1
  omega

theorem H_three (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (hw1 : 1 ≤ weight t x) (hw : 4 * weight t x ≤ t)
    (lab : Nat → Nat) (hlab : ∀ y, y < t * 4 → lab y < 3) (hne : ∀ c, c < 3 → ∃ v, v < t * 4 ∧ lab v = c) :
    4 * weight t x + 4 ≤ cost (t * 4) (wx t x) lab := Hx_three_parts t x ht hw1 hw lab hlab hne

theorem J_three (m : Nat) (lab : Nat → Nat) (hlab : ∀ y, y < m → lab y < 3)
    (hne : ∀ c, c < 3 → ∃ v, v < m ∧ lab v = c) : 2 * (2 * m - 3) ≤ cost m wK lab :=
  kn_lambda3 m lab hlab (fun c hc => by
    obtain ⟨v, hv, hl⟩ := hne c hc; exact cnt_pos m _ v hv (by simp [part, hl]))

section GxFacts
variable (t m : Nat) (x : Nat → Nat → Bool)

theorem Gx_monoH (lab : Nat → Nat) (ht : 0 < t) (h : ¬ (∃ u v, u < t * 4 ∧ v < t * 4 ∧ lab u ≠ lab v)) :
    ∀ u, u < t * 4 → lab u = lab 0 := by
  intro u hu; apply Classical.byContradiction; intro hne; exact h ⟨u, 0, hu, by omega, hne⟩

theorem Gx_monoJ (lab : Nat → Nat) (h : ¬ (∃ u v, u < m ∧ v < m ∧ lab (t * 4 + u) ≠ lab (t * 4 + v))) :
    ∀ u, t * 4 ≤ u → u < t * 4 + m → lab u = lab (t * 4) := by
  intro u h1 h2; apply Classical.byContradiction; intro hne
  exact h ⟨u - t * 4, 0, by omega, by omega, by rw [show t * 4 + (u - t * 4) = u by omega, Nat.add_zero]; exact hne⟩

theorem Gx_allJ (lab : Nat → Nat) (hv : ValidK (t * 4 + m) 3 lab) (hm : 1 ≤ m)
    (hH : ∀ u, u < t * 4 → lab u = lab 0) (hb : lab 0 = lab (t * 4)) :
    ∀ c, c < 3 → ∃ v, v < m ∧ lab (t * 4 + v) = c := by
  intro c hc
  obtain ⟨v, hv1, hv2⟩ := hv.2 c hc
  by_cases h : v < t * 4
  · exact ⟨0, by omega, by rw [Nat.add_zero, ← hb, ← hH v h, hv2]⟩
  · exact ⟨v - t * 4, by omega, by rw [show t * 4 + (v - t * 4) = v by omega, hv2]⟩

theorem Gx_allH (lab : Nat → Nat) (hv : ValidK (t * 4 + m) 3 lab) (ht : 0 < t)
    (hJ : ∀ u, t * 4 ≤ u → u < t * 4 + m → lab u = lab (t * 4)) (hb : lab 0 = lab (t * 4)) :
    ∀ c, c < 3 → ∃ v, v < t * 4 ∧ lab v = c := by
  intro c hc
  obtain ⟨v, hv1, hv2⟩ := hv.2 c hc
  by_cases h : v < t * 4
  · exact ⟨v, h, hv2⟩
  · exact ⟨0, by omega, by rw [hb, ← hJ v (by omega) hv1, hv2]⟩

theorem Gx_two_colours (lab : Nat → Nat) (hv : ValidK (t * 4 + m) 3 lab) (_ht : 0 < t)
    (mH : ∀ u, u < t * 4 → lab u = lab 0) (mJ : ∀ u, t * 4 ≤ u → u < t * 4 + m → lab u = lab (t * 4)) : False := by
  have g : ∀ v, v < t * 4 + m → lab v = lab 0 ∨ lab v = lab (t * 4) := by
    intro v hv'; by_cases h : v < t * 4
    · left; exact mH v h
    · right; exact mJ v (by omega) hv'
  obtain ⟨a, ha, la⟩ := hv.2 0 (by omega)
  obtain ⟨b, hb, lb⟩ := hv.2 1 (by omega)
  obtain ⟨c, hc, lc⟩ := hv.2 2 (by omega)
  rcases g a ha with h1 | h1 <;> rcases g b hb with h2 | h2 <;> rcases g c hc with h3 | h3 <;> omega

theorem Gx_lower (ht : 0 < t) (hw1 : 1 ≤ weight t x) (hw : 4 * weight t x ≤ t) (hm : 3 ≤ m)
    (lab : Nat → Nat) (hv : ValidK (t * 4 + m) 3 lab) :
    2 * (1 + min (2 * weight t x) (m - 1)) ≤ cost (t * 4 + m) (Gx t m x) lab := by
  rw [cost_Gx t m x ht (by omega)]
  have hlab : ∀ y, y < t * 4 → lab y < 3 := fun y hy => hv.1 y (by omega)
  have hlabJ : ∀ y, y < m → lab (t * 4 + y) < 3 := fun y hy => hv.1 _ (by omega)
  by_cases sH : ∃ u v, u < t * 4 ∧ v < t * 4 ∧ lab u ≠ lab v <;>
  by_cases sJ : ∃ u v, u < m ∧ v < m ∧ lab (t * 4 + u) ≠ lab (t * 4 + v)
  · obtain ⟨u, v, hu, hv', h⟩ := sH
    obtain ⟨u', v', hu', hv'', h'⟩ := sJ
    have := H_split t x ht hw lab u v hu hv' h
    have := J_split m (fun u => lab (t * 4 + u)) u' v' hu' hv'' h'
    simp only [Nat.min_def]; split <;> omega
  · by_cases hb : lab 0 = lab (t * 4)
    · have := H_three t x ht hw1 hw lab hlab (Gx_allH t m lab hv ht (Gx_monoJ t m lab sJ) hb)
      simp only [Nat.min_def]; split <;> omega
    · obtain ⟨u, v, hu, hv', h⟩ := sH
      have := H_split t x ht hw lab u v hu hv' h
      have e : 2 * ind (lab 0 != lab (t * 4)) = 2 := by simp [hb, ind]
      simp only [Nat.min_def]; split <;> omega
  · by_cases hb : lab 0 = lab (t * 4)
    · have := J_three m _ hlabJ (Gx_allJ t m lab hv (by omega) (Gx_monoH t lab ht sH) hb)
      simp only [Nat.min_def]; split <;> omega
    · obtain ⟨u, v, hu, hv', h⟩ := sJ
      have := J_split m (fun u => lab (t * 4 + u)) u v hu hv' h
      have e : 2 * ind (lab 0 != lab (t * 4)) = 2 := by simp [hb, ind]
      simp only [Nat.min_def]; split <;> omega
  · exact (Gx_two_colours t m lab hv ht (Gx_monoH t lab ht sH) (Gx_monoJ t m lab sJ)).elim

/-- Cutting H_x along (A, B) and isolating J. -/
def labA (u : Nat) : Nat := if u < t * 4 then (if halfA t u then 0 else 1) else 2
/-- Isolating H_x and cutting one vertex off J. -/
def labJx (u : Nat) : Nat := if u < t * 4 then 0 else if u = t * 4 then 1 else 2

theorem halfA_zero (_ht : 0 < t) : halfA t 0 = true := by
  simp [halfA, blk, Nat.zero_div]

theorem halfA_B (ht : 0 < t) : halfA t (t * 2) = false := by
  have : t * 2 / t = 2 := by rw [Nat.mul_comm]; exact Nat.mul_div_cancel _ ht
  simp [halfA, blk, this]

theorem labA_valid (ht : 0 < t) (hm : 1 ≤ m) : ValidK (t * 4 + m) 3 (labA t) := by
  refine ⟨fun y _ => by unfold labA; split <;> (try split) <;> omega, fun c hc => ?_⟩
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · exact ⟨0, by omega, by simp [labA, show 0 < t * 4 by omega, halfA_zero t ht]⟩
  · exact ⟨t * 2, by omega, by simp [labA, show t * 2 < t * 4 by omega, halfA_B t ht]⟩
  · exact ⟨t * 4, by omega, by simp [labA]⟩

theorem labJx_valid (ht : 0 < t) (hm : 2 ≤ m) : ValidK (t * 4 + m) 3 (labJx t) := by
  refine ⟨fun y _ => by unfold labJx; split <;> (try split) <;> omega, fun c hc => ?_⟩
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · exact ⟨0, by omega, by simp [labJx, show 0 < t * 4 by omega]⟩
  · exact ⟨t * 4, by omega, by simp [labJx]⟩
  · exact ⟨t * 4 + 1, by omega, by simp [labJx]⟩

theorem labA_cost (ht : 0 < t) (hw : 4 * weight t x ≤ t) (hm : 1 ≤ m) :
    cost (t * 4 + m) (Gx t m x) (labA t) = 4 * weight t x + 2 := by
  rw [cost_Gx t m x ht hm]
  have e1 : cost (t * 4) (wx t x) (labA t) = q (t * 4) (wx t x) (halfA t) := by
    unfold cost q; apply D_congr; intro u v hu hv
    simp only [labA, hu, hv, ite_true]
    cases halfA t u <;> cases halfA t v <;> rfl
  have e2 : cost m wK (fun u => labA t (t * 4 + u)) = 0 := by
    unfold cost; rw [D_congr m _ (fun _ _ => 0) (fun u v _ _ => by
      simp [labA, show ¬ (t * 4 + u < t * 4) by omega, show ¬ (t * 4 + v < t * 4) by omega, ind]), D_zero]
  have e3 : 2 * ind (labA t 0 != labA t (t * 4)) = 2 := by
    simp [labA, show 0 < t * 4 by omega, halfA_zero t ht, ind]
  rw [e1, e2, e3, (Hx_mincut t x ht hw).1]

theorem labJx_cost (ht : 0 < t) (hm : 2 ≤ m) :
    cost (t * 4 + m) (Gx t m x) (labJx t) = 2 * m := by
  rw [cost_Gx t m x ht (by omega)]
  have e1 : cost (t * 4) (wx t x) (labJx t) = 0 := by
    unfold cost; rw [D_congr (t * 4) _ (fun _ _ => 0) (fun u v hu hv => by simp [labJx, hu, hv, ind]), D_zero]
  have e2 : cost m wK (fun u => labJx t (t * 4 + u)) = q m wK (fun u => u == 0) := by
    unfold cost q; apply D_congr; intro u v _ _
    simp only [labJx, show ¬ (t * 4 + u < t * 4) by omega, show ¬ (t * 4 + v < t * 4) by omega, ite_false,
      Nat.add_right_eq_self]
    by_cases a : u = 0 <;> by_cases b : v = 0 <;> simp [a, b, ind]
    have ea : (u == 0) = false := by simp [a]
    have eb : (v == 0) = false := by simp [b]
    rw [ea, eb]; simp
  have e3 : q m wK (fun u => u == 0) = 2 * (m - 1) := by
    rw [kn_cut]
    have h1 : cnt m (fun u => u == 0) = 1 := by
      have := pick (fun _ => 1) 0 m (by omega); unfold cnt; simpa using this
    have h2 := cnt_compl m (fun u => u == 0)
    rw [h1] at h2 ⊢; omega
  have e4 : 2 * ind (labJx t 0 != labJx t (t * 4)) = 2 := by
    simp [labJx, show 0 < t * 4 by omega, ind]
  rw [e1, e2, e3, e4]; omega

/-- Equation (bridge-min3): λ₃(G_x) = 1 + min{λ₂(H_x), m - 1} (doubled), λ₂(H_x) = 2|x|. -/
theorem Gx_lambda3 (ht : 0 < t) (hw1 : 1 ≤ weight t x) (hw : 4 * weight t x ≤ t) (hm : 3 ≤ m) :
    IsMinK (t * 4 + m) (Gx t m x) 3 (2 * (1 + min (2 * weight t x) (m - 1))) := by
  refine ⟨?_, Gx_lower t m x ht hw1 hw hm⟩
  by_cases h : 2 * weight t x ≤ m - 1
  · exact ⟨labA t, labA_valid t m ht (by omega), by rw [labA_cost t m x ht hw (by omega)]; simp [Nat.min_def, h]; omega⟩
  · exact ⟨labJx t, labJx_valid t m ht (by omega), by rw [labJx_cost t m x ht (by omega)]; simp [Nat.min_def, h]; omega⟩

/-- If |x| = k - 1 (2|x| ≤ m - 2 with m = 2k), every optimum leaves J whole and splits H_x
    exactly along its unique minimum cut (A, B). -/
theorem Gx_opt_small (ht : 0 < t) (hw1 : 1 ≤ weight t x) (hw : 4 * weight t x ≤ t) (hm : 3 ≤ m)
    (hsm : 2 * weight t x + 2 ≤ m) (lab : Nat → Nat) (hv : ValidK (t * 4 + m) 3 lab)
    (hopt : cost (t * 4 + m) (Gx t m x) lab = 2 * (1 + min (2 * weight t x) (m - 1))) :
    (∀ u, t * 4 ≤ u → u < t * 4 + m → lab u = lab (t * 4)) ∧
    (∀ u v, u < t * 4 → v < t * 4 → (lab u = lab v ↔ halfA t u = halfA t v)) := by
  rw [cost_Gx t m x ht (by omega), show min (2 * weight t x) (m - 1) = 2 * weight t x by
    simp [Nat.min_def]; omega] at hopt
  have hlab : ∀ y, y < t * 4 → lab y < 3 := fun y hy => hv.1 y (by omega)
  have hlabJ : ∀ y, y < m → lab (t * 4 + y) < 3 := fun y hy => hv.1 _ (by omega)
  have hN : 0 < t * 4 := by omega
  have sJ : ¬ ∃ u v, u < m ∧ v < m ∧ lab (t * 4 + u) ≠ lab (t * 4 + v) := by
    intro sJ
    obtain ⟨u', v', hu', hv'', h'⟩ := sJ
    have := J_split m (fun u => lab (t * 4 + u)) u' v' hu' hv'' h'
    by_cases sH : ∃ u v, u < t * 4 ∧ v < t * 4 ∧ lab u ≠ lab v
    · obtain ⟨u, v, hu, hv', h⟩ := sH
      have := H_split t x ht hw lab u v hu hv' h; omega
    · by_cases hb : lab 0 = lab (t * 4)
      · have := J_three m _ hlabJ (Gx_allJ t m lab hv (by omega) (Gx_monoH t lab ht sH) hb); omega
      · have e : 2 * ind (lab 0 != lab (t * 4)) = 2 := by simp [hb, ind]
        omega
  have mJ := Gx_monoJ t m lab sJ
  refine ⟨mJ, ?_⟩
  have hb : lab 0 ≠ lab (t * 4) := by
    intro hb; have := H_three t x ht hw1 hw lab hlab (Gx_allH t m lab hv ht mJ hb); omega
  have e : 2 * ind (lab 0 != lab (t * 4)) = 2 := by simp [hb, ind]
  have sH : ∃ u v, u < t * 4 ∧ v < t * 4 ∧ lab u ≠ lab v := by
    apply Classical.byContradiction; intro sH
    exact Gx_two_colours t m lab hv ht (Gx_monoH t lab ht sH) mJ
  obtain ⟨u0, v0, hu0, hv0, hne0⟩ := sH
  have hq := shore_le_cost (t * 4) (wx t x) lab (lab 0)
  have hmc := (Hx_mincut t x ht hw).2 (part lab (lab 0)) ⟨0, hN, by simp [part]⟩ (by
    by_cases h : lab u0 = lab 0
    · exact ⟨v0, hv0, by simp [part]; omega⟩
    · exact ⟨u0, hu0, by simp [part, h]⟩)
  have heq : q (t * 4) (wx t x) (part lab (lab 0)) = 4 * weight t x := by omega
  have two : ∀ u v, u < t * 4 → v < t * 4 → lab u ≠ lab 0 → lab v ≠ lab 0 → lab u = lab v := by
    intro u v hu hv' h1 h2
    apply Classical.byContradiction; intro h3
    have l0 := hlab 0 hN; have lu := hlab u hu; have lv := hlab v hv'
    have := H_three t x ht hw1 hw lab hlab (fun c hc => by
      rcases (by omega : c = lab 0 ∨ c = lab u ∨ c = lab v) with e | e | e
      · exact ⟨0, hN, e.symm⟩
      · exact ⟨u, hu, e.symm⟩
      · exact ⟨v, hv', e.symm⟩)
    omega
  have key : ∀ u v, u < t * 4 → v < t * 4 →
      (lab u = lab v ↔ part lab (lab 0) u = part lab (lab 0) v) := by
    intro u v hu hv'
    simp only [part]
    constructor
    · intro e; rw [e]
    · intro e
      by_cases a : lab u = lab 0 <;> by_cases b : lab v = lab 0
      · rw [a, b]
      · simp [a, b] at e
      · simp [a, b] at e
      · exact two u v hu hv' a b
  intro u v hu hv'
  rw [key u v hu hv']
  rcases hmc.2 heq with hX | hX
  · rw [hX u hu, hX v hv']
  · rw [hX u hu, hX v hv']; cases halfA t u <;> cases halfA t v <;> simp

/-- If |x| = k (2|x| ≥ m = 2k), every optimum leaves H_x whole. -/
theorem Gx_opt_large (ht : 0 < t) (hw1 : 1 ≤ weight t x) (hw : 4 * weight t x ≤ t) (hm : 3 ≤ m)
    (hlm : m ≤ 2 * weight t x) (lab : Nat → Nat) (hv : ValidK (t * 4 + m) 3 lab)
    (hopt : cost (t * 4 + m) (Gx t m x) lab = 2 * (1 + min (2 * weight t x) (m - 1))) :
    ∀ u, u < t * 4 → lab u = lab 0 := by
  rw [cost_Gx t m x ht (by omega), show min (2 * weight t x) (m - 1) = m - 1 by
    simp [Nat.min_def]; omega] at hopt
  have hlab : ∀ y, y < t * 4 → lab y < 3 := fun y hy => hv.1 y (by omega)
  apply Gx_monoH t lab ht
  intro sH
  obtain ⟨u, v, hu, hv', h⟩ := sH
  have := H_split t x ht hw lab u v hu hv' h
  have sJ : ¬ ∃ u v, u < m ∧ v < m ∧ lab (t * 4 + u) ≠ lab (t * 4 + v) := by
    intro sJ; obtain ⟨u', v', hu', hv'', h'⟩ := sJ
    have := J_split m (fun u => lab (t * 4 + u)) u' v' hu' hv'' h'; omega
  by_cases hb : lab 0 = lab (t * 4)
  · have := H_three t x ht hw1 hw lab hlab (Gx_allH t m lab hv ht (Gx_monoJ t m lab sJ) hb); omega
  · have e : 2 * ind (lab 0 != lab (t * 4)) = 2 := by simp [hb, ind]
    omega

end GxFacts


/-- Theorem 20, reciprocity of the fixed-slot arrays: if the cross slot s of v returns u, then
    the cross slot of u indexed by idx v returns v, and both slots read the same bit of x; so
    every cross edge occupies the slots associated with the same pair (i, j) at its two
    endpoints. Same-block slots are public and listed exactly once (`nbr_complete`). -/
theorem nbr_recip (t : Nat) (x : Nat → Nat → Bool) (ht : 0 < t) (v s : Nat) (hv : v < t * 4) (hs : s < t) :
    nbr t x (nbr t x v s) (idx t v) = v ∧ slotBit t (nbr t x v s) (idx t v) = slotBit t v s := by
  obtain ⟨c, i, hc, hi, rfl, hb, hix⟩ := slot_decomp t v ht hv
  rw [hix]
  have hcr : ∀ b, cross c b < 4 := by intro b; unfold cross; (repeat' split) <;> omega
  have hB : ∀ b, blk t (t * cross c b + s) = cross c b := fun b => blk_eq t _ s ht hs
  have hI : ∀ b, idx t (t * cross c b + s) = s := fun b => idx_eq t _ s hs
  unfold nbr nbrF slotBit
  simp only [hb, hix, hs, hi, ite_true, hB, hI]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
  · cases h : x i s <;> simp [cross, h]
  · cases h : x s i <;> simp [cross, h]
  · cases h : x s i <;> simp [cross, h]
  · cases h : x i s <;> simp [cross, h]

end MinKCut
