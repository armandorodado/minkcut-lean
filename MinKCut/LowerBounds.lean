import MinKCut.Disjointness
/-! # Parts N–P: Lemma 25 threshold, Lemma 27, remaining deterministic statements, Corollary 28 -/

namespace MinKCut

/-! ## Part N: Lemma 25 as a threshold statement, and Lemma 27 for deterministic algorithms -/

/-! ### Counting utilities -/

theorem cnt_succ (P : Nat → Bool) (m : Nat) : cnt (m + 1) P = cnt m P + ind (P m) := by
  unfold cnt; rw [List.range_succ, lsum_append]; simp [lsum]

theorem cnt_prefix_mono (P : Nat → Bool) (a : Nat) : ∀ b, a ≤ b → cnt a P ≤ cnt b P := by
  intro b hab
  induction b with
  | zero => rw [show a = 0 by omega]; exact Nat.le_refl _
  | succ b ih =>
    by_cases h : a = b + 1
    · rw [h]; exact Nat.le_refl _
    · rw [cnt_succ]; have := ih (by omega); omega

theorem cnt_mono_set (n : Nat) (P Q : Nat → Bool) (h : ∀ x, x < n → P x = true → Q x = true) :
    cnt n P ≤ cnt n Q := by
  unfold cnt; apply lsum_mono; intro x hx
  have := h x (List.mem_range.mp hx)
  cases hp : P x <;> cases hq : Q x <;> simp_all [ind]

theorem cnt_split (n : Nat) (P Q : Nat → Bool) :
    cnt n P = cnt n (fun x => P x && Q x) + cnt n (fun x => P x && !Q x) := by
  unfold cnt; rw [← lsum_add]; apply lsum_congr; intro x _
  cases hp : P x <;> cases hq : Q x <;> simp [ind, hp, hq]

theorem cnt_lt_count (n p : Nat) (hp : p ≤ n) : cnt n (fun x => decide (x < p)) = p :=
  lsum_lt_count n p hp

/-- A set of vertices below p is counted fully by the first p positions. -/
theorem cnt_below (n p : Nat) (P : Nat → Bool) (hp : p ≤ n) (h : ∀ x, P x = true → x < p) :
    cnt n P = cnt p P := by
  unfold cnt
  rw [show n = p + (n - p) by omega, lsum_range_add]
  rw [lsum_congr (List.range (n - p)) (fun i => ind (P (p + i))) (fun _ => 0) (fun i _ => by
    cases hq : P (p + i)
    · simp [ind, hq]
    · have := h _ hq; omega), lsum_zero]
  omega

theorem rank_surj (C : Nat → Bool) : ∀ n r, r < cnt n C → ∃ x, x < n ∧ C x = true ∧ cnt x C = r := by
  intro n
  induction n with
  | zero => intro r h; simp [cnt, lsum] at h
  | succ n ih =>
    intro r h
    rw [cnt_succ] at h
    by_cases hr : r < cnt n C
    · obtain ⟨x, hx, h1, h2⟩ := ih r hr
      exact ⟨x, by omega, h1, h2⟩
    · cases hc : C n
      · simp [hc, ind] at h; omega
      · simp [hc, ind] at h
        exact ⟨n, by omega, hc, by omega⟩

theorem rank_lt (C : Nat → Bool) (x y : Nat) (hxy : x < y) (hx : C x = true) : cnt x C < cnt y C := by
  have h1 := cnt_prefix_mono C (x + 1) y (by omega)
  rw [cnt_succ] at h1
  simp [hx, ind] at h1; omega

theorem rank_inj (C : Nat → Bool) (x y : Nat) (hx : C x = true) (hy : C y = true)
    (h : cnt x C = cnt y C) : x = y := by
  rcases Nat.lt_trichotomy x y with hl | he | hg
  · have := rank_lt C x y hl hx; omega
  · exact he
  · have := rank_lt C y x hg hy; omega

theorem three_distinct (n : Nat) (C : Nat → Bool) (h : 3 ≤ cnt n C) :
    ∃ a b c, a < n ∧ b < n ∧ c < n ∧ C a = true ∧ C b = true ∧ C c = true ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c := by
  obtain ⟨a, ha, ca, ra⟩ := rank_surj C n 0 (by omega)
  obtain ⟨b, hb, cb, rb⟩ := rank_surj C n 1 (by omega)
  obtain ⟨c, hc, cc, rc⟩ := rank_surj C n 2 (by omega)
  refine ⟨a, b, c, ha, hb, hc, ca, cb, cc, ?_, ?_, ?_⟩ <;> intro e <;> subst e <;> omega


/-! ### Lemma 25 as a threshold: λ_k(L_{k,M}(F)) = T ⟺ F has a (k-1)-clique -/

/-- A labelled k-partition of 0..N-1 with every part nonempty. -/
def ValidK (N k : Nat) (lab : Nat → Nat) : Prop :=
  (∀ y, y < N → lab y < k) ∧ ∀ c, c < k → ∃ v, v < N ∧ lab v = c

/-- m is the (doubled) minimum k-cut value λ_k of w. -/
def IsMinK (N : Nat) (w : Nat → Nat → Nat) (k m : Nat) : Prop :=
  (∃ lab, ValidK N k lab ∧ cost N w lab = m) ∧ ∀ lab, ValidK N k lab → m ≤ cost N w lab

/-- F has a clique of size at least m on 0..p-1. -/
def HasClique (p : Nat) (F : Nat → Nat → Nat) (m : Nat) : Prop :=
  ∃ C : Nat → Bool, (∀ x, C x = true → x < p) ∧ m ≤ cnt p C ∧
    ∀ x y, C x = true → C y = true → x ≠ y → 1 ≤ F x y

def swpv (j a : Nat) : Nat := if a = j then 0 else if a = 0 then j else a

theorem swpv_inj (j a b : Nat) (h : swpv j a = swpv j b) : a = b := by
  unfold swpv at h; (repeat' split at h) <;> omega

theorem cost_swp (N : Nat) (w : Nat → Nat → Nat) (j : Nat) (lab : Nat → Nat) :
    cost N w (fun x => swpv j (lab x)) = cost N w lab := by
  unfold cost; apply D_congr; intro u v _ _
  by_cases h : lab u = lab v
  · simp [h]
  · have : swpv j (lab u) ≠ swpv j (lab v) := fun e => h (swpv_inj j _ _ e)
    have e1 : (swpv j (lab u) != swpv j (lab v)) = true := by simp [this]
    have e2 : (lab u != lab v) = true := by simp [h]
    rw [e1, e2]

theorem valid_swp (N k j : Nat) (lab : Nat → Nat) (hv : ValidK N k lab) (hj : j < k) :
    ValidK N k (fun x => swpv j (lab x)) := by
  refine ⟨fun y hy => ?_, fun c hc => ?_⟩
  · have := hv.1 y hy; show swpv j (lab y) < k; unfold swpv; (repeat' split) <;> omega
  · by_cases h0 : c = 0
    · obtain ⟨v, hv1, hv2⟩ := hv.2 j hj; exact ⟨v, hv1, by simp [swpv, hv2, h0]⟩
    · by_cases hcj : c = j
      · obtain ⟨v, hv1, hv2⟩ := hv.2 0 (by omega)
        exact ⟨v, hv1, by simp [swpv, hv2, hcj]⟩
      · obtain ⟨v, hv1, hv2⟩ := hv.2 c hc; exact ⟨v, hv1, by simp [swpv, hv2, hcj, h0]⟩

/-- Hypotheses of Lemma 25 for the canonical gadget: F = Fp + Fa + Fb simple, k ≥ 2, p ≥ 1,
    M ≥ k²p. -/
def LiHyp (k p M : Nat) (Fp Fa Fb : Nat → Nat → Nat) : Prop :=
  (∀ u v, Fp u v + Fa u v + Fb u v = Fp v u + Fa v u + Fb v u) ∧
  (∀ u, Fp u u + Fa u u + Fb u u = 0) ∧ (∀ u v, Fp u v + Fa u v + Fb u v ≤ 1) ∧
  2 ≤ k ∧ 1 ≤ p ∧ k * k * p ≤ M

theorem liG_base (p M : Nat) (Fp Fa Fb : Nat → Nat → Nat) (x y : Nat) (hx : x < p) (hy : y < p) :
    liG p M Fp Fa Fb x y = Fp x y + Fa x y + Fb x y := by
  simp [liG, liPub, rb, cliqueW, att, ind, hx, hy, show ¬ p ≤ x by omega, show ¬ p ≤ y by omega]

theorem liK_lower (k p M : Nat) (Fp Fa Fb : Nat → Nat → Nat) (hH : LiHyp k p M Fp Fa Fb)
    (lab : Nat → Nat) (hv : ValidK (p + M) k lab) :
    2 * ((k - 1) * p) ≤ cost (p + M) (liG p M Fp Fa Fb) lab + c2 (k - 1) ∧
    (cost (p + M) (liG p M Fp Fa Fb) lab + c2 (k - 1) = 2 * ((k - 1) * p) →
      HasClique p (fun x y => Fp x y + Fa x y + Fb x y) (k - 1)) := by
  obtain ⟨hsym, hloop, hle, hk, hp, hM⟩ := hH
  have h2k : 2 * k ≤ k * k := Nat.mul_le_mul_right k hk
  have h2kp : 2 * k * p ≤ k * k * p := Nat.mul_le_mul_right p h2k
  have hkp : 2 * p ≤ k * p := Nat.mul_le_mul_right p hk
  have hsub : (k - 1) * p + p = k * p := by rw [← Nat.succ_mul, show (k - 1).succ = k by omega]
  rw [Nat.mul_assoc] at h2kp
  have hpM : p ≤ M := by omega
  have shape := liG_shape p M Fp Fa Fb hpM hsym hloop hle
  generalize hL : liG p M Fp Fa Fb = L at shape
  by_cases hs : ∃ x0 y0, p ≤ x0 ∧ x0 < p + M ∧ p ≤ y0 ∧ y0 < p + M ∧ lab x0 ≠ lab y0
  · obtain ⟨x0, y0, h1, h2, h3, h4, h5⟩ := hs
    have hcs := clique_split (p + M) L lab (fun x => decide (p ≤ x))
      (fun x y _ _ hx hy hxy => by
        simp at hx hy
        rw [shape.2.2.2.1 x y hx hy (by omega) (by omega) hxy]; exact Nat.le_refl 1)
      x0 y0 h2 h4 (by simp [h1]) (by simp [h3]) h5
    have hW : cnt (p + M) (fun x => decide (p ≤ x)) = M := by
      have h1 := cnt_compl (p + M) (fun x => decide (x < p))
      rw [cnt_lt_count _ _ (by omega)] at h1
      have : (fun x => !decide (x < p)) = (fun x => decide (p ≤ x)) := by
        funext x; by_cases h : x < p <;> simp [h] <;> omega
      rw [this] at h1; omega
    rw [hW] at hcs
    constructor
    · omega
    · intro h; exfalso; omega
  · have hall : ∀ x, p ≤ x → x < p + M → lab x = lab p := by
      intro x h1 h2
      apply Classical.byContradiction; intro hne
      exact hs ⟨x, p, h1, h2, Nat.le_refl _, by omega, hne⟩
    have hj : lab p < k := hv.1 p (by omega)
    generalize hjj : lab p = j at hall hj
    have hv' := valid_swp (p + M) k j lab hv hj
    have hc' := cost_swp (p + M) L j lab
    generalize hlab' : (fun x => swpv j (lab x)) = lab' at hv' hc'
    have hl0 : ∀ x, p ≤ x → x < p + M → lab' x = 0 := by
      intro x h1 h2; rw [← hlab']; simp [swpv, hall x h1 h2]
    let R : Nat → Bool := fun x => decide (x < p + M) && !(lab' x == 0)
    have hR : ∀ x, x < p + M → (lab' x = 0 ↔ R x = false) := by
      intro x hx; simp [R, hx]
    have hRp : ∀ x, R x = true → x < p := by
      intro x hx
      simp only [R, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hx
      apply Classical.byContradiction; intro h
      exact hx.2 (hl0 x (by omega) hx.1)
    have hdeg : ∀ x, x < p + M → R x = true → deg (p + M) L x = p :=
      fun x _ hx => shape.2.2.2.2 x (hRp x hx)
    have hrp : cnt (p + M) R ≤ p := by
      have := cnt_mono_set (p + M) R (fun x => decide (x < p)) (fun x _ h => by simp [hRp x h])
      rw [cnt_lt_count _ _ (by omega)] at this; exact this
    have hne : ∀ i, 1 ≤ i → i < k → ∃ v, v < p + M ∧ lab' v = i := fun i _ hi => hv'.2 i hi
    obtain ⟨_, hlow⟩ := li_gadget_lower (p + M) L shape.1 shape.2.1 shape.2.2.1 k p hk lab' R hv'.1 hne hR hdeg hrp
    constructor
    · omega
    · intro heq
      rw [← hc'] at heq
      obtain ⟨_, hr, hcl⟩ := li_gadget_equality (p + M) L shape.1 shape.2.1 shape.2.2.1 k p hk lab' R
        hv'.1 hne hR hdeg hrp heq
      refine ⟨R, hRp, ?_, ?_⟩
      · rw [← cnt_below (p + M) p R (by omega) hRp]; exact hr
      · intro x y hx hy hxy
        have hx' := hRp x hx
        have hy' := hRp y hy
        have := hcl x y (by omega) (by omega) hx hy hxy
        rw [← hL, liG_base p M Fp Fa Fb x y hx' hy'] at this
        show 1 ≤ Fp x y + Fa x y + Fb x y
        omega

theorem cnt_cap (C : Nat → Bool) (r : Nat) : ∀ m,
    cnt m (fun x => C x && decide (cnt x C < r)) = min (cnt m C) r := by
  intro m
  induction m with
  | zero => simp [cnt, lsum]
  | succ m ih =>
    rw [cnt_succ, cnt_succ, ih]
    cases hc : C m <;> simp [hc, ind] <;> (try split) <;> omega

theorem liK_attain (k p M : Nat) (Fp Fa Fb : Nat → Nat → Nat) (hH : LiHyp k p M Fp Fa Fb)
    (hC : HasClique p (fun x y => Fp x y + Fa x y + Fb x y) (k - 1)) :
    ∃ lab, ValidK (p + M) k lab ∧ cost (p + M) (liG p M Fp Fa Fb) lab + c2 (k - 1) = 2 * ((k - 1) * p) := by
  obtain ⟨hsym, hloop, hle, hk, hp, hM⟩ := hH
  have h2k : 2 * k ≤ k * k := Nat.mul_le_mul_right k hk
  have h2kp : 2 * k * p ≤ k * k * p := Nat.mul_le_mul_right p h2k
  have hkp : 2 * p ≤ k * p := Nat.mul_le_mul_right p hk
  rw [Nat.mul_assoc] at h2kp
  have hpM : p ≤ M := by omega
  have shape := liG_shape p M Fp Fa Fb hpM hsym hloop hle
  obtain ⟨C, hCp, hcnt, hadj⟩ := hC
  let R : Nat → Bool := fun x => C x && decide (cnt x C < k - 1)
  let lab : Nat → Nat := fun x => if R x = true then cnt x C + 1 else 0
  have hRC : ∀ x, R x = true → C x = true := by intro x h; simp [R] at h; exact h.1
  have hRk : ∀ x, R x = true → cnt x C < k - 1 := by intro x h; simp [R] at h; exact h.2
  have hR : ∀ x, x < p + M → (lab x = 0 ↔ R x = false) := by
    intro x _; simp only [lab]; cases R x <;> simp
  have hdeg : ∀ x, x < p + M → R x = true → deg (p + M) (liG p M Fp Fa Fb) x = p :=
    fun x _ hx => shape.2.2.2.2 x (hCp x (hRC x hx))
  have hsingle : ∀ x y, x < p + M → y < p + M → R x = true → lab x = lab y → x = y := by
    intro x y _ _ hx hl
    simp only [lab, hx, ite_true] at hl
    cases hy : R y
    · simp [hy] at hl
    · simp only [hy, ite_true] at hl
      exact rank_inj C x y (hRC x hx) (hRC y hy) (by omega)
  have hclique : ∀ x y, x < p + M → y < p + M → R x = true → R y = true → x ≠ y →
      liG p M Fp Fa Fb x y = 1 := by
    intro x y _ _ hx hy hxy
    rw [liG_base p M Fp Fa Fb x y (hCp x (hRC x hx)) (hCp y (hRC y hy))]
    have h1 : 1 ≤ Fp x y + Fa x y + Fb x y := hadj x y (hRC x hx) (hRC y hy) hxy
    have := hle x y
    omega
  have hat := li_gadget_attain (p + M) (liG p M Fp Fa Fb) shape.1 shape.2.1 lab R p hR hdeg hsingle hclique
  have hcR : cnt (p + M) R = k - 1 := by
    rw [cnt_below (p + M) p R (by omega) (fun x h => hCp x (hRC x h))]
    rw [cnt_cap C (k - 1) p]; omega
  rw [hcR, Nat.mul_comm p] at hat
  refine ⟨lab, ⟨fun y _ => ?_, fun c hc => ?_⟩, hat⟩
  · simp only [lab]; split
    · have := hRk y (by assumption); omega
    · omega
  · by_cases h0 : c = 0
    · refine ⟨p, by omega, ?_⟩
      have : C p = false := by
        cases h : C p
        · rfl
        · have := hCp p h; omega
      simp [lab, R, this, h0]
    · obtain ⟨x, hx, hcx, hr⟩ := rank_surj C p (c - 1) (by omega)
      refine ⟨x, by omega, ?_⟩
      have : R x = true := by simp [R, hcx, hr]; omega
      simp only [lab, this, ite_true]; omega

/-- Lemma 25 (threshold form): if m = λ_k(L_{k,M}(F)) (doubled), then
    m + (k-1)(k-2) = 2(k-1)p exactly when F has a (k-1)-clique. -/
theorem li_threshold (k p M : Nat) (Fp Fa Fb : Nat → Nat → Nat) (hH : LiHyp k p M Fp Fa Fb) (m : Nat)
    (hm : IsMinK (p + M) (liG p M Fp Fa Fb) k m) :
    m + c2 (k - 1) = 2 * ((k - 1) * p) ↔ HasClique p (fun x y => Fp x y + Fa x y + Fb x y) (k - 1) := by
  obtain ⟨⟨lab0, hv0, hc0⟩, hmin⟩ := hm
  constructor
  · intro h; rw [← hc0] at h; exact (liK_lower k p M Fp Fa Fb hH lab0 hv0).2 h
  · intro hC
    obtain ⟨lab, hv, heq⟩ := liK_attain k p M Fp Fa Fb hH hC
    have h1 := hmin lab hv
    have h2 := (liK_lower k p M Fp Fa Fb hH lab0 hv0).1
    rw [hc0] at h2
    omega


/-! ### The base graph of Lemma 27: Γ_t joined to a clique U of size k - 4 -/

/-- The clique U = {3t, ..., 3t+u-1}, joined to every vertex of Γ_t. -/
def Uj (t u : Nat) (a b : Nat) : Nat :=
  ind (decide (3 * t ≤ a) && decide (a < 3 * t + u) && decide (3 * t ≤ b) && decide (b < 3 * t + u) && a != b)
  + ind (decide (3 * t ≤ a) && decide (a < 3 * t + u) && decide (b < 3 * t))
  + ind (decide (3 * t ≤ b) && decide (b < 3 * t + u) && decide (a < 3 * t))

theorem Uj_inside (t u a b : Nat) (ha : a < 3 * t) (hb : b < 3 * t) : Uj t u a b = 0 := by
  simp [Uj, ind, show ¬ 3 * t ≤ a by omega, show ¬ 3 * t ≤ b by omega]

theorem Uj_simple (t u : Nat) :
    (∀ a b, Uj t u a b = Uj t u b a) ∧ (∀ a, Uj t u a a = 0) ∧ (∀ a b, Uj t u a b ≤ 1) := by
  refine ⟨fun a b => ?_, fun a => ?_, fun a b => ?_⟩
  · unfold Uj ind
    by_cases hab : a = b
    · subst hab; omega
    · have h1 : (a != b) = true := by simp [hab]
      have h2 : (b != a) = true := by simp [Ne.symm hab]
      rw [h1, h2]
      by_cases a1 : 3 * t ≤ a <;> by_cases a2 : a < 3 * t + u <;> by_cases b1 : 3 * t ≤ b <;>
        by_cases b2 : b < 3 * t + u <;> simp [a1, a2, b1, b2] <;> omega
  · unfold Uj ind
    by_cases a1 : 3 * t ≤ a <;> by_cases a2 : a < 3 * t + u <;> simp [a1, a2] <;> omega
  · unfold Uj ind
    by_cases a1 : 3 * t ≤ a <;> by_cases a2 : a < 3 * t + u <;> by_cases b1 : 3 * t ≤ b <;>
      by_cases b2 : b < 3 * t + u <;> simp [a1, a2, b1, b2] <;> (repeat' split) <;> omega

theorem gamma_support (t : Nat) (x y : Nat → Nat → Bool) (a b : Nat)
    (h : 1 ≤ gPub t a b + gA t x a b + gB t y a b) : a < 3 * t ∧ b < 3 * t := by
  apply Classical.byContradiction; intro hn
  have : gPub t a b + gA t x a b + gB t y a b = 0 := by
    unfold gPub gA gB ind
    by_cases a1 : a < 3 * t
    · have b1 : ¬ b < 3 * t := by omega
      by_cases a2 : a < t <;> by_cases a3 : a < 2 * t <;> simp [a1, b1, a2, a3] <;> (repeat' split) <;> omega
    · by_cases b2 : b < t <;> by_cases b3 : b < 2 * t <;> simp [a1, b2, b3] <;> (repeat' split) <;> omega
  omega

/-- The public part of the base graph: the matching of Γ_t and the clique U with its join. -/
def basePub (t u : Nat) (a b : Nat) : Nat := gPub t a b + Uj t u a b

theorem base_eq (t u : Nat) (x y : Nat → Nat → Bool) (a b : Nat) :
    basePub t u a b + gA t x a b + gB t y a b = gamma t x y a b + Uj t u a b := by
  unfold basePub gamma; omega

theorem base_hyp (k t M : Nat) (x y : Nat → Nat → Bool) (hk : 4 ≤ k) (ht : 1 ≤ t)
    (hM : k * k * (3 * t + (k - 4)) ≤ M) :
    LiHyp k (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y) := by
  obtain ⟨gs, gl, gle⟩ := gamma_simple t x y
  obtain ⟨us, ul, ule⟩ := Uj_simple t (k - 4)
  refine ⟨fun a b => ?_, fun a => ?_, fun a b => ?_, by omega, by omega, hM⟩
  · rw [base_eq, base_eq, us a b]; unfold gamma; rw [gs a b]
  · rw [base_eq, ul a]; unfold gamma; rw [gl a]
  · rw [base_eq]; unfold gamma
    have := gle a b
    have := ule a b
    by_cases h : 1 ≤ gPub t a b + gA t x a b + gB t y a b
    · have hs := gamma_support t x y a b h
      rw [Uj_inside t (k - 4) a b hs.1 hs.2]; omega
    · omega

theorem cnt_three (n a b c : Nat) (ha : a < n) (hb : b < n) (hc : c < n) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (P : Nat → Bool) (hPa : P a = true) (hPb : P b = true) (hPc : P c = true) :
    3 ≤ cnt n P := by
  have h1 : cnt n (fun z => z == a || z == b || z == c) = 3 := by
    unfold cnt
    rw [lsum_congr _ _ (fun z => ind ((a == z) && true) + ind ((b == z) && true) + ind ((c == z) && true))
      (fun z _ => by
        by_cases e1 : a = z <;> by_cases e2 : b = z <;> by_cases e3 : c = z <;>
          simp [ind, e1, e2, e3, @eq_comm _ z] <;> omega)]
    rw [lsum_add, lsum_add, count_one, count_one, count_one]
    simp [ha, hb, hc, ind]
  have := cnt_mono_set n (fun z => z == a || z == b || z == c) P (by
    intro z _ hz
    simp only [Bool.or_eq_true, beq_iff_eq] at hz
    rcases hz with (h | h) | h <;> subst h <;> assumption)
  omega

theorem gamma_tri_edges (t : Nat) (x y : Nat → Nat → Bool) (i j : Nat) (hi : i < t) (hj : j < t)
    (hx : x i j = true) (hy : y i j = true) :
    1 ≤ gamma t x y i (t + j) ∧ 1 ≤ gamma t x y (t + j) (2 * t + i) ∧ 1 ≤ gamma t x y i (2 * t + i) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [gamma_gadj t x y _ _ (by omega) (by omega)]
    simp [gdec, hi, show ¬ t + j < t by omega, show t + j < 2 * t by omega, gadj, mask, hx, hj, ind,
      show t + j - t = j by omega]
  · rw [gamma_gadj t x y _ _ (by omega) (by omega)]
    simp [gdec, show ¬ t + j < t by omega, show t + j < 2 * t by omega, show ¬ 2 * t + i < t by omega,
      show ¬ 2 * t + i < 2 * t by omega, gadj, mask, hy, hi, hj, ind, show t + j - t = j by omega,
      show 2 * t + i - 2 * t = i by omega]
  · rw [gamma_gadj t x y _ _ (by omega) (by omega)]
    simp [gdec, hi, show ¬ 2 * t + i < t by omega, show ¬ 2 * t + i < 2 * t by omega, gadj, ind,
      show 2 * t + i - 2 * t = i by omega]

theorem gamma_symm (t : Nat) (x y : Nat → Nat → Bool) (a b : Nat) : gamma t x y a b = gamma t x y b a := by
  unfold gamma; exact (gamma_simple t x y).1 a b

/-- The base graph has a (k-1)-clique iff Γ_t has a triangle iff x and y intersect. -/
theorem base_clique (k t : Nat) (x y : Nat → Nat → Bool) (hk : 4 ≤ k) :
    HasClique (3 * t + (k - 4)) (fun a b => basePub t (k - 4) a b + gA t x a b + gB t y a b) (k - 1) ↔
    ∃ i j, i < t ∧ j < t ∧ x i j = true ∧ y i j = true := by
  have gs := (gamma_simple t x y).1
  have hcU : cnt (3 * t + (k - 4)) (fun a => !decide (a < 3 * t)) = k - 4 := by
    have := cnt_compl (3 * t + (k - 4)) (fun a => decide (a < 3 * t))
    rw [cnt_lt_count _ _ (by omega)] at this; omega
  constructor
  · rintro ⟨C, hCp, hcnt, hadj⟩
    have hsp := cnt_split (3 * t + (k - 4)) C (fun a => decide (a < 3 * t))
    have hle := cnt_mono_set (3 * t + (k - 4)) (fun a => C a && !decide (a < 3 * t)) (fun a => !decide (a < 3 * t))
      (fun a _ h => by simp at h ⊢; exact h.2)
    obtain ⟨a, b, c, ha, hb, hc, ca, cb, cc, hab, hbc, hac⟩ :=
      three_distinct (3 * t + (k - 4)) (fun a => C a && decide (a < 3 * t)) (by omega)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ca cb cc
    have e : ∀ a b, a < 3 * t → b < 3 * t → C a = true → C b = true → a ≠ b → 1 ≤ gamma t x y a b := by
      intro a b ha hb h1 h2 hne
      have := hadj a b h1 h2 hne
      simp only [base_eq, Uj_inside t (k - 4) a b ha hb] at this
      exact this
    exact (gamma_triangle_nat t x y).mp ⟨a, b, c, ca.2, cb.2, cc.2, e a b ca.2 cb.2 ca.1 cb.1 hab,
      e b c cb.2 cc.2 cb.1 cc.1 hbc, e a c ca.2 cc.2 ca.1 cc.1 hac⟩
  · rintro ⟨i, j, hi, hj, hx, hy⟩
    obtain ⟨e1, e2, e3⟩ := gamma_tri_edges t x y i j hi hj hx hy
    let C : Nat → Bool := fun a => a == i || a == t + j || a == 2 * t + i ||
      (decide (3 * t ≤ a) && decide (a < 3 * t + (k - 4)))
    refine ⟨C, fun a h => ?_, ?_, ?_⟩
    · simp only [C, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h; omega
    · have hsp := cnt_split (3 * t + (k - 4)) C (fun a => decide (a < 3 * t))
      have h3 := cnt_three (3 * t + (k - 4)) i (t + j) (2 * t + i) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (fun a => C a && decide (a < 3 * t))
        (by simp [C]; omega) (by simp [C]; omega) (by simp [C]; omega)
      have hU : cnt (3 * t + (k - 4)) (fun a => C a && !decide (a < 3 * t)) = k - 4 := by
        have : cnt (3 * t + (k - 4)) (fun a => C a && !decide (a < 3 * t))
            = cnt (3 * t + (k - 4)) (fun a => !decide (a < 3 * t)) := by
          unfold cnt; apply lsum_congr; intro a ha
          have ha := List.mem_range.mp ha
          by_cases h : a < 3 * t
          · simp [h]
          · simp [C, h, show 3 * t ≤ a by omega, ha, ind]
        rw [this, hcU]
      omega
    · intro a b ha hb hab
      show 1 ≤ basePub t (k - 4) a b + gA t x a b + gB t y a b
      rw [base_eq]
      simp only [C, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at ha hb
      have hap : a < 3 * t + (k - 4) := by omega
      have hbp : b < 3 * t + (k - 4) := by omega
      by_cases hU : 3 * t ≤ a ∨ 3 * t ≤ b
      · have : 1 ≤ Uj t (k - 4) a b := by
          unfold Uj ind
          have hab' : (a != b) = true := by simp [hab]
          rw [hab']
          simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
          (repeat' split) <;> omega
        omega
      · have : 1 ≤ gamma t x y a b := by
          rcases ha with ((ha | ha) | ha) | ha <;> rcases hb with ((hb | hb) | hb) | hb <;>
            (try omega) <;> subst ha hb <;> (try exact e1) <;> (try exact e2) <;> (try exact e3) <;>
            (try (rw [gamma_symm]; exact e1)) <;> (try (rw [gamma_symm]; exact e2)) <;> (try (rw [gamma_symm]; exact e3)) <;> omega
        omega


/-! ### Lemma 27 for deterministic algorithms -/

namespace Prot
/-- Post-process the output of a protocol (no communication). -/
def mapOut {IA IB α β : Type} (g : α → β) : Prot IA IB α → Prot IA IB β
  | ret r => ret (g r)
  | sendA f k => sendA f (fun bit => mapOut g (k bit))
  | sendB h k => sendB h (fun bit => mapOut g (k bit))

theorem mapOut_spec {IA IB α β : Type} (g : α → β) (a : IA) (b : IB) (P : Prot IA IB α) :
    exec a b (mapOut g P) = g (exec a b P) ∧ bits a b (mapOut g P) = bits a b P := by
  induction P with
  | ret r => exact ⟨rfl, rfl⟩
  | sendA f k ih => simp only [mapOut, exec, bits]; exact ⟨(ih _).1, by rw [(ih _).2]⟩
  | sendB h k ih => simp only [mapOut, exec, bits]; exact ⟨(ih _).1, by rw [(ih _).2]⟩
end Prot

/-- Lemma 27 (deterministic, no cited ingredient). Let k ≥ 4, t ≥ 1, p = 3t + (k - 4) and
    M ≥ k²p, so n = p + M. Any deterministic cut-query algorithm that returns λ_k on every
    gadget L_{k,M}(F_{x,y}) (simple graphs on n vertices, by `liG_shape` and `base_hyp`) asks,
    on some input, a number q of queries with
      t² ≤ 2p(⌈log₂ p⌉ + 1) + 2(2⌈log₂ n⌉ + 1)·q,
    i.e. q = Ω(t² / log n) = Ω_k(n² / log n) when M = Θ(k²p). -/
theorem kge4_det_lb (k t M : Nat) (hk : 4 ≤ k) (ht : 1 ≤ t)
    (hM : k * k * (3 * t + (k - 4)) ≤ M) (A : Alg Nat)
    (hA : ∀ x y, IsMinK (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y)) k
      (Alg.run (q (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y))) A)) :
    ∃ x y, t * t ≤ 2 * ((3 * t + (k - 4)) * (clog (3 * t + (k - 4)) + 1)) +
      2 * (2 * clog (3 * t + (k - 4) + M) + 1) *
        Alg.cost (q (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y))) A := by
  generalize hp : 3 * t + (k - 4) = p at hA hM ⊢
  let c1 := clog p + 1
  let c := 2 * clog (p + M) + 1
  let P : Prot (Nat → Nat → Nat) (Nat → Nat → Nat) Nat :=
    Prot.vecA (fun F => degF p F) c1 p (fun gA => Prot.vecB (fun F => degF p F) c1 p (fun gB =>
      simQ c (q (p + M) (liPub p M (basePub t (k - 4)) (fun v => degF p (basePub t (k - 4)) v + gA v + gB v)))
        (fun F => q (p + M) (rb p F)) (fun F => q (p + M) (rb p F)) A))
  let Pb := Prot.mapOut (fun m => m + c2 (k - 1) == 2 * ((k - 1) * p)) P
  let Pv := Prot.comap (fun v => gA t (dec t v)) (fun w => gB t (dec t w)) Pb
  have hspec : ∀ x y, Prot.exec (gA t x) (gB t y) P =
      Alg.run (q (p + M) (liG p M (basePub t (k - 4)) (gA t x) (gB t y))) A ∧
      Prot.bits (gA t x) (gB t y) P = 2 * (p * c1) + 2 * c *
        Alg.cost (q (p + M) (liG p M (basePub t (k - 4)) (gA t x) (gB t y))) A :=
    fun x y => li_protocol p M (basePub t (k - 4)) A (gA t x) (gB t y) (gA_le t x) (gB_le t y)
  have hPv : ∀ v w, Prot.exec v w Pv = true ↔ ∃ i, i < t * t ∧ v i = true ∧ w i = true := by
    intro v w
    simp only [Pv, Pb]
    rw [(Prot.comap_spec _ _ v w _).1, (Prot.mapOut_spec _ _ _ P).1, (hspec _ _).1, beq_iff_eq]
    have hH := base_hyp k t M (dec t v) (dec t w) hk ht (by rw [hp]; exact hM)
    rw [hp] at hH
    rw [li_threshold k p M _ _ _ hH _ (hA _ _), ← hp, base_clique k t _ _ hk, dec_meet]
  obtain ⟨v, hv⟩ := disj_lower (t * t) Pv hPv
  refine ⟨dec t v, dec t (fun i => !v i), ?_⟩
  simp only [Pv, Pb] at hv
  rw [(Prot.comap_spec _ _ v _ _).2, (Prot.mapOut_spec _ _ _ P).2, (hspec _ _).2] at hv
  exact hv


/-! ## Part O: remaining deterministic statements
  * partition output in Lemma 27 (`kge4_det_lb_part`);
  * the O(n²) upper bound of Proposition 29 (`weighted_ub`);
  * connectivity of Li's gadget (Lemma 25) (`liG_connected`);
  * the reduction of Proposition 22 (`iso_lambda3`). -/

/-- Ask the cut queries S 0, ..., S (N-1). -/
def askAll (S : Nat → (Nat → Bool)) : Nat → Alg (Nat → Nat)
  | 0 => .ret (fun _ => 0)
  | m + 1 => Alg.bind (askAll S m) (fun g => .ask (S m) (fun r => .ret (fun v => if v = m then r else g v)))

theorem askAll_spec (O : (Nat → Bool) → Nat) (S : Nat → (Nat → Bool)) : ∀ m,
    Alg.run O (askAll S m) = (fun v => if v < m then O (S v) else 0) ∧ Alg.cost O (askAll S m) = m := by
  intro m
  induction m with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    simp only [askAll, Alg.run_bind, Alg.cost_bind, ih.1, ih.2, Alg.run, Alg.cost]
    refine ⟨?_, by simp [Alg.cost]⟩
    funext v
    by_cases h1 : v = m
    · subst h1; simp
    · by_cases h2 : v < m
      · simp [h1, h2, show v < m + 1 by omega]
      · simp [h1, h2, show ¬ v < m + 1 by omega]

/-! ### Partition output: k shore queries recover the value -/

/-- From a labelled k-partition, k shore queries and `shore_sum` give its cost. -/
def valueOf (k : Nat) (lab : Nat → Nat) : Alg Nat :=
  Alg.bind (askAll (fun i => part lab i) k) (fun g => .ret (lsum (List.range k) g / 2))

theorem valueOf_spec (N : Nat) (w : Nat → Nat → Nat) (k : Nat) (lab : Nat → Nat)
    (hlab : ∀ u, u < N → lab u < k) :
    Alg.run (q N w) (valueOf k lab) = cost N w lab ∧ Alg.cost (q N w) (valueOf k lab) = k := by
  unfold valueOf
  rw [Alg.run_bind, Alg.cost_bind, (askAll_spec _ _ k).1, (askAll_spec _ _ k).2]
  refine ⟨?_, rfl⟩
  show lsum (List.range k) (fun v => if v < k then q N w (part lab v) else 0) / 2 = cost N w lab
  rw [lsum_congr _ _ (fun i => q N w (part lab i)) (fun i hi => by simp [List.mem_range.mp hi]),
    shore_sum N w k lab hlab]
  omega

/-- Lemma 27 for algorithms that output an optimum k-partition: k more queries. -/
theorem kge4_det_lb_part (k t M : Nat) (hk : 4 ≤ k) (ht : 1 ≤ t)
    (hM : k * k * (3 * t + (k - 4)) ≤ M) (A : Alg (Nat → Nat))
    (hA : ∀ x y, ValidK (3 * t + (k - 4) + M) k
        (Alg.run (q (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y))) A) ∧
      ∀ lab, ValidK (3 * t + (k - 4) + M) k lab →
        cost (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y))
          (Alg.run (q (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y))) A)
        ≤ cost (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y)) lab) :
    ∃ x y, t * t ≤ 2 * ((3 * t + (k - 4)) * (clog (3 * t + (k - 4)) + 1)) +
      2 * (2 * clog (3 * t + (k - 4) + M) + 1) *
        (Alg.cost (q (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y))) A + k) := by
  let A' := Alg.bind A (fun lab => valueOf k lab)
  have hspec : ∀ x y,
      Alg.run (q (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y))) A'
        = cost (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y))
          (Alg.run (q (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y))) A) ∧
      Alg.cost (q (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y))) A'
        = Alg.cost (q (3 * t + (k - 4) + M) (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y))) A + k := by
    intro x y
    simp only [A']
    rw [Alg.run_bind, Alg.cost_bind]
    have := valueOf_spec _ (liG (3 * t + (k - 4)) M (basePub t (k - 4)) (gA t x) (gB t y)) k _ (hA x y).1.1
    exact ⟨this.1, by rw [this.2]⟩
  obtain ⟨x, y, h⟩ := kge4_det_lb k t M hk ht hM A' (fun x y => by
    rw [(hspec x y).1]
    exact ⟨⟨_, (hA x y).1, rfl⟩, (hA x y).2⟩)
  refine ⟨x, y, ?_⟩
  rw [(hspec x y).2] at h
  exact h

/-! ### Proposition 29, upper bound: n + n² cut queries reconstruct the weights -/

theorem q_pair (n : Nat) (w : Nat → Nat → Nat) (hsym : ∀ x y, w x y = w y x) (_hloop : ∀ x, w x x = 0)
    (u v : Nat) (hu : u < n) (hv : v < n) (huv : u ≠ v) :
    q n w (union (sing u) (sing v)) + 4 * w u v = q n w (sing u) + q n w (sing v) := by
  have h := cross_query n w (sing u) (sing v) (fun x _ => by
    simp only [sing]; by_cases h : x = u
    · subst h; simp [huv]
    · simp [h])
  rw [e_sing n w hsym u v hu hv huv] at h
  omega

/-- Ask all singleton cuts and all pair cuts, and decode the weights. -/
def reconAlg (n : Nat) : Alg (Nat → Nat → Nat) :=
  Alg.bind (askAll sing n) (fun a =>
    Alg.bind (askAll (fun j => union (sing (j / n)) (sing (j % n))) (n * n)) (fun b =>
      .ret (fun u v => if u < n ∧ v < n ∧ u ≠ v then (a u + a v - b (n * u + v)) / 4 else 0)))

theorem reconAlg_spec (n : Nat) (w : Nat → Nat → Nat) (hsym : ∀ x y, w x y = w y x) (hloop : ∀ x, w x x = 0) :
    (∀ u v, u < n → v < n → Alg.run (q n w) (reconAlg n) u v = w u v) ∧
    Alg.cost (q n w) (reconAlg n) = n + n * n := by
  unfold reconAlg
  simp only [Alg.run_bind, Alg.cost_bind, (askAll_spec _ _ n).1, (askAll_spec _ _ n).2,
    (askAll_spec _ _ (n * n)).1, (askAll_spec _ _ (n * n)).2, Alg.run, Alg.cost]
  refine ⟨fun u v hu hv => ?_, by omega⟩
  by_cases huv : u = v
  · subst huv; simp [hloop]
  · have hj : n * u + v < n * n := by
      have := Nat.mul_le_mul_left n (show u + 1 ≤ n by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    have h1 : (n * u + v) / n = u := by rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hv]; omega
    have h2 : (n * u + v) % n = v := by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hv]
    simp only [hu, hv, hj, h1, h2, ite_true, true_and, ne_eq, huv, not_false_eq_true]
    have := q_pair n w hsym hloop u v hu hv huv
    omega

theorem exists_min (P : Nat → Prop) (h : ∃ m, P m) : ∃ m, P m ∧ ∀ m', P m' → m ≤ m' := by
  obtain ⟨m, hm⟩ := h
  induction m using Nat.strongRecOn with
  | _ m ih =>
    by_cases hs : ∃ m', m' < m ∧ P m'
    · obtain ⟨m', h1, h2⟩ := hs; exact ih m' h1 h2
    · refine ⟨m, hm, fun m' hm' => ?_⟩
      apply Classical.byContradiction; intro hl
      exact hs ⟨m', by omega, hm'⟩

/-- λ₃ of w on 0..n-1 (any value if n < 3). -/
noncomputable def lam3 (n : Nat) (w : Nat → Nat → Nat) : Nat := Classical.epsilon (fun m => IsMin3 n w m)

theorem lam3_spec (n : Nat) (w : Nat → Nat → Nat) (hn : 3 ≤ n) : IsMin3 n w (lam3 n w) := by
  apply Classical.epsilon_spec
  obtain ⟨m, ⟨lab, hv, hc⟩, hmin⟩ := exists_min (fun m => ∃ lab, Valid3 n lab ∧ cost n w lab = m)
    ⟨_, labUV 0 1, labUV_valid n 0 1 hn (by omega) (by omega) (by omega), rfl⟩
  exact ⟨m, ⟨lab, hv, hc⟩, fun lab' hv' => hmin _ ⟨lab', hv', rfl⟩⟩

/-- Proposition 29, upper bound: the algorithm that reconstructs the weights with n + n² cut
    queries and then computes λ₃ locally is correct on every symmetric weighting. -/
theorem weighted_ub (n : Nat) (hn : 3 ≤ n) (w : Nat → Nat → Nat) (hsym : ∀ x y, w x y = w y x)
    (hloop : ∀ x, w x x = 0) :
    IsMin3 n w (Alg.run (q n w) (Alg.bind (reconAlg n) (fun w' => .ret (lam3 n w')))) ∧
    Alg.cost (q n w) (Alg.bind (reconAlg n) (fun w' => .ret (lam3 n w'))) = n + n * n := by
  rw [Alg.run_bind, Alg.cost_bind]
  obtain ⟨hr, hc⟩ := reconAlg_spec n w hsym hloop
  refine ⟨?_, by rw [hc]; rfl⟩
  generalize Alg.run (q n w) (reconAlg n) = w' at hr
  have hcost : ∀ lab, cost n w' lab = cost n w lab := by
    intro lab; unfold cost; apply D_congr; intro u v hu hv; rw [hr u v hu hv]
  obtain ⟨⟨lab, hv, hcl⟩, hmin⟩ := lam3_spec n w' hn
  exact ⟨⟨lab, hv, by rw [← hcost]; exact hcl⟩, fun lab' hv' => by rw [← hcost]; exact hmin lab' hv'⟩

/-! ### Lemma 25: Li's gadget is connected -/

theorem liG_connected (p M : Nat) (Fp Fa Fb : Nat → Nat → Nat) (hM : 1 ≤ M) (hpM : p ≤ M)
    (hsym : ∀ u v, Fp u v + Fa u v + Fb u v = Fp v u + Fa v u + Fb v u)
    (hloop : ∀ u, Fp u u + Fa u u + Fb u u = 0)
    (hle : ∀ u v, Fp u v + Fa u v + Fb u v ≤ 1) :
    ∀ u v, u < p + M → v < p + M → Reach (liG p M Fp Fa Fb) u v := by
  have shape := liG_shape p M Fp Fa Fb hpM hsym hloop hle
  have hto : ∀ u, u < p + M → Reach (liG p M Fp Fa Fb) u p := by
    intro u hu
    by_cases hup : u = p
    · subst hup; exact Reach.refl _
    · refine Reach.step (Reach.refl u) ?_
      by_cases hb : u < p
      · -- base vertex: attached to p since d_F(u) ≤ p - 1
        have hd : degF p (fun a b => Fp a b + Fa a b + Fb a b) u ≤ p - 1 := by
          unfold degF
          rw [← rowK p u hb]
          apply lsum_mono; intro y _
          by_cases h : u = y
          · subst h; show Fp u u + Fa u u + Fb u u ≤ _; rw [hloop]; exact Nat.zero_le _
          · have := hle u y; simp [ind, h]; exact this
        have : 1 ≤ att p (degF p (fun a b => Fp a b + Fa a b + Fb a b)) u p := by
          have e : (decide (u < p) && decide (p ≤ p) &&
              decide (p < p + (p - degF p (fun a b => Fp a b + Fa a b + Fb a b) u))) = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
          unfold att; rw [e]; exact Nat.le_refl 1
        unfold liG liPub; omega
      · rw [shape.2.2.2.1 u p (by omega) (Nat.le_refl _) hu (by omega) hup]; exact Nat.le_refl 1
  intro u v hu hv
  exact reach_trans _ (hto u hu) (reach_symm _ shape.1 (hto v hv))

/-! ### Proposition 22: adding an isolated vertex -/

/-- F restricted to 0..n-1, as a graph on 0..n whose vertex n is isolated. -/
def addIso (n : Nat) (F : Nat → Nat → Nat) (u v : Nat) : Nat := if u < n ∧ v < n then F u v else 0

theorem cost_zero_edge (N : Nat) (w : Nat → Nat → Nat) (lab : Nat → Nat) (h : cost N w lab = 0)
    (a b : Nat) (ha : a < N) (hb : b < N) (hw : 1 ≤ w a b) : lab a = lab b := by
  have := D_ge_term N (fun u v => ind (lab u != lab v) * w u v) a b ha hb
  unfold cost at h
  rw [h] at this
  apply Classical.byContradiction; intro hne
  simp [hne, ind] at this; omega

/-- Proposition 22, reduction: λ₃(F + isolated vertex) = 0 iff F is disconnected. Adjacency-array
    queries to `addIso n F` are answered by the same queries to F (and vertex n has no
    neighbours), so this transfers the connectivity lower bound. -/
theorem iso_lambda3 (n : Nat) (hn : 1 ≤ n) (F : Nat → Nat → Nat) (hsym : ∀ x y, F x y = F y x)
    (m : Nat) (hm : IsMinK (n + 1) (addIso n F) 3 m) :
    m = 0 ↔ ¬ ∀ u v, u < n → v < n → Reach (addIso n F) u v := by
  classical
  have hGsym : ∀ x y, addIso n F x y = addIso n F y x := by
    intro x y; unfold addIso; by_cases h : x < n ∧ y < n
    · simp [h, show y < n ∧ x < n from ⟨h.2, h.1⟩, hsym x y]
    · have : ¬ (y < n ∧ x < n) := fun h' => h ⟨h'.2, h'.1⟩
      simp only [h, this, ite_false]
  have hGe : ∀ a b, 1 ≤ addIso n F a b → a < n ∧ b < n := by
    intro a b h; unfold addIso at h; split at h
    · assumption
    · omega
  obtain ⟨⟨lab0, hv0, hc0⟩, hmin⟩ := hm
  constructor
  · intro h0 hconn
    rw [← hc0] at h0
    have hall : ∀ x, x < n → lab0 x = lab0 0 := by
      intro x hx
      have hr := hconn 0 x (by omega) hx
      suffices ∀ a b, Reach (addIso n F) a b → lab0 b = lab0 a from (this 0 x hr)
      intro a b hab
      induction hab with
      | refl => rfl
      | @step v w _ hvw ih =>
        have := hGe v w hvw
        rw [← ih]; exact (cost_zero_edge (n + 1) _ lab0 h0 v w (by omega) (by omega) hvw).symm
    obtain ⟨a, ha, la⟩ := hv0.2 0 (by omega)
    obtain ⟨b, hb, lb⟩ := hv0.2 1 (by omega)
    obtain ⟨c, hc, lc⟩ := hv0.2 2 (by omega)
    have g : ∀ z, z < n + 1 → lab0 z = lab0 0 ∨ lab0 z = lab0 n := by
      intro z hz
      by_cases h : z < n
      · left; exact hall z h
      · right; rw [show z = n by omega]
    rcases g a ha with h1 | h1 <;> rcases g b hb with h2 | h2 <;> rcases g c hc with h3 | h3 <;> omega
  · intro hnc
    apply Classical.byContradiction; intro hm0
    -- a component that is not everything
    have : ∃ u v, u < n ∧ v < n ∧ ¬ Reach (addIso n F) u v := by
      apply Classical.byContradiction; intro h
      apply hnc; intro u v hu hv
      apply Classical.byContradiction; intro h'
      exact h ⟨u, v, hu, hv, h'⟩
    obtain ⟨u, v, hu, hv, huv⟩ := this
    let lab : Nat → Nat := fun x => if x = n then 2 else if Reach (addIso n F) u x then 0 else 1
    have hval : ValidK (n + 1) 3 lab := by
      refine ⟨fun y _ => by simp only [lab]; split <;> (try split) <;> omega, fun c hc => ?_⟩
      rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
      · exact ⟨u, by omega, by simp [lab, show u ≠ n by omega, Reach.refl]⟩
      · exact ⟨v, by omega, by simp [lab, show v ≠ n by omega, huv]⟩
      · exact ⟨n, by omega, by simp [lab]⟩
    have hzero : cost (n + 1) (addIso n F) lab = 0 := by
      unfold cost
      rw [D_congr (n + 1) _ (fun _ _ => 0) (fun a b _ _ => ?_), D_zero]
      by_cases hw : 1 ≤ addIso n F a b
      · have hab := hGe a b hw
        have e1 : Reach (addIso n F) u a ↔ Reach (addIso n F) u b :=
          ⟨fun h => Reach.step h hw, fun h => Reach.step h (by rw [hGsym]; exact hw)⟩
        have : lab a = lab b := by
          simp only [lab, show a ≠ n by omega, show b ≠ n by omega, ite_false]
          by_cases h : Reach (addIso n F) u a
          · simp [h, e1.mp h]
          · simp [h, show ¬ Reach (addIso n F) u b from fun h' => h (e1.mpr h')]
        simp [this, ind]
      · have : addIso n F a b = 0 := by omega
        simp [this]
    have := hmin lab hval
    omega


/-! ## Part P: Corollary 28 (the singleton threshold) for deterministic algorithms -/

/-! ### A generic form of the Lemma 27 lower bound -/

theorem det_lb_generic (k t p M : Nat) (Fp : Nat → Nat → Nat)
    (hH : ∀ x y, LiHyp k p M Fp (gA t x) (gB t y))
    (hcl : ∀ x y, HasClique p (fun a b => Fp a b + gA t x a b + gB t y a b) (k - 1) ↔
      ∃ i j, i < t ∧ j < t ∧ x i j = true ∧ y i j = true)
    (A : Alg Nat)
    (hA : ∀ x y, IsMinK (p + M) (liG p M Fp (gA t x) (gB t y)) k
      (Alg.run (q (p + M) (liG p M Fp (gA t x) (gB t y))) A)) :
    ∃ x y, t * t ≤ 2 * (p * (clog p + 1)) +
      2 * (2 * clog (p + M) + 1) * Alg.cost (q (p + M) (liG p M Fp (gA t x) (gB t y))) A := by
  let c1 := clog p + 1
  let c := 2 * clog (p + M) + 1
  let P : Prot (Nat → Nat → Nat) (Nat → Nat → Nat) Nat :=
    Prot.vecA (fun F => degF p F) c1 p (fun gA => Prot.vecB (fun F => degF p F) c1 p (fun gB =>
      simQ c (q (p + M) (liPub p M Fp (fun v => degF p Fp v + gA v + gB v)))
        (fun F => q (p + M) (rb p F)) (fun F => q (p + M) (rb p F)) A))
  let Pb := Prot.mapOut (fun m => m + c2 (k - 1) == 2 * ((k - 1) * p)) P
  let Pv := Prot.comap (fun v => gA t (dec t v)) (fun w => gB t (dec t w)) Pb
  have hspec : ∀ x y, Prot.exec (gA t x) (gB t y) P =
      Alg.run (q (p + M) (liG p M Fp (gA t x) (gB t y))) A ∧
      Prot.bits (gA t x) (gB t y) P = 2 * (p * c1) + 2 * c *
        Alg.cost (q (p + M) (liG p M Fp (gA t x) (gB t y))) A :=
    fun x y => li_protocol p M Fp A (gA t x) (gB t y) (gA_le t x) (gB_le t y)
  have hPv : ∀ v w, Prot.exec v w Pv = true ↔ ∃ i, i < t * t ∧ v i = true ∧ w i = true := by
    intro v w
    simp only [Pv, Pb]
    rw [(Prot.comap_spec _ _ v w _).1, (Prot.mapOut_spec _ _ _ P).1, (hspec _ _).1, beq_iff_eq,
      li_threshold k p M _ _ _ (hH _ _) _ (hA _ _), hcl, dec_meet]
  obtain ⟨v, hv⟩ := disj_lower (t * t) Pv hPv
  refine ⟨dec t v, dec t (fun i => !v i), ?_⟩
  simp only [Pv, Pb] at hv
  rw [(Prot.comap_spec _ _ v _ _).2, (Prot.mapOut_spec _ _ _ P).2, (hspec _ _).2] at hv
  exact hv

/-! ### The base graph Γ_t + P₃ (a public path on 3t, 3t+1, 3t+2) -/

def Pth (t : Nat) (a b : Nat) : Nat :=
  ind ((a == 3 * t && b == 3 * t + 1) || (a == 3 * t + 1 && b == 3 * t) ||
       (a == 3 * t + 1 && b == 3 * t + 2) || (a == 3 * t + 2 && b == 3 * t + 1))

def pathPub (t : Nat) (a b : Nat) : Nat := gPub t a b + Pth t a b

theorem Pth_pos (t a b : Nat) (h : 1 ≤ Pth t a b) :
    (a = 3 * t ∧ b = 3 * t + 1) ∨ (a = 3 * t + 1 ∧ b = 3 * t) ∨
    (a = 3 * t + 1 ∧ b = 3 * t + 2) ∨ (a = 3 * t + 2 ∧ b = 3 * t + 1) := by
  unfold Pth ind at h; split at h
  · rename_i hc; simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc; omega
  · omega

theorem path_eq (t : Nat) (x y : Nat → Nat → Bool) (a b : Nat) :
    pathPub t a b + gA t x a b + gB t y a b = gamma t x y a b + Pth t a b := by
  unfold pathPub gamma; omega

theorem path_hyp (t M : Nat) (x y : Nat → Nat → Bool) (hM : 16 * (3 * t + 3) ≤ M) :
    LiHyp 4 (3 * t + 3) M (pathPub t) (gA t x) (gB t y) := by
  obtain ⟨gs, gl, gle⟩ := gamma_simple t x y
  have ps : ∀ a b, Pth t a b = Pth t b a := by
    intro a b; unfold Pth ind
    by_cases h1 : a = 3 * t <;> by_cases h2 : a = 3 * t + 1 <;> by_cases h3 : a = 3 * t + 2 <;>
    by_cases h4 : b = 3 * t <;> by_cases h5 : b = 3 * t + 1 <;> by_cases h6 : b = 3 * t + 2 <;>
      simp [h1, h2, h3, h4, h5, h6] <;> omega
  have pl : ∀ a, Pth t a a = 0 := by
    intro a; unfold Pth ind; split
    · rename_i hc; simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc; omega
    · rfl
  have ple : ∀ a b, Pth t a b ≤ 1 := by intro a b; unfold Pth ind; split <;> omega
  refine ⟨fun a b => ?_, fun a => ?_, fun a b => ?_, by omega, by omega, by omega⟩
  · rw [path_eq, path_eq, ps a b]; unfold gamma; rw [gs a b]
  · rw [path_eq, pl a]; unfold gamma; rw [gl a]
  · rw [path_eq]; unfold gamma
    have := gle a b
    by_cases h : 1 ≤ gPub t a b + gA t x a b + gB t y a b
    · have hs := gamma_support t x y a b h
      have : Pth t a b = 0 := by
        apply Classical.byContradiction; intro hne
        have := Pth_pos t a b (by omega); omega
      omega
    · have := ple a b; omega

theorem path_clique (t : Nat) (x y : Nat → Nat → Bool) :
    HasClique (3 * t + 3) (fun a b => pathPub t a b + gA t x a b + gB t y a b) (4 - 1) ↔
    ∃ i j, i < t ∧ j < t ∧ x i j = true ∧ y i j = true := by
  have gs := gamma_symm t x y
  constructor
  · rintro ⟨C, hCp, hcnt, hadj⟩
    obtain ⟨a, b, c, ha, hb, hc, ca, cb, cc, hab, hbc, hac⟩ := three_distinct (3 * t + 3) C (by omega)
    have e : ∀ u v, C u = true → C v = true → u ≠ v → 1 ≤ gamma t x y u v + Pth t u v := by
      intro u v hu hv huv
      have h : 1 ≤ pathPub t u v + gA t x u v + gB t y u v := hadj u v hu hv huv
      rw [path_eq] at h; exact h
    have g : ∀ u v, u < 3 * t → C u = true → C v = true → u ≠ v → 1 ≤ gamma t x y u v ∧ v < 3 * t := by
      intro u v hu h1 h2 huv
      have := e u v h1 h2 huv
      by_cases hg : 1 ≤ gamma t x y u v
      · exact ⟨hg, (gamma_support t x y u v hg).2⟩
      · have := Pth_pos t u v (by omega); omega
    by_cases hA : a < 3 * t
    · obtain ⟨g1, hb'⟩ := g a b hA ca cb hab
      obtain ⟨g2, hc'⟩ := g b c hb' cb cc hbc
      obtain ⟨g3, _⟩ := g a c hA ca cc hac
      exact (gamma_triangle_nat t x y).mp ⟨a, b, c, hA, hb', hc', g1, g2, g3⟩
    · -- a is on the path, so b and c are too, and the path has no triangle
      have onp : ∀ u v, ¬ u < 3 * t → C u = true → C v = true → u ≠ v → 1 ≤ Pth t u v := by
        intro u v hu h1 h2 huv
        have := e u v h1 h2 huv
        by_cases hg : 1 ≤ gamma t x y u v
        · have := (gamma_support t x y u v hg).1; omega
        · omega
      have p1 := Pth_pos t a b (onp a b hA ca cb hab)
      have hB : ¬ b < 3 * t := by omega
      have p2 := Pth_pos t b c (onp b c hB cb cc hbc)
      have p3 := Pth_pos t a c (onp a c hA ca cc hac)
      omega
  · rintro ⟨i, j, hi, hj, hx, hy⟩
    obtain ⟨e1, e2, e3⟩ := gamma_tri_edges t x y i j hi hj hx hy
    let C : Nat → Bool := fun a => a == i || a == t + j || a == 2 * t + i
    refine ⟨C, fun a h => ?_, ?_, ?_⟩
    · simp only [C, Bool.or_eq_true, beq_iff_eq] at h; omega
    · exact cnt_three _ i (t + j) (2 * t + i) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) C (by simp [C]) (by simp [C]) (by simp [C])
    · intro a b ha hb hab
      show 1 ≤ pathPub t a b + gA t x a b + gB t y a b
      rw [path_eq]
      simp only [C, Bool.or_eq_true, beq_iff_eq] at ha hb
      have : 1 ≤ gamma t x y a b := by
        rcases ha with (ha | ha) | ha <;> rcases hb with (hb | hb) | hb <;>
          (try omega) <;> subst ha hb <;> (try exact e1) <;> (try exact e2) <;> (try exact e3) <;>
          (try (rw [gs]; exact e1)) <;> (try (rw [gs]; exact e2)) <;> (try (rw [gs]; exact e3)) <;> omega
      omega

/-- Lemma 27 with the path base, k = 4: the lower bound used in Corollary 28. -/
theorem path_det_lb (t M : Nat) (hM : 16 * (3 * t + 3) ≤ M) (A : Alg Nat)
    (hA : ∀ x y, IsMinK (3 * t + 3 + M) (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y)) 4
      (Alg.run (q (3 * t + 3 + M) (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y))) A)) :
    ∃ x y, t * t ≤ 2 * ((3 * t + 3) * (clog (3 * t + 3) + 1)) +
      2 * (2 * clog (3 * t + 3 + M) + 1) *
        Alg.cost (q (3 * t + 3 + M) (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y))) A :=
  det_lb_generic 4 t (3 * t + 3) M (pathPub t) (fun x y => path_hyp t M x y hM) (path_clique t) A hA


/-! ### The gadget H = L_{4,M}(Γ_t + P₃): an optimum with exactly three singleton parts -/

theorem D_even (n : Nat) (f : Nat → Nat → Nat) (hs : ∀ u v, f u v = f v u) (hd : ∀ u, f u u = 0) :
    D n f = 2 * D n (fun u v => ind (decide (u < v)) * f u v) := by
  have : D n f = D n (fun u v => ind (decide (u < v)) * f u v) + D n (fun u v => ind (decide (v < u)) * f v u) := by
    rw [← D_add]; apply D_congr; intro u v _ _
    by_cases h : u < v
    · simp [h, show ¬ v < u by omega, ind]
    · by_cases h' : v < u
      · simp [h, h', ind, hs u v]
      · simp [h, h', show u = v by omega, hd, ind]
  rw [this, D_swap n (fun u v => ind (decide (u < v)) * f u v)]; omega

theorem cost_even (n : Nat) (w : Nat → Nat → Nat) (hs : ∀ u v, w u v = w v u) (hl : ∀ u, w u u = 0)
    (lab : Nat → Nat) : cost n w lab % 2 = 0 := by
  unfold cost
  rw [D_even n _ (fun u v => by
    show ind (lab u != lab v) * w u v = ind (lab v != lab u) * w v u
    rw [hs u v]
    by_cases h : lab u = lab v
    · rw [h]
    · have h' : lab v ≠ lab u := fun e => h e.symm
      have e1 : (lab u != lab v) = true := by simp [h]
      have e2 : (lab v != lab u) = true := by simp [h']
      rw [e1, e2]) (fun u => by simp [hl])]
  omega

/-- Isolate a, b, c as parts 1, 2, 3. -/
def iso3 (a b c : Nat) (x : Nat) : Nat := if x = a then 1 else if x = b then 2 else if x = c then 3 else 0

def R3 (a b c : Nat) (x : Nat) : Bool := x == a || x == b || x == c

theorem ind_R3 (a b c x : Nat) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ind (R3 a b c x) = ind (x == a) + ind (x == b) + ind (x == c) := by
  unfold R3
  by_cases e1 : x = a
  · subst e1; simp [ind, hab, hac]
  · by_cases e2 : x = b
    · subst e2; simp [ind, e1, hbc]
    · by_cases e3 : x = c
      · subst e3; simp [ind, e1, e2]
      · simp [ind, e1, e2, e3]

theorem cnt_R3 (n a b c : Nat) (ha : a < n) (hb : b < n) (hc : c < n) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : cnt n (R3 a b c) = 3 := by
  unfold cnt
  rw [lsum_congr _ _ (fun x => ind (x == a) + ind (x == b) + ind (x == c))
    (fun x _ => ind_R3 a b c x hab hbc hac), lsum_add, lsum_add]
  have p1 := pick (fun _ => 1) a n ha
  have p2 := pick (fun _ => 1) b n hb
  have p3 := pick (fun _ => 1) c n hc
  simp only [Nat.mul_one] at p1 p2 p3
  omega

theorem row_R3 (n : Nat) (w : Nat → Nat → Nat) (a b c u : Nat) (ha : a < n) (hb : b < n) (hc : c < n)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    lsum (List.range n) (fun y => ind (R3 a b c y) * w u y) = w u a + w u b + w u c := by
  rw [lsum_congr _ _ (fun y => ind (y == a) * w u y + ind (y == b) * w u y + ind (y == c) * w u y)
    (fun y _ => by rw [ind_R3 a b c y hab hbc hac, Nat.add_mul, Nat.add_mul]), lsum_add, lsum_add,
    pick (fun y => w u y) a n ha, pick (fun y => w u y) b n hb, pick (fun y => w u y) c n hc]

theorem inner_R3 (n : Nat) (w : Nat → Nat → Nat) (hs : ∀ u v, w u v = w v u) (hl : ∀ u, w u u = 0)
    (a b c : Nat) (ha : a < n) (hb : b < n) (hc : c < n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    inner n w (R3 a b c) = 2 * (w a b + w b c + w a c) := by
  unfold inner
  have h : D n (fun x y => ind (R3 a b c x && R3 a b c y) * w x y) =
      D n (fun x y => ind (x == a) * (ind (R3 a b c y) * w x y)) +
      D n (fun x y => ind (x == b) * (ind (R3 a b c y) * w x y)) +
      D n (fun x y => ind (x == c) * (ind (R3 a b c y) * w x y)) := by
    rw [← D_add, ← D_add]; apply D_congr; intro x y _ _
    have e : ind (R3 a b c x && R3 a b c y) = ind (R3 a b c x) * ind (R3 a b c y) := by
      cases R3 a b c x <;> cases R3 a b c y <;> rfl
    rw [e, ind_R3 a b c x hab hbc hac]
    simp only [Nat.add_mul, Nat.mul_assoc]
  rw [h, D_left n a ha, D_left n b hb, D_left n c hc, row_R3 n w a b c a ha hb hc hab hbc hac,
    row_R3 n w a b c b ha hb hc hab hbc hac, row_R3 n w a b c c ha hb hc hab hbc hac, hl, hl, hl,
    hs b a, hs c a, hs c b]
  omega

/-- Cost of isolating three base vertices of the gadget: 2(3p - e(a,b,c)) (doubled). -/
theorem iso3_cost (p M : Nat) (Fp Fa Fb : Nat → Nat → Nat) (hpM : p ≤ M)
    (hsym : ∀ u v, Fp u v + Fa u v + Fb u v = Fp v u + Fa v u + Fb v u)
    (hloop : ∀ u, Fp u u + Fa u u + Fb u u = 0) (hle : ∀ u v, Fp u v + Fa u v + Fb u v ≤ 1)
    (a b c : Nat) (ha : a < p) (hb : b < p) (hc : c < p) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cost (p + M) (liG p M Fp Fa Fb) (iso3 a b c) +
      2 * ((Fp a b + Fa a b + Fb a b) + (Fp b c + Fa b c + Fb b c) + (Fp a c + Fa a c + Fb a c)) = 2 * (3 * p) := by
  have shape := liG_shape p M Fp Fa Fb hpM hsym hloop hle
  have hR : ∀ x, x < p + M → (iso3 a b c x = 0 ↔ R3 a b c x = false) := by
    intro x _; unfold iso3 R3
    by_cases e1 : x = a
    · simp [e1, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
    · by_cases e2 : x = b
      · simp [e1, e2, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
      · by_cases e3 : x = c <;> simp [e1, e2, e3, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
  have hRp : ∀ x, R3 a b c x = true → x < p := by
    intro x h; simp only [R3, Bool.or_eq_true, beq_iff_eq] at h; omega
  have hdeg : ∀ x, x < p + M → R3 a b c x = true → deg (p + M) (liG p M Fp Fa Fb) x = p :=
    fun x _ h => shape.2.2.2.2 x (hRp x h)
  have hid := li_cost_identity (p + M) (liG p M Fp Fa Fb) shape.1 (iso3 a b c) (R3 a b c) p hR hdeg
  have hown : own (p + M) (liG p M Fp Fa Fb) (iso3 a b c) (R3 a b c) = 0 := by
    unfold own
    rw [D_congr (p + M) _ (fun _ _ => 0) (fun x y _ _ => ?_), D_zero]
    by_cases hRx : R3 a b c x = true
    · by_cases hl : iso3 a b c x = iso3 a b c y
      · have hxy : x = y := by
          simp only [R3, Bool.or_eq_true, beq_iff_eq] at hRx
          unfold iso3 at hl
          by_cases e1 : y = a <;> by_cases e2 : y = b <;> by_cases e3 : y = c <;>
            simp [e1, e2, e3] at hl <;> (repeat' split at hl) <;> omega
        subst hxy; simp [shape.2.1]
      · simp [hl, ind]
    · simp [hRx, ind]
  rw [hown, cnt_R3 (p + M) a b c (by omega) (by omega) (by omega) hab hbc hac,
    inner_R3 (p + M) _ shape.1 shape.2.1 a b c (by omega) (by omega) (by omega) hab hbc hac,
    liG_base p M Fp Fa Fb a b ha hb, liG_base p M Fp Fa Fb b c hb hc, liG_base p M Fp Fa Fb a c ha hc] at hid
  omega

theorem iso3_valid (N a b c : Nat) (ha : a < N) (hb : b < N) (hc : c < N) (z : Nat) (hz : z < N)
    (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ValidK N 4 (iso3 a b c) := by
  refine ⟨fun y _ => by unfold iso3; (repeat' split) <;> omega, fun k hk => ?_⟩
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
  · exact ⟨z, hz, by simp [iso3, hza, hzb, hzc]⟩
  · exact ⟨a, ha, by simp [iso3]⟩
  · exact ⟨b, hb, by simp [iso3, Ne.symm hab]⟩
  · exact ⟨c, hc, by simp [iso3, Ne.symm hac, Ne.symm hbc]⟩

/-- Number of singleton parts among parts 0..k-1. -/
def nsing (N k : Nat) (lab : Nat → Nat) : Nat := cnt k (fun c => cnt N (part lab c) == 1)

theorem nsing_iso3 (N a b c : Nat) (ha : a < N) (hb : b < N) (hc : c < N) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) (hN : 5 ≤ N) : nsing N 4 (iso3 a b c) = 3 := by
  have pa : part (iso3 a b c) 1 = fun x => x == a := by
    funext x; unfold part iso3; by_cases e1 : x = a
    · simp [e1, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
    · simp [e1, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]; (repeat' split) <;> simp_all
  have pb : part (iso3 a b c) 2 = fun x => x == b := by
    funext x; unfold part iso3; by_cases e1 : x = a
    · simp [e1, hab, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
    · by_cases e2 : x = b
      · simp [e1, e2, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
      · simp [e1, e2, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]; split <;> simp_all
  have pc : part (iso3 a b c) 3 = fun x => x == c := by
    funext x; unfold part iso3; by_cases e1 : x = a
    · simp [e1, hac, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
    · by_cases e2 : x = b
      · simp [e1, e2, hbc, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
      · by_cases e3 : x = c <;> simp [e1, e2, e3, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
  have p0 : part (iso3 a b c) 0 = fun x => !R3 a b c x := by
    funext x; unfold part iso3 R3; by_cases e1 : x = a
    · simp [e1, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
    · by_cases e2 : x = b
      · simp [e1, e2, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
      · by_cases e3 : x = c <;> simp [e1, e2, e3, hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac]
  have one : ∀ u, u < N → cnt N (fun x => x == u) = 1 := by
    intro u hu
    have := pick (fun _ => 1) u N hu
    unfold cnt; simpa using this
  have c0 : cnt N (fun x => !R3 a b c x) = N - 3 := by
    have := cnt_compl N (R3 a b c); rw [cnt_R3 N a b c ha hb hc hab hbc hac] at this; omega
  unfold nsing
  show lsum (List.range 4) (fun k => ind (cnt N (part (iso3 a b c) k) == 1)) = 3
  rw [range4]
  rw [pa, pb, pc, p0, one a ha, one b hb, one c hc, c0]
  simp [ind, show N - 3 ≠ 1 by omega]


/-- The gadget H of Corollary 28 always has an optimum 4-partition with exactly three singleton
    parts, and λ₄(H) ≤ 3p - 2 (doubled: 2(3p - 2)). -/
theorem H_facts (t M : Nat) (hM : 16 * (3 * t + 3) ≤ M) (x y : Nat → Nat → Bool) (m : Nat)
    (hm : IsMinK (3 * t + 3 + M) (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y)) 4 m) :
    m ≤ 2 * (3 * (3 * t + 3) - 2) ∧
    ∃ lab, ValidK (3 * t + 3 + M) 4 lab ∧
      cost (3 * t + 3 + M) (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y)) lab = m ∧
      nsing (3 * t + 3 + M) 4 lab = 3 := by
  have hH := path_hyp t M x y hM
  obtain ⟨hsym, hloop, hle, _, _, _⟩ := hH
  have hpM : 3 * t + 3 ≤ M := by omega
  have shape := liG_shape (3 * t + 3) M (pathPub t) (gA t x) (gB t y) hpM hsym hloop hle
  have g0 : ∀ a b, 3 * t ≤ a → gamma t x y a b = 0 := by
    intro a b ha; apply Classical.byContradiction; intro h
    have := gamma_support t x y a b (by unfold gamma at h; omega); omega
  have F1 : pathPub t (3 * t) (3 * t + 1) + gA t x (3 * t) (3 * t + 1) + gB t y (3 * t) (3 * t + 1) = 1 := by
    rw [path_eq, g0 _ _ (Nat.le_refl _)]; simp [Pth, ind]
  have F2 : pathPub t (3 * t + 1) (3 * t + 2) + gA t x (3 * t + 1) (3 * t + 2) + gB t y (3 * t + 1) (3 * t + 2) = 1 := by
    rw [path_eq, g0 _ _ (by omega)]; simp [Pth, ind]
  have F3 : pathPub t (3 * t) (3 * t + 2) + gA t x (3 * t) (3 * t + 2) + gB t y (3 * t) (3 * t + 2) = 0 := by
    rw [path_eq, g0 _ _ (Nat.le_refl _)]; simp [Pth, ind]
  have cP := iso3_cost (3 * t + 3) M (pathPub t) (gA t x) (gB t y) hpM hsym hloop hle (3 * t) (3 * t + 1) (3 * t + 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [F1, F2, F3] at cP
  have vP := iso3_valid (3 * t + 3 + M) (3 * t) (3 * t + 1) (3 * t + 2) (by omega) (by omega) (by omega)
    (3 * t + 3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have sP := nsing_iso3 (3 * t + 3 + M) (3 * t) (3 * t + 1) (3 * t + 2) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨⟨lab0, hv0, hc0⟩, hmin⟩ := hm
  have hup := hmin _ vP
  have hlow := (liK_lower 4 (3 * t + 3) M (pathPub t) (gA t x) (gB t y) (path_hyp t M x y hM) lab0 hv0).1
  have c23 : c2 (4 - 1) = 6 := rfl
  rw [c23, hc0] at hlow
  refine ⟨by omega, ?_⟩
  by_cases tri : ∃ i j, i < t ∧ j < t ∧ x i j = true ∧ y i j = true
  · obtain ⟨i, j, hi, hj, hx, hy⟩ := tri
    obtain ⟨e1, e2, e3⟩ := gamma_tri_edges t x y i j hi hj hx hy
    have one : ∀ a b, 1 ≤ gamma t x y a b →
        pathPub t a b + gA t x a b + gB t y a b = 1 := by
      intro a b h; have := hle a b; rw [path_eq] at this ⊢; omega
    have cT := iso3_cost (3 * t + 3) M (pathPub t) (gA t x) (gB t y) hpM hsym hloop hle i (t + j) (2 * t + i)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [one _ _ e1, one _ _ e2, one _ _ e3] at cT
    have vT := iso3_valid (3 * t + 3 + M) i (t + j) (2 * t + i) (by omega) (by omega) (by omega)
      (3 * t + 3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have sT := nsing_iso3 (3 * t + 3 + M) i (t + j) (2 * t + i) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
    have := hmin _ vT
    exact ⟨_, vT, by omega, sT⟩
  · have hne : m + c2 (4 - 1) ≠ 2 * ((4 - 1) * (3 * t + 3)) := by
      intro h
      apply tri
      exact (path_clique t x y).mp ((li_threshold 4 (3 * t + 3) M (pathPub t) (gA t x) (gB t y)
        (path_hyp t M x y hM) m ⟨⟨lab0, hv0, hc0⟩, hmin⟩).mp h)
    rw [c23] at hne
    have hev := cost_even (3 * t + 3 + M) _ shape.1 shape.2.1 lab0
    rw [hc0] at hev
    exact ⟨_, vP, by omega, sP⟩


/-! ### Tools for k > 4: restriction, compaction of labels, iterated strict monotonicity -/

theorem div_block (R i z : Nat) (hR : 0 < R) (h1 : R * i ≤ z) (h2 : z < R * (i + 1)) : z / R = i := by
  have a := (Nat.le_div_iff_mul_le hR).mpr (by rw [Nat.mul_comm] at h1; exact h1)
  have b := (Nat.div_lt_iff_lt_mul hR).mpr (by rw [Nat.mul_comm] at h2; exact h2)
  omega

theorem cnt_interval (n a b : Nat) (hab : a ≤ b) (hb : b ≤ n) :
    cnt n (fun x => decide (a ≤ x) && decide (x < b)) = b - a := by
  have h1 := cnt_split n (fun x => decide (x < b)) (fun x => decide (x < a))
  rw [cnt_lt_count n b hb] at h1
  have e1 : cnt n (fun x => decide (x < b) && decide (x < a)) = a := by
    refine Eq.trans ?_ (cnt_lt_count n a (by omega))
    unfold cnt; apply lsum_congr; intro x _
    by_cases h : x < a
    · simp [h, show x < b by omega]
    · simp [h]
  have e2 : cnt n (fun x => decide (x < b) && !decide (x < a)) = cnt n (fun x => decide (a ≤ x) && decide (x < b)) := by
    unfold cnt; apply lsum_congr; intro x _
    by_cases h : x < a
    · simp [h, show ¬ a ≤ x by omega]
    · by_cases h' : x < b <;> simp [h, h', show a ≤ x by omega]
  omega

theorem D_restrict (N NG : Nat) (hN : N ≤ NG) (f : Nat → Nat → Nat)
    (hf : ∀ u v, ¬ (u < N ∧ v < N) → f u v = 0) : D NG f = D N f := by
  unfold D
  rw [show NG = N + (NG - N) by omega, lsum_range_add]
  rw [lsum_congr (List.range (NG - N)) _ (fun _ => 0) (fun i _ => by
    rw [lsum_congr _ _ (fun _ => 0) (fun v _ => hf _ _ (by omega)), lsum_zero]), lsum_zero, Nat.add_zero]
  apply lsum_congr; intro u hu
  have hu := List.mem_range.mp hu
  rw [lsum_range_add, lsum_congr (List.range (NG - N)) _ (fun _ => 0) (fun i _ => hf _ _ (by omega)), lsum_zero]
  rfl

/-- The image of i ↦ f i over {i < Q : P i} has at most |{i < Q : P i}| elements. -/
theorem cnt_image (K : Nat) (f : Nat → Nat) (P : Nat → Bool) : ∀ Q,
    cnt K (fun l => (List.range Q).any (fun i => P i && f i == l)) ≤ cnt Q P := by
  intro Q
  induction Q with
  | zero => simp [cnt, lsum, List.any]; exact lsum_zero _
  | succ Q ih =>
    rw [cnt_succ]
    have h1 : cnt K (fun l => (List.range (Q + 1)).any (fun i => P i && f i == l)) ≤
        cnt K (fun l => (List.range Q).any (fun i => P i && f i == l)) + cnt K (fun l => P Q && f Q == l) := by
      unfold cnt; rw [← lsum_add]; apply lsum_mono; intro l _
      dsimp only
      rw [List.range_succ, List.any_append]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      cases (List.range Q).any (fun i => P i && f i == l) <;> cases (P Q && f Q == l) <;> simp [ind]
    have h2 : cnt K (fun l => P Q && f Q == l) ≤ ind (P Q) := by
      cases hp : P Q
      · simp [cnt, ind]; exact lsum_zero _
      · simp only [Bool.true_and]
        have := count_one (f Q) true K
        simp only [Bool.and_true] at this
        unfold cnt; rw [this]; unfold ind; split <;> simp
    omega

/-- Strict monotonicity iterated: a (4+d)-partition of a connected graph costs at least 2d more
    than some 4-partition. -/
theorem iter_mono (N : Nat) (w : Nat → Nat → Nat) (hsym : ∀ x y, w x y = w y x)
    (hconn : ∀ X : Nat → Bool, (∃ x, x < N ∧ X x = true) → (∃ y, y < N ∧ X y = false) → 1 ≤ q N w X) :
    ∀ d lab, ValidK N (4 + d) lab → ∃ lab4, ValidK N 4 lab4 ∧ cost N w lab4 + 2 * d ≤ cost N w lab := by
  intro d
  induction d with
  | zero => intro lab hv; exact ⟨lab, hv, by simp⟩
  | succ d ih =>
    intro lab hv
    obtain ⟨lab', h1, h2, h3⟩ := strict_mono N w hsym hconn (4 + d) (by omega) lab hv.1 hv.2
    obtain ⟨lab4, hv4, h4⟩ := ih lab' ⟨h1, h2⟩
    exact ⟨lab4, hv4, by omega⟩

/-- Compaction: a labelling of 0..N-1 with labels below K uses r labels, and can be renumbered
    to a valid r-partition with the same cost. -/
theorem compact (N K : Nat) (w : Nat → Nat → Nat) (lab : Nat → Nat) (hK : ∀ x, x < N → lab x < K) :
    let used : Nat → Bool := fun l => (List.range N).any (fun v => lab v == l)
    ValidK N (cnt K used) (fun x => cnt (lab x) used) ∧ cost N w (fun x => cnt (lab x) used) = cost N w lab := by
  intro used
  have hu : ∀ x, x < N → used (lab x) = true := by
    intro x hx; simp only [used, List.any_eq_true, List.mem_range, beq_iff_eq]; exact ⟨x, hx, rfl⟩
  refine ⟨⟨fun y hy => ?_, fun c hc => ?_⟩, ?_⟩
  · exact rank_lt used (lab y) K (hK y hy) (hu y hy)
  · obtain ⟨l, hl, hul, hr⟩ := rank_surj used K c hc
    simp only [used, List.any_eq_true, List.mem_range, beq_iff_eq] at hul
    obtain ⟨v, hv, hlv⟩ := hul
    exact ⟨v, hv, by show cnt (lab v) used = c; rw [hlv]; exact hr⟩
  · unfold cost; apply D_congr; intro u v hu' hv'
    by_cases h : lab u = lab v
    · simp [h]
    · have : cnt (lab u) used ≠ cnt (lab v) used := fun e => h (rank_inj used _ _ (hu u hu') (hu v hv') e)
      have e1 : (cnt (lab u) used != cnt (lab v) used) = true := by simp [this]
      have e2 : (lab u != lab v) = true := by simp [h]
      rw [e1, e2]

theorem conn_cut (N : Nat) (w : Nat → Nat → Nat) (hR : ∀ u v, u < N → v < N → Reach w u v)
    (hsupp : ∀ a b, 1 ≤ w a b → a < N ∧ b < N)
    (X : Nat → Bool) (hx : ∃ x, x < N ∧ X x = true) (hy : ∃ y, y < N ∧ X y = false) : 1 ≤ q N w X := by
  obtain ⟨x, hxN, hX⟩ := hx
  obtain ⟨y, hyN, hY⟩ := hy
  obtain ⟨a, b, ha, hb, hab⟩ := reach_cross w X (hR x y hxN hyN) hX hY
  have := D_ge_term N (fun u v => ind (X u != X v) * w u v) a b (hsupp a b hab).1 (hsupp a b hab).2
  unfold q
  have e : (X a != X b) = true := by rw [ha, hb]; rfl
  dsimp only at this
  have t : ind (X a != X b) * w a b = w a b := by rw [e]; simp [ind]
  rw [t] at this
  omega


/-! ### The graph G of Corollary 28: H plus q public cliques, each bridged to a vertex z of H -/

def blkC (N R i : Nat) (x : Nat) : Bool := decide (N + R * i ≤ x) && decide (x < N + R * (i + 1))
def clqs (N R Q : Nat) (u v : Nat) : Nat := lsum (List.range Q) (fun i => ind (blkC N R i u && blkC N R i v && u != v))
def brgs (N R Q z : Nat) (u v : Nat) : Nat := lsum (List.range Q) (fun i => bridge (N + R * i) z u v)
def Hr (N : Nat) (L : Nat → Nat → Nat) (u v : Nat) : Nat := if u < N ∧ v < N then L u v else 0
def Gk (N R Q z : Nat) (L : Nat → Nat → Nat) (u v : Nat) : Nat := Hr N L u v + clqs N R Q u v + brgs N R Q z u v

theorem lsum_pos (l : List Nat) (f : Nat → Nat) (h : 1 ≤ lsum l f) : ∃ a, a ∈ l ∧ 1 ≤ f a := by
  induction l with
  | nil => simp [lsum] at h
  | cons a l ih =>
    simp only [lsum] at h
    by_cases ha : 1 ≤ f a
    · exact ⟨a, by simp, ha⟩
    · obtain ⟨b, hb, hfb⟩ := ih (by omega); exact ⟨b, by simp [hb], hfb⟩

theorem cost_add3 (n : Nat) (w1 w2 w3 : Nat → Nat → Nat) (lab : Nat → Nat) :
    cost n (fun u v => w1 u v + w2 u v + w3 u v) lab = cost n w1 lab + cost n w2 lab + cost n w3 lab := by
  unfold cost; rw [← D_add, ← D_add]; apply D_congr; intro u v _ _; simp only [Nat.mul_add]

theorem cost_Hr (N NG : Nat) (hN : N ≤ NG) (L : Nat → Nat → Nat) (lab : Nat → Nat) :
    cost NG (Hr N L) lab = cost N L lab := by
  unfold cost
  rw [D_restrict N NG hN _ (fun u v h => by simp [Hr, h])]
  apply D_congr; intro u v hu hv; simp [Hr, hu, hv]

theorem cost_brgs (N R Q z NG : Nat) (hz : z < N) (hR : 1 ≤ R) (hNG : N + R * Q ≤ NG) (lab : Nat → Nat) :
    cost NG (brgs N R Q z) lab = 2 * cnt Q (fun i => lab (N + R * i) != lab z) := by
  unfold cost brgs
  rw [D_congr NG _ (fun u v => lsum (List.range Q) (fun i => ind (lab u != lab v) * bridge (N + R * i) z u v))
    (fun u v _ _ => (lsum_mul_left _ _ _).symm), ← lsum_D]
  unfold cnt; rw [← lsum_mul_left]
  apply lsum_congr; intro i hi
  have hi := List.mem_range.mp hi
  have : N + R * i < NG := by
    have := Nat.mul_le_mul_left R (show i + 1 ≤ Q by omega); rw [Nat.mul_add, Nat.mul_one] at this; omega
  exact cost_bridge NG lab (N + R * i) z this (by omega) (by omega)

theorem blk_mem (N R _Q i x : Nat) (hR : 1 ≤ R) (h : blkC N R i x = true) : (x - N) / R = i ∧ N ≤ x := by
  simp only [blkC, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨div_block R i (x - N) (by omega) (by omega) (by omega), by omega⟩

/-- λ_k(G) = λ₄(H) + q (doubled: + 2q), for k = 4 + q; and an optimum of H with three singleton
    parts extends to one of G. -/
theorem G_lamk (N R Q z : Nat) (L : Nat → Nat → Nat) (hsym : ∀ u v, L u v = L v u)
    (hsupp : ∀ a b, 1 ≤ L a b → a < N ∧ b < N) (hconn : ∀ u v, u < N → v < N → Reach L u v)
    (hz : z < N) (hR : 2 ≤ R) (m4 : Nat) (hm : IsMinK N L 4 m4) (hgap : m4 + 2 * Q < 2 * (R - 1)) :
    IsMinK (N + R * Q) (Gk N R Q z L) (4 + Q) (m4 + 2 * Q) ∧
    (∀ labH, ValidK N 4 labH → cost N L labH = m4 → nsing N 4 labH = 3 →
      ∃ lab, ValidK (N + R * Q) (4 + Q) lab ∧ cost (N + R * Q) (Gk N R Q z L) lab = m4 + 2 * Q ∧
        nsing (N + R * Q) (4 + Q) lab = 3) := by
  classical
  have hNG : N ≤ N + R * Q := by omega
  have hdec : ∀ lab, cost (N + R * Q) (Gk N R Q z L) lab =
      cost N L lab + cost (N + R * Q) (clqs N R Q) lab + 2 * cnt Q (fun i => lab (N + R * i) != lab z) := by
    intro lab
    unfold Gk
    rw [cost_add3, cost_Hr N _ hNG, cost_brgs N R Q z _ hz (by omega) (Nat.le_refl _)]
  have hblk : ∀ i, i < Q → N + R * (i + 1) ≤ N + R * Q := by
    intro i hi; have := Nat.mul_le_mul_left R (show i + 1 ≤ Q by omega); omega
  -- the canonical extension of a 4-partition of H
  let ext : (Nat → Nat) → Nat → Nat := fun labH x => if x < N then labH x else 4 + (x - N) / R
  have ext_valid : ∀ labH, ValidK N 4 labH → ValidK (N + R * Q) (4 + Q) (ext labH) := by
    intro labH hv
    refine ⟨fun y hy => ?_, fun c hc => ?_⟩
    · simp only [ext]; split
      · have := hv.1 y (by assumption); omega
      · have : (y - N) / R < Q := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [Nat.mul_comm]; omega)
        omega
    · by_cases h4 : c < 4
      · obtain ⟨v, hv1, hv2⟩ := hv.2 c h4; exact ⟨v, by omega, by simp [ext, hv1, hv2]⟩
      · refine ⟨N + R * (c - 4), by
          have h1 := hblk (c - 4) (by omega); rw [Nat.mul_add, Nat.mul_one] at h1; omega, ?_⟩
        simp only [ext, show ¬ (N + R * (c - 4) < N) by omega, ite_false]
        rw [show N + R * (c - 4) - N = R * (c - 4) by omega, Nat.mul_div_cancel_left _ (by omega)]; omega
  have ext_cost : ∀ labH, ValidK N 4 labH →
      cost (N + R * Q) (Gk N R Q z L) (ext labH) = cost N L labH + 2 * Q := by
    intro labH hv
    rw [hdec]
    have h1 : cost N L (ext labH) = cost N L labH := by
      unfold cost; apply D_congr; intro u v hu hv; simp [ext, hu, hv]
    have h2 : cost (N + R * Q) (clqs N R Q) (ext labH) = 0 := by
      unfold cost
      rw [D_congr _ _ (fun _ _ => 0) (fun u v _ _ => ?_), D_zero]
      by_cases hc : 1 ≤ clqs N R Q u v
      · obtain ⟨i, hi, hpos⟩ := lsum_pos _ _ hc
        have hb : blkC N R i u = true ∧ blkC N R i v = true := by
          revert hpos; cases h1 : blkC N R i u <;> cases h2 : blkC N R i v <;> simp [ind]
        obtain ⟨eu, nu⟩ := blk_mem N R Q i u (by omega) hb.1
        obtain ⟨ev, nv⟩ := blk_mem N R Q i v (by omega) hb.2
        have hu' : ¬ u < N := by
          simp only [blkC, Bool.and_eq_true, decide_eq_true_eq] at hb; omega
        have hv' : ¬ v < N := by
          simp only [blkC, Bool.and_eq_true, decide_eq_true_eq] at hb; omega
        show ind (ext labH u != ext labH v) * clqs N R Q u v = 0
        have : ext labH u = ext labH v := by simp only [ext, hu', hv', ite_false, eu, ev]
        rw [this]; simp [ind]
      · show ind (ext labH u != ext labH v) * clqs N R Q u v = 0
        rw [show clqs N R Q u v = 0 by omega, Nat.mul_zero]
    have h3 : cnt Q (fun i => ext labH (N + R * i) != ext labH z) = Q := by
      refine Eq.trans ?_ (lsum_ones Q); unfold cnt; apply lsum_congr; intro i hi
      have hi := List.mem_range.mp hi
      have hz4 := hv.1 z hz
      simp only [ext, show ¬ (N + R * i < N) by omega, hz, ite_true, ite_false,
        show N + R * i - N = R * i by omega, Nat.mul_div_cancel_left _ (show 0 < R by omega)]
      simp [ind]; omega
    rw [h1, h2, h3]; omega
  -- lower bound
  have lower : ∀ lab, ValidK (N + R * Q) (4 + Q) lab → m4 + 2 * Q ≤ cost (N + R * Q) (Gk N R Q z L) lab := by
    intro lab hv
    by_cases hs : ∃ i u v, i < Q ∧ blkC N R i u = true ∧ blkC N R i v = true ∧ lab u ≠ lab v
    · obtain ⟨i, u, v, hi, hu, hv', hne⟩ := hs
      have hb := hblk i hi
      have hb' : N + R * i + R ≤ N + R * Q := by rw [Nat.mul_add, Nat.mul_one] at hb; omega
      have hu2 : u < N + R * Q := by simp only [blkC, Bool.and_eq_true, decide_eq_true_eq] at hu; omega
      have hv2 : v < N + R * Q := by simp only [blkC, Bool.and_eq_true, decide_eq_true_eq] at hv'; omega
      have hcs := clique_split (N + R * Q) (Gk N R Q z L) lab (blkC N R i) (fun x y _ _ hx hy hxy => by
        have hc1 : 1 ≤ clqs N R Q x y := by
          unfold clqs; refine Nat.le_trans ?_ (lsum_ge_term _ i Q hi); simp [hx, hy, hxy, ind]
        show 1 ≤ Hr N L x y + clqs N R Q x y + brgs N R Q z x y
        omega) u v hu2 hv2 hu hv' hne
      have hc : cnt (N + R * Q) (blkC N R i) = R := by
        unfold blkC; rw [cnt_interval _ _ _ (Nat.add_le_add_left (Nat.mul_le_mul_left R (Nat.le_succ i)) N) hb, Nat.mul_succ]; omega
      rw [hc] at hcs; omega
    · have mono : ∀ i u, i < Q → blkC N R i u = true → lab u = lab (N + R * i) := by
        intro i u hi hu
        apply Classical.byContradiction; intro hne
        apply hs; refine ⟨i, u, N + R * i, hi, hu, ?_, hne⟩
        simp only [blkC, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · omega
        · rw [Nat.mul_add, Nat.mul_one]; omega
      have hK : ∀ x, x < N → lab x < 4 + Q := fun x hx => hv.1 x (by omega)
      obtain ⟨hvC, hcC⟩ := compact N (4 + Q) L lab hK
      generalize hused : (fun l => (List.range N).any (fun v => lab v == l)) = used at hvC hcC
      have husedl : ∀ l, used l = true ↔ ∃ v, v < N ∧ lab v = l := by
        intro l; rw [← hused]; simp
      generalize hr : cnt (4 + Q) used = r at hvC
      generalize hc : cnt Q (fun i => lab (N + R * i) != lab z) = c
      have hcQ : c ≤ Q := by
        rw [← hc]; have := cnt_mono_set Q (fun i => lab (N + R * i) != lab z) (fun _ => true) (fun _ _ _ => rfl)
        rw [show cnt Q (fun _ => true) = Q by unfold cnt; simp [ind]; exact lsum_ones Q] at this; exact this
      -- unused labels are colours of bridged cliques whose bridge crosses
      have himg := cnt_image (4 + Q) (fun i => lab (N + R * i)) (fun i => lab (N + R * i) != lab z) Q
      rw [hc] at himg
      have hun : cnt (4 + Q) (fun l => !used l) ≤ c := by
        refine Nat.le_trans (cnt_mono_set _ _ _ (fun l hl hnu => ?_)) himg
        simp only [Bool.not_eq_true'] at hnu
        obtain ⟨v, hvN, hlv⟩ := hv.2 l hl
        have hvge : N ≤ v := by
          apply Classical.byContradiction; intro h
          have := (husedl l).mpr ⟨v, by omega, hlv⟩; rw [this] at hnu; exact absurd hnu (by simp)
        let i := (v - N) / R
        have hiQ : i < Q := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [Nat.mul_comm]; omega)
        have hbi : blkC N R i v = true := by
          simp only [blkC, Bool.and_eq_true, decide_eq_true_eq]
          have h1 := Nat.div_add_mod (v - N) R
          have h2 := Nat.mod_lt (v - N) (show 0 < R by omega)
          constructor
          · simp only [i]; omega
          · rw [Nat.mul_add, Nat.mul_one]; simp only [i]; omega
        have hli : lab (N + R * i) = l := by rw [← mono i v hiQ hbi]; exact hlv
        have hzl : lab z ≠ l := by
          intro e; have := (husedl l).mpr ⟨z, hz, e⟩; rw [this] at hnu; exact absurd hnu (by simp)
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
        exact ⟨i, hiQ, by rw [hli]; exact fun e => hzl e.symm, hli⟩
      have hcomp := cnt_compl (4 + Q) used
      rw [hr] at hcomp
      have hr4 : 4 ≤ r := by omega
      obtain ⟨lab4, hv4, h4⟩ := iter_mono N L hsym (conn_cut N L hconn hsupp) (r - 4) _
        (by rw [show 4 + (r - 4) = r by omega]; exact hvC)
      have := hm.2 lab4 hv4
      rw [hdec, ← hcC, hc]; omega
  refine ⟨⟨?_, lower⟩, ?_⟩
  · obtain ⟨⟨labH, hv, hcH⟩, _⟩ := hm
    exact ⟨ext labH, ext_valid labH hv, by rw [ext_cost labH hv, hcH]⟩
  · intro labH hv hcH hs3
    refine ⟨ext labH, ext_valid labH hv, by rw [ext_cost labH hv, hcH], ?_⟩
    unfold nsing at hs3 ⊢
    change lsum (List.range 4) (fun c => ind (cnt N (part labH c) == 1)) = 3 at hs3
    show lsum (List.range (4 + Q)) (fun c => ind (cnt (N + R * Q) (part (ext labH) c) == 1)) = 3
    rw [lsum_range_add 4 _ Q]
    have hfirst : lsum (List.range 4) (fun c => ind (cnt (N + R * Q) (part (ext labH) c) == 1))
        = lsum (List.range 4) (fun c => ind (cnt N (part labH c) == 1)) := by
      apply lsum_congr; intro c hc
      have hc := List.mem_range.mp hc
      have e : cnt (N + R * Q) (part (ext labH) c) = cnt N (part labH c) := by
        rw [cnt_below (N + R * Q) N _ hNG (fun x hx => by
          simp only [part, ext, beq_iff_eq] at hx; split at hx
          · assumption
          · generalize (x - N) / R = j at hx; omega)]
        unfold cnt; apply lsum_congr; intro x hx
        simp [part, ext, List.mem_range.mp hx]
      rw [e]
    have hsecond : lsum (List.range Q) (fun i => ind (cnt (N + R * Q) (part (ext labH) (4 + i)) == 1)) = 0 := by
      rw [lsum_congr _ _ (fun _ => 0) (fun i hi => ?_), lsum_zero]
      have hi := List.mem_range.mp hi
      have e : cnt (N + R * Q) (part (ext labH) (4 + i)) = R := by
        have hb := hblk i hi
        refine Eq.trans ?_ (show cnt (N + R * Q) (blkC N R i) = R by
          unfold blkC; rw [cnt_interval _ _ _ (Nat.add_le_add_left (Nat.mul_le_mul_left R (Nat.le_succ i)) N) hb, Nat.mul_succ]; omega)
        unfold cnt; apply lsum_congr; intro x hx
        have hx := List.mem_range.mp hx
        by_cases hxN : x < N
        · have := hv.1 x hxN
          have e1 : (ext labH x == 4 + i) = false := by simp only [ext, hxN, ite_true]; simp; omega
          have e2 : blkC N R i x = false := by simp [blkC]; omega
          simp only [part, e1, e2]
        · simp only [part, ext, hxN, ite_false, blkC]
          have h1 := Nat.div_add_mod (x - N) R
          have h2 := Nat.mod_lt (x - N) (show 0 < R by omega)
          by_cases hq : (x - N) / R = i
          · have : N + R * i ≤ x ∧ x < N + R * (i + 1) := by
              rw [← hq, Nat.mul_add, Nat.mul_one]; omega
            simp [hq, this.1, this.2]
          · have : ¬ (N + R * i ≤ x ∧ x < N + R * (i + 1)) := by
              intro hh; obtain ⟨hh1, hh2⟩ := hh; rw [Nat.mul_add, Nat.mul_one] at hh2
              apply hq; exact div_block R i (x - N) (by omega) (by omega) (by rw [Nat.mul_add, Nat.mul_one]; omega)
            have e3 : (4 + (x - N) / R == 4 + i) = false := by simp; omega
            rw [e3]
            by_cases a1 : N + R * i ≤ x
            · simp [a1, show ¬ x < N + R * (i + 1) from fun h => this ⟨a1, h⟩, ind]
            · simp [a1, ind]
      rw [e]; simp [ind]; omega
    rw [hfirst, hsecond]; omega


/-! ### Corollary 28 assembled -/

theorem isMinK_unique (N k : Nat) (w : Nat → Nat → Nat) (a b : Nat) (ha : IsMinK N w k a) (hb : IsMinK N w k b) :
    a = b := by
  obtain ⟨⟨la, hva, hca⟩, hma⟩ := ha
  obtain ⟨⟨lb, hvb, hcb⟩, hmb⟩ := hb
  have := hma lb hvb; have := hmb la hva; omega

theorem isMinK_exists (N k : Nat) (w : Nat → Nat → Nat) (lab : Nat → Nat) (hv : ValidK N k lab) :
    ∃ m, IsMinK N w k m := by
  obtain ⟨m, ⟨l, hl, hc⟩, hmin⟩ := exists_min (fun m => ∃ lab, ValidK N k lab ∧ cost N w lab = m) ⟨_, lab, hv, rfl⟩
  exact ⟨m, ⟨l, hl, hc⟩, fun l' hl' => hmin _ ⟨l', hl', rfl⟩⟩

theorem liG_supp (p M : Nat) (Fp Fa Fb : Nat → Nat → Nat) (hpM : p ≤ M) (a b : Nat)
    (h : 1 ≤ liG p M Fp Fa Fb a b) : a < p + M ∧ b < p + M := by
  apply Classical.byContradiction; intro hn
  have : liG p M Fp Fa Fb a b = 0 := by
    unfold liG liPub rb cliqueW att ind
    by_cases ha : a < p + M
    · have hb : ¬ b < p + M := by omega
      simp [hb, show ¬ b < p by omega]
      intros; omega
    · simp [ha, show ¬ a < p by omega]; intro _ _; omega
  omega

/-- Answering a cut query by one query to an oracle plus a public correction. -/
def simAdd {α : Type} (pub : (Nat → Bool) → Nat) : Alg α → Alg α
  | .ret a => .ret a
  | .ask S k => .ask S (fun r => simAdd pub (k (r + pub S)))

theorem simAdd_spec {α : Type} (O pub : (Nat → Bool) → Nat) (A : Alg α) :
    Alg.run O (simAdd pub A) = Alg.run (fun S => O S + pub S) A ∧
    Alg.cost O (simAdd pub A) = Alg.cost (fun S => O S + pub S) A := by
  induction A with
  | ret a => exact ⟨rfl, rfl⟩
  | ask S k ih => simp only [simAdd, Alg.run, Alg.cost]; exact ⟨(ih _).1, by rw [(ih _).2]⟩

theorem q_Hr (N NG : Nat) (hN : N ≤ NG) (L : Nat → Nat → Nat) (S : Nat → Bool) :
    q NG (Hr N L) S = q N L S := by
  unfold q
  rw [D_restrict N NG hN _ (fun u v h => by simp [Hr, h])]
  apply D_congr; intro u v hu hv; simp [Hr, hu, hv]

/-- The hard graphs of Corollary 28 (k = 4 + Q): G_{x,y} = H_{x,y} with Q public cliques of size
    R = 3p + Q, each bridged to the vertex p of Li's clique; p = 3t + 3, M ≥ 16p. -/
def cor28G (t M Q : Nat) (x y : Nat → Nat → Bool) : Nat → Nat → Nat :=
  Gk (3 * t + 3 + M) (3 * (3 * t + 3) + Q) Q (3 * t + 3) (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y))

/-- Corollary 28, the promise: every G_{x,y} has an optimum (4+Q)-partition with exactly three
    singleton parts, and λ_{4+Q}(G) = λ₄(H) + Q. -/
theorem cor28_promise (t M Q : Nat) (hM : 16 * (3 * t + 3) ≤ M) (x y : Nat → Nat → Bool) :
    ∃ m4, IsMinK (3 * t + 3 + M) (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y)) 4 m4 ∧
    IsMinK (3 * t + 3 + M + (3 * (3 * t + 3) + Q) * Q) (cor28G t M Q x y) (4 + Q) (m4 + 2 * Q) ∧
    ∃ lab, ValidK (3 * t + 3 + M + (3 * (3 * t + 3) + Q) * Q) (4 + Q) lab ∧
      cost (3 * t + 3 + M + (3 * (3 * t + 3) + Q) * Q) (cor28G t M Q x y) lab = m4 + 2 * Q ∧
      nsing (3 * t + 3 + M + (3 * (3 * t + 3) + Q) * Q) (4 + Q) lab = 3 := by
  obtain ⟨hsym, hloop, hle, _, _, _⟩ := path_hyp t M x y hM
  have shape := liG_shape (3 * t + 3) M (pathPub t) (gA t x) (gB t y) (by omega) hsym hloop hle
  have vP := iso3_valid (3 * t + 3 + M) (3 * t) (3 * t + 1) (3 * t + 2) (by omega) (by omega) (by omega)
    (3 * t + 3) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨m4, hm4⟩ := isMinK_exists _ 4 (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y)) _ vP
  obtain ⟨hup, labH, hvH, hcH, hsH⟩ := H_facts t M hM x y m4 hm4
  have hG := G_lamk (3 * t + 3 + M) (3 * (3 * t + 3) + Q) Q (3 * t + 3) _ shape.1
    (liG_supp _ M _ _ _ (by omega)) (liG_connected _ M _ _ _ (by omega) (by omega) hsym hloop hle)
    (by omega) (by omega) m4 hm4 (by omega)
  obtain ⟨lab, h1, h2, h3⟩ := hG.2 labH hvH hcH hsH
  exact ⟨m4, hm4, hG.1, lab, h1, h2, h3⟩

/-- Corollary 28, lower bound (deterministic, no cited ingredient): an algorithm that returns
    λ_{4+Q} on every G_{x,y} asks, on some input, q queries with
      t² ≤ 2p(⌈log₂ p⌉ + 1) + 2(2⌈log₂(p+M)⌉ + 1)·q,
    since each cut query to G is one cut query to H plus a public correction. -/
theorem cor28_det_lb (t M Q : Nat) (hM : 16 * (3 * t + 3) ≤ M) (A : Alg Nat)
    (hA : ∀ x y, IsMinK (3 * t + 3 + M + (3 * (3 * t + 3) + Q) * Q) (cor28G t M Q x y) (4 + Q)
      (Alg.run (q (3 * t + 3 + M + (3 * (3 * t + 3) + Q) * Q) (cor28G t M Q x y)) A)) :
    ∃ x y, t * t ≤ 2 * ((3 * t + 3) * (clog (3 * t + 3) + 1)) + 2 * (2 * clog (3 * t + 3 + M) + 1) *
      Alg.cost (q (3 * t + 3 + M + (3 * (3 * t + 3) + Q) * Q) (cor28G t M Q x y)) A := by
  generalize hN : 3 * t + 3 + M = N at *
  generalize hR : 3 * (3 * t + 3) + Q = R at *
  let pub : (Nat → Bool) → Nat := fun S => q (N + R * Q) (clqs N R Q) S + q (N + R * Q) (brgs N R Q (3 * t + 3)) S
  let AH : Alg Nat := Alg.bind (simAdd pub A) (fun m => .ret (m - 2 * Q))
  have hO : ∀ x y, (fun S => q N (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y)) S + pub S)
      = q (N + R * Q) (cor28G t M Q x y) := by
    intro x y; funext S
    simp only [pub, cor28G, hN, hR]
    unfold Gk
    rw [q_add3, q_Hr N _ (by omega)]; omega
  have hspec : ∀ x y, Alg.run (q N (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y))) AH =
      Alg.run (q (N + R * Q) (cor28G t M Q x y)) A - 2 * Q ∧
      Alg.cost (q N (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y))) AH =
      Alg.cost (q (N + R * Q) (cor28G t M Q x y)) A := by
    intro x y
    simp only [AH, Alg.run_bind, Alg.cost_bind, (simAdd_spec _ _ A).1, (simAdd_spec _ _ A).2, hO x y]
    exact ⟨rfl, by simp [Alg.cost]⟩
  have hAH : ∀ x y, IsMinK (3 * t + 3 + M) (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y)) 4
      (Alg.run (q (3 * t + 3 + M) (liG (3 * t + 3) M (pathPub t) (gA t x) (gB t y))) AH) := by
    intro x y
    obtain ⟨m4, hm4, hG, _⟩ := cor28_promise t M Q (by omega) x y
    rw [hN, hR] at hG
    have := isMinK_unique _ _ _ _ _ (hA x y) hG
    rw [hN, (hspec x y).1, this]
    rw [hN] at hm4
    rw [show m4 + 2 * Q - 2 * Q = m4 by omega]; exact hm4
  obtain ⟨x, y, h⟩ := path_det_lb t M hM AH hAH
  refine ⟨x, y, ?_⟩
  rw [hN, (hspec x y).2] at h
  exact h


/-! ### The graphs G_{x,y} are simple and connected -/

theorem lsum_le_one (Q : Nat) (f : Nat → Nat) (h1 : ∀ i, i < Q → f i ≤ 1)
    (h2 : ∀ i j, i < Q → j < Q → 1 ≤ f i → 1 ≤ f j → i = j) : lsum (List.range Q) f ≤ 1 := by
  induction Q with
  | zero => simp [lsum]
  | succ Q ih =>
    rw [List.range_succ, lsum_append]; simp only [lsum]
    by_cases hQ : 1 ≤ f Q
    · have : lsum (List.range Q) f = 0 := by
        rw [lsum_congr _ _ (fun _ => 0) (fun i hi => by
          have hi := List.mem_range.mp hi
          show f i = 0
          apply Classical.byContradiction; intro hne
          have := h2 i Q (by omega) (by omega) (by omega) hQ; omega), lsum_zero]
      have := h1 Q (by omega); omega
    · have := ih (fun i hi => h1 i (by omega)) (fun i j hi hj => h2 i j (by omega) (by omega)); omega

theorem Gk_simple_conn (N R Q z : Nat) (L : Nat → Nat → Nat) (hsym : ∀ u v, L u v = L v u)
    (hloop : ∀ u, L u u = 0) (hle : ∀ u v, L u v ≤ 1)
    (hsupp : ∀ a b, 1 ≤ L a b → a < N ∧ b < N) (hconn : ∀ u v, u < N → v < N → Reach L u v)
    (hz : z < N) (hR : 2 ≤ R) :
    (∀ u v, Gk N R Q z L u v = Gk N R Q z L v u) ∧ (∀ u, Gk N R Q z L u u = 0) ∧
    (∀ u v, Gk N R Q z L u v ≤ 1) ∧
    (∀ u v, u < N + R * Q → v < N + R * Q → Reach (Gk N R Q z L) u v) := by
  have hHr : ∀ u v, Hr N L u v = L u v := by
    intro u v; unfold Hr; split
    · rfl
    · apply Classical.byContradiction; intro h; rename_i hn; exact hn (hsupp u v (by omega))
  have bsym : ∀ h j u v, bridge h j u v = bridge h j v u := by
    intro h j u v; unfold bridge; congr 1; cases u == h <;> cases v == j <;> cases u == j <;> cases v == h <;> rfl
  have cpos : ∀ u v, 1 ≤ clqs N R Q u v → ∃ i, i < Q ∧ blkC N R i u = true ∧ blkC N R i v = true ∧ u ≠ v := by
    intro u v h
    obtain ⟨i, hi, hp⟩ := lsum_pos _ _ h
    refine ⟨i, List.mem_range.mp hi, ?_⟩
    revert hp; cases h1 : blkC N R i u <;> cases h2 : blkC N R i v <;> by_cases e : u = v <;> simp [ind, e]
  have bpos : ∀ u v, 1 ≤ brgs N R Q z u v → ∃ i, i < Q ∧ ((u = N + R * i ∧ v = z) ∨ (u = z ∧ v = N + R * i)) := by
    intro u v h
    obtain ⟨i, hi, hp⟩ := lsum_pos _ _ h
    refine ⟨i, List.mem_range.mp hi, ?_⟩
    unfold bridge ind at hp; split at hp
    · rename_i hc; simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc; omega
    · omega
  have blk_uniq : ∀ i j x, blkC N R i x = true → blkC N R j x = true → i = j := by
    intro i j x h1 h2
    have a := (blk_mem N R Q i x (by omega) h1).1
    have b := (blk_mem N R Q j x (by omega) h2).1
    omega
  refine ⟨fun u v => ?_, fun u => ?_, fun u v => ?_, ?_⟩
  · unfold Gk; rw [hHr, hHr, hsym u v]
    unfold clqs brgs
    rw [lsum_congr _ _ (fun i => ind (blkC N R i v && blkC N R i u && v != u)) (fun i _ => by
      by_cases e : u = v
      · subst e; rw [Bool.and_comm (blkC N R i u)]
      · have e' : v ≠ u := fun h => e h.symm
        have e1 : (u != v) = true := by simp [e]
        have e2 : (v != u) = true := by simp [e']
        show ind (blkC N R i u && blkC N R i v && (u != v)) = ind (blkC N R i v && blkC N R i u && (v != u))
        rw [e1, e2, Bool.and_comm (blkC N R i u)]),
      lsum_congr _ (fun i => bridge (N + R * i) z u v) _ (fun i _ => bsym _ _ u v)]
  · unfold Gk; rw [hHr, hloop]
    have h1 : clqs N R Q u u = 0 := by
      unfold clqs; rw [lsum_congr _ _ (fun _ => 0) (fun i _ => by simp [ind]), lsum_zero]
    have h2 : brgs N R Q z u u = 0 := by
      apply Classical.byContradiction; intro h
      obtain ⟨i, _, hh⟩ := bpos u u (by omega); omega
    omega
  · unfold Gk; rw [hHr]
    have hc : clqs N R Q u v ≤ 1 := by
      unfold clqs
      apply lsum_le_one
      · intro i _; unfold ind; split <;> omega
      · intro i j _ _ h1 h2
        have a : blkC N R i u = true := by revert h1; cases blkC N R i u <;> simp [ind]
        have b : blkC N R j u = true := by revert h2; cases blkC N R j u <;> simp [ind]
        exact blk_uniq i j u a b
    have hb : brgs N R Q z u v ≤ 1 := by
      unfold brgs
      apply lsum_le_one
      · intro i _; unfold bridge ind; split <;> omega
      · intro i j hi hj h1 h2
        have a := bpos u v (by unfold brgs; exact Nat.le_trans h1 (lsum_ge_term (fun i => bridge (N + R * i) z u v) i Q hi))
        unfold bridge ind at h1 h2; split at h1 <;> split at h2
        · rename_i c1 c2
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at c1 c2
          rcases c1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases c2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
            (try omega) <;>
            (have := Nat.eq_of_mul_eq_mul_left (show 0 < R by omega) (show R * i = R * j by omega); exact this)
        all_goals omega
    by_cases hL : 1 ≤ L u v
    · have hs := hsupp u v hL
      have : clqs N R Q u v = 0 := by
        apply Classical.byContradiction; intro h
        obtain ⟨i, _, h1, _, _⟩ := cpos u v (by omega)
        have := (blk_mem N R Q i u (by omega) h1).2; omega
      have : brgs N R Q z u v = 0 := by
        apply Classical.byContradiction; intro h
        obtain ⟨i, _, hh⟩ := bpos u v (by omega); omega
      have := hle u v; omega
    · by_cases hC : 1 ≤ clqs N R Q u v
      · obtain ⟨i, _, h1, h2, _⟩ := cpos u v hC
        have := (blk_mem N R Q i u (by omega) h1).2
        have := (blk_mem N R Q i v (by omega) h2).2
        have : brgs N R Q z u v = 0 := by
          apply Classical.byContradiction; intro h
          obtain ⟨j, _, hh⟩ := bpos u v (by omega); omega
        omega
      · omega
  · -- every vertex reaches z
    have hmono : ∀ a b, L a b ≤ Gk N R Q z L a b := by intro a b; unfold Gk; rw [hHr]; omega
    have hGs : ∀ a b, Gk N R Q z L a b = Gk N R Q z L b a := by
      intro a b; unfold Gk; rw [hHr, hHr, hsym a b]
      unfold clqs brgs
      rw [lsum_congr _ _ (fun i => ind (blkC N R i b && blkC N R i a && b != a)) (fun i _ => by
        by_cases e : a = b
        · subst e; rw [Bool.and_comm (blkC N R i a)]
        · have e' : b ≠ a := fun h => e h.symm
          have e1 : (a != b) = true := by simp [e]
          have e2 : (b != a) = true := by simp [e']
          show ind (blkC N R i a && blkC N R i b && (a != b)) = ind (blkC N R i b && blkC N R i a && (b != a))
          rw [e1, e2, Bool.and_comm (blkC N R i a)]),
        lsum_congr _ (fun i => bridge (N + R * i) z a b) _ (fun i _ => bsym _ _ a b)]
    have hto : ∀ u, u < N + R * Q → Reach (Gk N R Q z L) u z := by
      intro u hu
      by_cases huN : u < N
      · exact reach_mono L _ hmono (hconn u z huN hz)
      · let i := (u - N) / R
        have hiQ : i < Q := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [Nat.mul_comm]; omega)
        have h1 := Nat.div_add_mod (u - N) R
        have h2 := Nat.mod_lt (u - N) (show 0 < R by omega)
        have hb : 1 ≤ Gk N R Q z L (N + R * i) z := by
          have : 1 ≤ brgs N R Q z (N + R * i) z := by
            unfold brgs; refine Nat.le_trans ?_ (lsum_ge_term _ i Q hiQ); simp [bridge, ind]
          unfold Gk; omega
        have hstart : Reach (Gk N R Q z L) (N + R * i) z := Reach.step (Reach.refl _) hb
        by_cases hus : u = N + R * i
        · rw [hus]; exact hstart
        · have hc : 1 ≤ Gk N R Q z L u (N + R * i) := by
            have : 1 ≤ clqs N R Q u (N + R * i) := by
              unfold clqs; refine Nat.le_trans ?_ (lsum_ge_term _ i Q hiQ)
              have e1 : blkC N R i u = true := by
                simp only [blkC, Bool.and_eq_true, decide_eq_true_eq]; simp only [i]
                rw [Nat.mul_add, Nat.mul_one]; omega
              have e2 : blkC N R i (N + R * i) = true := by
                simp only [blkC, Bool.and_eq_true, decide_eq_true_eq]
                rw [Nat.mul_add, Nat.mul_one]; omega
              have e3 : (u != N + R * i) = true := by simp [hus]
              simp [e1, e2, e3, ind]
            unfold Gk; omega
          exact reach_trans _ (Reach.step (Reach.refl u) hc) hstart
    intro u v hu hv
    exact reach_trans _ (hto u hu) (reach_symm _ hGs (hto v hv))

/-- Corollary 28: the hard graphs are simple and connected. -/
theorem cor28G_simple_conn (t M Q : Nat) (hM : 16 * (3 * t + 3) ≤ M) (x y : Nat → Nat → Bool) :
    (∀ u v, cor28G t M Q x y u v = cor28G t M Q x y v u) ∧ (∀ u, cor28G t M Q x y u u = 0) ∧
    (∀ u v, cor28G t M Q x y u v ≤ 1) ∧
    (∀ u v, u < 3 * t + 3 + M + (3 * (3 * t + 3) + Q) * Q → v < 3 * t + 3 + M + (3 * (3 * t + 3) + Q) * Q →
      Reach (cor28G t M Q x y) u v) := by
  obtain ⟨hsym, hloop, hle, _, _, _⟩ := path_hyp t M x y hM
  have shape := liG_shape (3 * t + 3) M (pathPub t) (gA t x) (gB t y) (by omega) hsym hloop hle
  exact Gk_simple_conn _ _ Q _ _ shape.1 shape.2.1 shape.2.2.1 (liG_supp _ M _ _ _ (by omega))
    (liG_connected _ M _ _ _ (by omega) (by omega) hsym hloop hle) (by omega) (by omega)



end MinKCut
