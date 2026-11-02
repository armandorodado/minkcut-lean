import MinKCut.Simulation
/-! # Part M: deterministic communication complexity of set disjointness -/

namespace MinKCut

/-! ## Part M: the deterministic communication complexity of set disjointness

  Fooling-set argument: every deterministic protocol for DISJ_N sends at least N bits on some
  input. Combined with `triangle_protocol` this gives Lemma 24 for deterministic algorithms
  with no cited ingredient. -/

/-- A fooling family for P with value b: P outputs b on every pair of the family, and for two
    different pairs one of the two crossed inputs gives !b. -/
def Fooling {IA IB : Type} (P : Prot IA IB Bool) (b : Bool) (F : List (IA × IB)) : Prop :=
  (∀ p, p ∈ F → Prot.exec p.1 p.2 P = b) ∧
  F.Pairwise (fun p p' => Prot.exec p.1 p'.2 P = !b ∨ Prot.exec p'.1 p.2 P = !b)

theorem length_filter_split {β : Type} (f : β → Bool) : ∀ l : List β,
    (l.filter f).length + (l.filter (fun a => !f a)).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih => cases h : f a <;> simp [List.filter, h] <;> omega

/-- A fooling family of size m forces some pair of the family to use at least log₂ m bits. -/
theorem fooling_bound {IA IB : Type} (b : Bool) : ∀ (P : Prot IA IB Bool) (F : List (IA × IB)) (d : Nat),
    Fooling P b F → (∀ p, p ∈ F → Prot.bits p.1 p.2 P ≤ d) → F.length ≤ 2 ^ d := by
  intro P
  induction P with
  | ret r =>
    intro F d hF _
    match F, hF with
    | [], _ => simp
    | [_], _ => simp; exact Nat.one_le_two_pow
    | p :: p' :: l, ⟨hd, hpw⟩ =>
      have h1 := hd p (by simp)
      have h2 := (List.pairwise_cons.mp hpw).1 p' (by simp)
      simp only [Prot.exec] at h1 h2
      subst h1; cases r <;> simp at h2
  | sendA f k ih =>
    intro F d hF hb
    cases F with
    | nil => simp
    | cons p0 l =>
      have hd1 : 1 ≤ d := by have := hb p0 (by simp); simp only [Prot.bits] at this; omega
      have hsplit := length_filter_split (fun p => f p.1) (p0 :: l)
      have key : ∀ c : Bool, ((p0 :: l).filter (fun p => f p.1 == c)).length ≤ 2 ^ (d - 1) := by
        intro c
        apply ih c _ (d - 1)
        · refine ⟨fun p hp => ?_, ?_⟩
          · have hp' := List.mem_filter.mp hp
            have := hF.1 p hp'.1
            simp only [Prot.exec, beq_iff_eq.mp hp'.2] at this; exact this
          · apply List.Pairwise.imp_of_mem _ (hF.2.sublist (List.filter_sublist _))
            intro a a' ha ha' h
            have e1 := beq_iff_eq.mp (List.mem_filter.mp ha).2
            have e2 := beq_iff_eq.mp (List.mem_filter.mp ha').2
            simp only [Prot.exec, e1, e2] at h; exact h
        · intro p hp
          have hp' := List.mem_filter.mp hp
          have := hb p hp'.1
          simp only [Prot.bits, beq_iff_eq.mp hp'.2] at this; omega
      have k1 := key true
      have k0 := key false
      have e1 : (fun p : IA × IB => f p.1 == true) = (fun p => f p.1) := by funext p; cases f p.1 <;> rfl
      have e0 : (fun p : IA × IB => f p.1 == false) = (fun p => !f p.1) := by funext p; cases f p.1 <;> rfl
      rw [e1] at k1; rw [e0] at k0
      have : 2 ^ d = 2 ^ (d - 1) + 2 ^ (d - 1) := by
        rw [show d = (d - 1) + 1 by omega, Nat.pow_succ]; simp; omega
      omega
  | sendB g k ih =>
    intro F d hF hb
    cases F with
    | nil => simp
    | cons p0 l =>
      have hd1 : 1 ≤ d := by have := hb p0 (by simp); simp only [Prot.bits] at this; omega
      have hsplit := length_filter_split (fun p => g p.2) (p0 :: l)
      have key : ∀ c : Bool, ((p0 :: l).filter (fun p => g p.2 == c)).length ≤ 2 ^ (d - 1) := by
        intro c
        apply ih c _ (d - 1)
        · refine ⟨fun p hp => ?_, ?_⟩
          · have hp' := List.mem_filter.mp hp
            have := hF.1 p hp'.1
            simp only [Prot.exec, beq_iff_eq.mp hp'.2] at this; exact this
          · apply List.Pairwise.imp_of_mem _ (hF.2.sublist (List.filter_sublist _))
            intro a a' ha ha' h
            have e1 := beq_iff_eq.mp (List.mem_filter.mp ha).2
            have e2 := beq_iff_eq.mp (List.mem_filter.mp ha').2
            simp only [Prot.exec, e1, e2] at h; exact h
        · intro p hp
          have hp' := List.mem_filter.mp hp
          have := hb p hp'.1
          simp only [Prot.bits, beq_iff_eq.mp hp'.2] at this; omega
      have k1 := key true
      have k0 := key false
      have e1 : (fun p : IA × IB => g p.2 == true) = (fun p => g p.2) := by funext p; cases g p.2 <;> rfl
      have e0 : (fun p : IA × IB => g p.2 == false) = (fun p => !g p.2) := by funext p; cases g p.2 <;> rfl
      rw [e1] at k1; rw [e0] at k0
      have : 2 ^ d = 2 ^ (d - 1) + 2 ^ (d - 1) := by
        rw [show d = (d - 1) + 1 by omega, Nat.pow_succ]; simp; omega
      omega

/-- All 0/1 vectors supported on 0..N-1. -/
def allVecs : Nat → List (Nat → Bool)
  | 0 => [fun _ => false]
  | N + 1 => allVecs N ++ (allVecs N).map (fun v i => if i = N then true else v i)

theorem allVecs_spec : ∀ N, (allVecs N).length = 2 ^ N ∧ (∀ v, v ∈ allVecs N → ∀ i, N ≤ i → v i = false) ∧
    (allVecs N).Pairwise (fun v v' => ∃ i, i < N ∧ v i ≠ v' i) := by
  intro N
  induction N with
  | zero => refine ⟨rfl, ?_, by simp [allVecs]⟩; intro v hv i _; simp [allVecs] at hv; subst hv; rfl
  | succ N ih =>
    obtain ⟨hl, hz, hp⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · simp [allVecs, hl, Nat.pow_succ]; omega
    · intro v hv i hi
      simp only [allVecs, List.mem_append, List.mem_map] at hv
      rcases hv with hv | ⟨w, hw, rfl⟩
      · exact hz v hv i (by omega)
      · simp [show i ≠ N by omega, hz w hw i (by omega)]
    · simp only [allVecs]
      rw [List.pairwise_append, List.pairwise_map]
      refine ⟨hp.imp (fun h => by obtain ⟨i, hi, h⟩ := h; exact ⟨i, by omega, h⟩),
        hp.imp (fun h => by
          obtain ⟨i, hi, h⟩ := h
          exact ⟨i, by omega, by simp [show i ≠ N by omega, h]⟩), ?_⟩
      intro a ha b hb
      simp only [List.mem_map] at hb
      obtain ⟨w, _, rfl⟩ := hb
      exact ⟨N, by omega, by simp [hz a ha N (Nat.le_refl _)]⟩

/-- Deterministic communication complexity of disjointness: a protocol that outputs whether
    x and y (subsets of 0..N-1) intersect sends at least N bits on some input (x, complement of x). -/
theorem disj_lower (N : Nat) (P : Prot (Nat → Bool) (Nat → Bool) Bool)
    (hP : ∀ x y, Prot.exec x y P = true ↔ ∃ i, i < N ∧ x i = true ∧ y i = true) :
    ∃ x, N ≤ Prot.bits x (fun i => !x i) P := by
  apply Classical.byContradiction
  intro hno
  have hlt : ∀ x, Prot.bits x (fun i => !x i) P ≤ N - 1 := by
    intro x
    apply Classical.byContradiction; intro h; exact hno ⟨x, by omega⟩
  have hN : 1 ≤ N := by
    apply Classical.byContradiction; intro h; exact hno ⟨fun _ => false, by omega⟩
  obtain ⟨hl, _, hpw⟩ := allVecs_spec N
  let F := (allVecs N).map (fun v => (v, fun i => !v i))
  have hF : Fooling P false F := by
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [F, List.mem_map] at hp
      obtain ⟨v, _, rfl⟩ := hp
      cases h : Prot.exec v (fun i => !v i) P
      · rfl
      · obtain ⟨i, _, h1, h2⟩ := (hP _ _).mp h
        simp [h1] at h2
    · simp only [F]
      rw [List.pairwise_map]
      apply hpw.imp
      rintro v v' ⟨i, hi, hne⟩
      cases hv : v i
      · have hv' : v' i = true := by cases h : v' i <;> simp_all
        right; simp only [Bool.not_false]
        exact (hP _ _).mpr ⟨i, hi, hv', by simp [hv]⟩
      · have hv' : v' i = false := by cases h : v' i <;> simp_all
        left; simp only [Bool.not_false]
        exact (hP _ _).mpr ⟨i, hi, hv, by simp [hv']⟩
  have hb := fooling_bound false P F (N - 1) hF (by
    intro p hp
    simp only [F, List.mem_map] at hp
    obtain ⟨v, _, rfl⟩ := hp
    exact hlt v)
  simp only [F, List.length_map, hl] at hb
  have : 2 ^ N = 2 ^ (N - 1) + 2 ^ (N - 1) := by
    rw [show N = (N - 1) + 1 by omega, Nat.pow_succ]; simp; omega
  have := Nat.one_le_two_pow (n := N - 1)
  omega


/-- Reading a vector of length t² as a t × t matrix. -/
def dec (t : Nat) (v : Nat → Bool) : Nat → Nat → Bool := fun i j => v (t * i + j) && decide (i < t) && decide (j < t)

theorem dec_meet (t : Nat) (v w : Nat → Bool) :
    (∃ i j, i < t ∧ j < t ∧ dec t v i j = true ∧ dec t w i j = true) ↔
    ∃ k, k < t * t ∧ v k = true ∧ w k = true := by
  constructor
  · rintro ⟨i, j, hi, hj, h1, h2⟩
    simp only [dec, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
    refine ⟨t * i + j, ?_, h1.1.1, h2.1.1⟩
    have := Nat.mul_le_mul_left t (show i + 1 ≤ t by omega)
    rw [Nat.mul_add, Nat.mul_one] at this; omega
  · rintro ⟨k, hk, h1, h2⟩
    have ht : 0 < t := by
      apply Classical.byContradiction; intro h
      rw [show t = 0 by omega] at hk; omega
    have hq : k / t < t := (Nat.div_lt_iff_lt_mul ht).mpr hk
    have hr : k % t < t := Nat.mod_lt _ ht
    refine ⟨k / t, k % t, hq, hr, ?_, ?_⟩ <;> simp [dec, Nat.div_add_mod, h1, h2, hq, hr]

/-- Lemma 24 for deterministic algorithms, with no cited ingredient: a deterministic cut-query
    algorithm that decides whether Γ_t(x, y) has a triangle asks at least
    t² / (2(2⌈log₂ 3t⌉ + 1)) queries on some input. -/
theorem triangle_det_lb (t : Nat) (A : Alg Bool)
    (hA : ∀ x y, Alg.run (q (3 * t) (gamma t x y)) A = true ↔
      ∃ u v w, u < 3 * t ∧ v < 3 * t ∧ w < 3 * t ∧
        1 ≤ gamma t x y u v ∧ 1 ≤ gamma t x y v w ∧ 1 ≤ gamma t x y u w) :
    ∃ x y, t * t ≤ 2 * (2 * clog (3 * t) + 1) * Alg.cost (q (3 * t) (gamma t x y)) A := by
  let c := 2 * clog (3 * t) + 1
  let P := simQ c (q (3 * t) (gPub t)) (fun x => q (3 * t) (gA t x)) (fun y => q (3 * t) (gB t y)) A
  let P' := Prot.comap (dec t) (dec t) P
  have hP' : ∀ v w, Prot.exec v w P' = true ↔ ∃ k, k < t * t ∧ v k = true ∧ w k = true := by
    intro v w
    rw [(Prot.comap_spec _ _ v w P).1, (triangle_protocol t A (dec t v) (dec t w)).1, hA,
      gamma_triangle_nat, dec_meet]
  obtain ⟨v, hv⟩ := disj_lower (t * t) P' hP'
  refine ⟨dec t v, dec t (fun i => !v i), ?_⟩
  rw [(Prot.comap_spec _ _ v _ P).2, (triangle_protocol t A _ _).2] at hv
  exact hv



end MinKCut
