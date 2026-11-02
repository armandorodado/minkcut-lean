import MinKCut.LowerBounds
/-! # Part Q: expected to worst-case query bounds -/

namespace MinKCut

/-! ## Part Q: from expected to worst-case query bounds (end of the proof of Lemma 27)

  A randomized algorithm is a family A r of decision trees indexed by S equally likely seeds
  r < S. Truncating every run at T queries gives worst-case cost ≤ T, and changes the output
  only on seeds whose run is longer than T; by Markov's inequality there are at most C·S/(T+1)
  of these when the expected cost is at most C. -/

/-- Stop after T queries and output d. -/
def trunc {α : Type} (d : α) : Nat → Alg α → Alg α
  | _, .ret a => .ret a
  | 0, .ask _ _ => .ret d
  | T + 1, .ask S k => .ask S (fun r => trunc d T (k r))

theorem trunc_cost {α : Type} (O : (Nat → Bool) → Nat) (d : α) : ∀ T (A : Alg α),
    Alg.cost O (trunc d T A) ≤ T := by
  intro T
  induction T with
  | zero => intro A; cases A <;> simp [trunc, Alg.cost]
  | succ T ih =>
    intro A; cases A with
    | ret a => simp [trunc, Alg.cost]
    | ask S k => simp only [trunc, Alg.cost]; have := ih (k (O S)); omega

theorem trunc_run {α : Type} (O : (Nat → Bool) → Nat) (d : α) : ∀ T (A : Alg α),
    Alg.cost O A ≤ T → Alg.run O (trunc d T A) = Alg.run O A := by
  intro T
  induction T with
  | zero => intro A h; cases A with
    | ret a => rfl
    | ask S k => simp [Alg.cost] at h
  | succ T ih =>
    intro A h; cases A with
    | ret a => rfl
    | ask S k => simp only [trunc, Alg.run]; simp only [Alg.cost] at h; exact ih _ (by omega)

/-- Markov's inequality, counting form: (T+1)·#{r < S : c r > T} ≤ Σ_{r<S} c r. -/
theorem markov_count (c : Nat → Nat) (T : Nat) : ∀ S,
    (T + 1) * cnt S (fun r => decide (T < c r)) ≤ lsum (List.range S) c := by
  intro S
  induction S with
  | zero => simp [cnt, lsum]
  | succ S ih =>
    rw [cnt_succ, List.range_succ, lsum_append]; simp only [lsum]
    rw [Nat.mul_add]
    by_cases h : T < c S
    · simp [h, ind]; omega
    · simp [h, ind]; omega

theorem cnt_or_le (S : Nat) (P Q : Nat → Bool) : cnt S (fun r => P r || Q r) ≤ cnt S P + cnt S Q := by
  unfold cnt; rw [← lsum_add]; apply lsum_mono; intro r _
  cases hp : P r <;> cases hq : Q r <;> simp [ind, hp, hq]

/-- Expected-to-worst-case: if on some input the S seeds have total cost at most C·S and at most
    E of them give a wrong output, then the truncated algorithm has worst-case cost ≤ T and at most
    E + C·S/(T+1) wrong seeds; e.g. T + 1 = 7C turns error 1/3 into error < 1/2. -/
theorem truncate_errors {α : Type} (O : (Nat → Bool) → Nat) (d : α) (good : α → Bool) (A : Nat → Alg α)
    (S C T E : Nat) (hcost : lsum (List.range S) (fun r => Alg.cost O (A r)) ≤ C * S)
    (herr : cnt S (fun r => !good (Alg.run O (A r))) ≤ E) :
    (∀ r, Alg.cost O (trunc d T (A r)) ≤ T) ∧
    (T + 1) * cnt S (fun r => !good (Alg.run O (trunc d T (A r)))) ≤ (T + 1) * E + C * S := by
  refine ⟨fun r => trunc_cost O d T (A r), ?_⟩
  have h1 : cnt S (fun r => !good (Alg.run O (trunc d T (A r)))) ≤
      cnt S (fun r => !good (Alg.run O (A r)) || decide (T < Alg.cost O (A r))) := by
    apply cnt_mono_set; intro r _ h
    by_cases hc : Alg.cost O (A r) ≤ T
    · rw [trunc_run O d T (A r) hc] at h; simp [h]
    · simp [show T < Alg.cost O (A r) by omega]
  have h2 := cnt_or_le S (fun r => !good (Alg.run O (A r))) (fun r => decide (T < Alg.cost O (A r)))
  have h3 := markov_count (fun r => Alg.cost O (A r)) T S
  have h4 := Nat.mul_le_mul_left (T + 1) (Nat.le_trans h1 h2)
  rw [Nat.mul_add] at h4
  have h5 := Nat.mul_le_mul_left (T + 1) herr
  omega


end MinKCut
