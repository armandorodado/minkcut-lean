import MinKCut.Certificate
/-! # Part J: query costs (Lemmas 6, 8, 12) -/

namespace MinKCut

/-! ## Part J: query costs (Lemma 8 and the search in Lemma 12)

  A deterministic cut-query algorithm is a decision tree: `Alg α` either returns a value or asks
  the oracle for the cut value of a vertex set and continues with the answer. `Alg.run O A` is
  its output and `Alg.cost O A` the number of queries it makes against the oracle O; both are
  worst-case notions, since O is arbitrary. For a graph G the oracle is O(S) = d_G(S) = `dq n G S`.

  We verify, for every simple graph and every input:
  * `countNb`: two cut queries give e(v, L) once d(v) is known (equation (star-query));
  * `recov`: the bisection of Lemma 8 returns exactly the neighbours of v in a list L with at
    most 2(2 m (⌈log₂|L|⌉ + 1) + 1) queries, where m is the number of those neighbours;
  * `lemma8`: recovering E ∩ Q for an oriented pair set Q costs at most
    Σ_v (1 + 2(2 m_v (⌈log₂ n⌉ + 1) + 1)) = 3n + 4(⌈log₂ n⌉ + 1)·|E ∩ Q| queries, i.e. O(n + M log n);
  * `findOne`: the binary search used in Lemma 12 finds a neighbour of v in L, if there is one,
    with at most 2(⌈log₂|L|⌉ + 1) queries.
  `clog n` is ⌈log₂ n⌉ (`clog_pow`: n ≤ 2^clog n). -/

inductive Alg (α : Type) where
  | ret : α → Alg α
  | ask : (Nat → Bool) → (Nat → Alg α) → Alg α

namespace Alg
def run {α} (O : (Nat → Bool) → Nat) : Alg α → α
  | ret a => a
  | ask S k => run O (k (O S))
def cost {α} (O : (Nat → Bool) → Nat) : Alg α → Nat
  | ret _ => 0
  | ask S k => 1 + cost O (k (O S))
def bind {α β} : Alg α → (α → Alg β) → Alg β
  | ret a, f => f a
  | ask S k, f => ask S (fun r => bind (k r) f)
theorem run_bind {α β} (O : (Nat → Bool) → Nat) (a : Alg α) (f : α → Alg β) :
    run O (bind a f) = run O (f (run O a)) := by
  induction a with
  | ret a => rfl
  | ask S k ih => simp only [bind, run]; exact ih _
theorem cost_bind {α β} (O : (Nat → Bool) → Nat) (a : Alg α) (f : α → Alg β) :
    cost O (bind a f) = cost O a + cost O (f (run O a)) := by
  induction a with
  | ret a => simp [bind, cost, run]
  | ask S k ih => simp only [bind, cost, run]; rw [ih]; omega
def query (S : Nat → Bool) : Alg Nat := ask S ret

theorem run_query (O : (Nat → Bool) → Nat) (S : Nat → Bool) : run O (query S) = O S := rfl
theorem run_ret {α : Type} (O : (Nat → Bool) → Nat) (a : α) : run O (ret a) = a := rfl
theorem cost_ret {α : Type} (O : (Nat → Bool) → Nat) (a : α) : cost O (ret a) = 0 := rfl
theorem cost_query (O : (Nat → Bool) → Nat) (S : Nat → Bool) : cost O (query S) = 1 := rfl
end Alg

def clog (n : Nat) : Nat := if h : n ≤ 1 then 0 else clog ((n + 1) / 2) + 1
termination_by n
decreasing_by omega

def recov (cnt : List Nat → Alg Nat) (L : List Nat) : Alg (List Nat) :=
  match L with
  | [] => .ret []
  | [a] => Alg.bind (cnt [a]) fun c => if c = 0 then .ret [] else .ret [a]
  | a :: b :: rest =>
    Alg.bind (cnt (a :: b :: rest)) fun c =>
      if c = 0 then .ret [] else
        Alg.bind (recov cnt ((a :: b :: rest).take ((rest.length + 2) / 2))) fun A =>
          Alg.bind (recov cnt ((a :: b :: rest).drop ((rest.length + 2) / 2))) fun B => .ret (A ++ B)
termination_by L.length
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem clog_mono : ∀ a b, a ≤ b → clog a ≤ clog b := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b hab
    unfold clog
    by_cases ha : a ≤ 1
    · simp [ha]
    · have hb : ¬ b ≤ 1 := by omega
      simp only [ha, hb, dite_false]
      have := ih ((a + 1) / 2) (by omega) ((b + 1) / 2) (by omega)
      omega

theorem clog_step (n : Nat) (h : 2 ≤ n) : clog n = clog ((n + 1) / 2) + 1 := by
  rw [clog]; simp [show ¬ n ≤ 1 by omega]

/-- clog n = ⌈log₂ n⌉: n ≤ 2^(clog n). -/
theorem clog_pow : ∀ n, n ≤ 2 ^ clog n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases h : n ≤ 1
    · unfold clog; simp [h]
    · rw [clog_step n (by omega), Nat.pow_succ]
      have := ih ((n + 1) / 2) (by omega)
      omega

/-- The bisection is correct and output-sensitive for any test `cnt` that is zero exactly on
    lists without good elements (for instance an exact count of good elements, or a count of
    edges into a union of blocks) and costs at most 2 queries. -/
theorem recov_spec (O : (Nat → Bool) → Nat) (cnt : List Nat → Alg Nat) (good : Nat → Bool)
    (L0 : List Nat)
    (hcnt : ∀ L, L.Sublist L0 → (Alg.run O (cnt L) = 0 ↔ L.filter good = []) ∧ Alg.cost O (cnt L) ≤ 2) :
    ∀ L, L.Sublist L0 → Alg.run O (recov cnt L) = L.filter good ∧
      Alg.cost O (recov cnt L) ≤ 2 * (2 * (L.filter good).length * (clog L.length + 1) + 1) := by
  intro L
  induction L using (measure List.length).wf.induction with
  | h L ih =>
  intro hsub
  match L, ih, hsub with
  | [], _, _ => simp [recov, Alg.run, Alg.cost]
  | [a], _, hsub =>
    obtain ⟨h1, h2⟩ := hcnt [a] hsub
    rw [recov, Alg.run_bind, Alg.cost_bind]
    by_cases hz : Alg.run O (cnt [a]) = 0
    · have := h1.mp hz
      simp only [hz, ite_true, Alg.run, Alg.cost]
      refine ⟨this.symm, ?_⟩
      omega
    · have hne : [a].filter good ≠ [] := fun e => hz (h1.mpr e)
      have hg : good a = true := by
        cases h : good a
        · simp [h] at hne
        · rfl
      simp only [hz, ite_false, Alg.run, Alg.cost]
      refine ⟨by simp [hg], ?_⟩
      simp [hg]; omega
  | a :: b :: rest, ih, hsub =>
    obtain ⟨h1, h2⟩ := hcnt _ hsub
    rw [recov, Alg.run_bind, Alg.cost_bind]
    by_cases hz : Alg.run O (cnt (a :: b :: rest)) = 0
    · have := h1.mp hz
      simp only [hz, ite_true, Alg.run, Alg.cost]
      refine ⟨this.symm, ?_⟩
      omega
    · have hne : (a :: b :: rest).filter good ≠ [] := fun e => hz (h1.mpr e)
      have hpos : 1 ≤ ((a :: b :: rest).filter good).length := by
        cases h : (a :: b :: rest).filter good
        · exact absurd h hne
        · simp
      simp only [hz, ite_false]
      generalize hL : a :: b :: rest = L at *
      generalize hh : (rest.length + 2) / 2 = h
      have hlen : L.length = rest.length + 2 := by rw [← hL]; simp
      have s1 : (L.take h).Sublist L0 := (List.take_sublist _ _).trans hsub
      have s2 : (L.drop h).Sublist L0 := (List.drop_sublist _ _).trans hsub
      obtain ⟨r1, c1⟩ := ih (L.take h) (by show (L.take h).length < L.length; rw [List.length_take]; omega) s1
      obtain ⟨r2, c2⟩ := ih (L.drop h) (by show (L.drop h).length < L.length; rw [List.length_drop]; omega) s2
      rw [Alg.run_bind, Alg.cost_bind, Alg.run_bind, Alg.cost_bind, r1, r2]
      simp only [Alg.run, Alg.cost, Nat.add_zero]
      have hsplit : L.filter good = (L.take h).filter good ++ (L.drop h).filter good := by
        rw [← List.filter_append, List.take_append_drop]
      refine ⟨hsplit.symm, ?_⟩
      have hm : ((L.take h).filter good).length + ((L.drop h).filter good).length
          = (L.filter good).length := by rw [hsplit, List.length_append]
      have hK := clog_step L.length (by omega)
      have k1 : clog (L.take h).length ≤ clog ((L.length + 1) / 2) :=
        clog_mono _ _ (by rw [List.length_take]; omega)
      have k2 : clog (L.drop h).length ≤ clog ((L.length + 1) / 2) :=
        clog_mono _ _ (by rw [List.length_drop]; omega)
      generalize ((L.take h).filter good).length = m1 at *
      generalize ((L.drop h).filter good).length = m2 at *
      generalize (L.filter good).length = m at *
      generalize clog (L.take h).length = a1 at *
      generalize clog (L.drop h).length = a2 at *
      generalize clog ((L.length + 1) / 2) = K at *
      rw [hK]
      have p1 : m1 * (a1 + 1) ≤ m1 * (K + 1) := Nat.mul_le_mul_left _ (by omega)
      have p2 : m2 * (a2 + 1) ≤ m2 * (K + 1) := Nat.mul_le_mul_left _ (by omega)
      have p3 : (m1 + m2) * (K + 1) = m1 * (K + 1) + m2 * (K + 1) := Nat.add_mul _ _ _
      have p4 : m * (K + 1 + 1) = m * (K + 1) + m := by rw [Nat.mul_add, Nat.mul_one]
      have q1 : 2 * m1 * (a1 + 1) = 2 * (m1 * (a1 + 1)) := Nat.mul_assoc _ _ _
      have q2 : 2 * m2 * (a2 + 1) = 2 * (m2 * (a2 + 1)) := Nat.mul_assoc _ _ _
      have q3 : 2 * m * (K + 1 + 1) = 2 * (m * (K + 1 + 1)) := Nat.mul_assoc _ _ _
      subst hm
      omega

/-! ### The binary search of Lemma 12 -/

def descend (cnt : List Nat → Alg Nat) (L : List Nat) : Alg (Option Nat) :=
  match L with
  | [] => .ret none
  | [a] => .ret (some a)
  | a :: b :: rest =>
    Alg.bind (cnt ((a :: b :: rest).take ((rest.length + 2) / 2))) fun c =>
      if c = 0 then descend cnt ((a :: b :: rest).drop ((rest.length + 2) / 2))
      else descend cnt ((a :: b :: rest).take ((rest.length + 2) / 2))
termination_by L.length
decreasing_by
  all_goals simp_wf
  all_goals omega

def findOne (cnt : List Nat → Alg Nat) (L : List Nat) : Alg (Option Nat) :=
  Alg.bind (cnt L) fun c => if c = 0 then .ret none else descend cnt L

theorem descend_spec (O : (Nat → Bool) → Nat) (cnt : List Nat → Alg Nat) (good : Nat → Bool)
    (L0 : List Nat) (cc : Nat)
    (hcnt : ∀ L, L.Sublist L0 → (Alg.run O (cnt L) = 0 ↔ L.filter good = []) ∧ Alg.cost O (cnt L) ≤ cc) :
    ∀ L, L.Sublist L0 → (L.filter good) ≠ [] →
      (∃ u, Alg.run O (descend cnt L) = some u ∧ u ∈ L ∧ good u = true) ∧
      Alg.cost O (descend cnt L) ≤ cc * clog L.length := by
  intro L
  induction L using (measure List.length).wf.induction with
  | h L ih =>
  intro hsub hne
  match L, ih, hsub, hne with
  | [], _, _, hne => simp at hne
  | [a], _, _, hne =>
    have : good a = true := by
      cases h : good a
      · simp [h] at hne
      · rfl
    simp only [descend, Alg.run, Alg.cost]
    exact ⟨⟨a, rfl, by simp, this⟩, Nat.zero_le _⟩
  | a :: b :: rest, ih, hsub, hne =>
    generalize hL : a :: b :: rest = L at *
    have hlen : L.length = rest.length + 2 := by rw [← hL]; simp
    generalize hh : (rest.length + 2) / 2 = h
    have s1 : (L.take h).Sublist L0 := (List.take_sublist _ _).trans hsub
    have s2 : (L.drop h).Sublist L0 := (List.drop_sublist _ _).trans hsub
    obtain ⟨h1, h2⟩ := hcnt _ s1
    have hsplit : L.filter good = (L.take h).filter good ++ (L.drop h).filter good := by
      rw [← List.filter_append, List.take_append_drop]
    have hK := clog_step L.length (by omega)
    have k1 : clog (L.take h).length ≤ clog ((L.length + 1) / 2) :=
      clog_mono _ _ (by rw [List.length_take]; omega)
    have k2 : clog (L.drop h).length ≤ clog ((L.length + 1) / 2) :=
      clog_mono _ _ (by rw [List.length_drop]; omega)
    rw [← hL, descend, hL, hh, Alg.run_bind, Alg.cost_bind]
    by_cases hz : Alg.run O (cnt (L.take h)) = 0
    · simp only [hz, ite_true]
      have hz' := h1.mp hz
      have hne2 : (L.drop h).filter good ≠ [] := by
        intro e; apply hne; rw [hsplit, hz', e]; rfl
      obtain ⟨⟨u, hu1, hu2, hu3⟩, c2⟩ := ih (L.drop h)
        (by show (L.drop h).length < L.length; rw [List.length_drop]; omega) s2 hne2
      refine ⟨⟨u, hu1, (List.drop_sublist _ _).subset hu2, hu3⟩, ?_⟩
      have m1 := Nat.mul_le_mul_left cc k2
      rw [hK, Nat.mul_succ]
      omega
    · simp only [hz, ite_false]
      have hne1 : (L.take h).filter good ≠ [] := fun e => hz (h1.mpr e)
      obtain ⟨⟨u, hu1, hu2, hu3⟩, c1⟩ := ih (L.take h)
        (by show (L.take h).length < L.length; rw [List.length_take]; omega) s1 hne1
      refine ⟨⟨u, hu1, (List.take_sublist _ _).subset hu2, hu3⟩, ?_⟩
      have m1 := Nat.mul_le_mul_left cc k1
      rw [hK, Nat.mul_succ]
      omega

/-- The search used in Lemma 12: `findOne` returns none exactly when L has no good element, and
    otherwise a good element of L, using at most 2(⌈log₂|L|⌉ + 1) queries. -/
theorem findOne_spec (O : (Nat → Bool) → Nat) (cnt : List Nat → Alg Nat) (good : Nat → Bool)
    (L : List Nat) (cc : Nat)
    (hcnt : ∀ L', L'.Sublist L → (Alg.run O (cnt L') = 0 ↔ L'.filter good = []) ∧ Alg.cost O (cnt L') ≤ cc) :
    (Alg.run O (findOne cnt L) = none ↔ L.filter good = []) ∧
    (∀ u, Alg.run O (findOne cnt L) = some u → u ∈ L ∧ good u = true) ∧
    Alg.cost O (findOne cnt L) ≤ cc * (clog L.length + 1) := by
  obtain ⟨h1, h2⟩ := hcnt L (List.Sublist.refl L)
  unfold findOne
  rw [Alg.run_bind, Alg.cost_bind]
  by_cases hz : Alg.run O (cnt L) = 0
  · simp only [hz, ite_true, Alg.run, Alg.cost]
    refine ⟨⟨fun _ => h1.mp hz, fun _ => by simp⟩, fun u h => by simp at h, by rw [Nat.mul_succ]; omega⟩
  · simp only [hz, ite_false]
    have hne : L.filter good ≠ [] := fun e => hz (h1.mpr e)
    obtain ⟨⟨u, hu1, hu2, hu3⟩, c⟩ := descend_spec O cnt good L cc hcnt L (List.Sublist.refl L) hne
    refine ⟨⟨fun h => by rw [hu1] at h; simp at h, fun h => absurd h hne⟩, ?_, by rw [Nat.mul_succ]; omega⟩
    intro u' h'
    rw [hu1] at h'
    cases h'
    exact ⟨hu2, hu3⟩

/-! ### The graph oracle -/

section GraphOracle

variable (n : Nat) (wt : Nat → Nat → Nat)

def setOf (L : List Nat) : Nat → Bool := fun x => L.contains x

/-- Counting the neighbours of v in L with two cut queries, given d(v). -/
def countNb (v dv : Nat) (L : List Nat) : Alg Nat :=
  Alg.bind (Alg.query (setOf L)) fun a =>
    Alg.bind (Alg.query (union (setOf L) (sing v))) fun b => .ret ((dv + a - b) / 2)

theorem e_sing_right (hsym : ∀ x y, wt x y = wt y x) (X : Nat → Bool) (v : Nat) (hv : v < n)
    (hXv : X v = false) : e n wt X (sing v) = 2 * row n wt v X := by
  have hl := D_left n v hv (fun x y => ind (X y) * wt x y)
  have hr := D_right n v hv (fun x y => ind (X x) * wt x y)
  have hsplit : e n wt X (sing v) = D n (fun x y => ind (x == v) * (ind (X y) * wt x y))
      + D n (fun x y => ind (y == v) * (ind (X x) * wt x y)) := by
    unfold e sing; rw [← D_add]; apply D_congr; intro x y _ _
    by_cases hx : x = v <;> by_cases hy : y = v
    · subst hx; subst hy; simp [hXv, ind]
    · subst hx
      have : (y == x) = false := by simp; omega
      cases X y <;> simp [hXv, this, ind]
    · subst hy
      have : (x == y) = false := by simp; omega
      cases X x <;> simp [hXv, this, ind]
    · have h1 : (x == v) = false := by simp; omega
      have h2 : (y == v) = false := by simp; omega
      simp [h1, h2, ind]
  rw [hsplit, hl, hr]
  have : lsum (List.range n) (fun x => ind (X x) * wt x v) = row n wt v X := by
    unfold row; apply lsum_congr; intro x _; rw [hsym x v]
  have h2 : lsum (List.range n) (fun y => ind (X y) * wt v y) = row n wt v X := rfl
  omega

theorem dq_sing (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0) (v : Nat) (hv : v < n) :
    dq n wt (sing v) = deg n wt v := by
  have h1 := q_sing n wt hsym hloop v hv
  have h2 := q_eq_two_dq n wt hsym (sing v)
  omega

/-- The star identity behind (star-query): d(X ∪ {v}) + 2 e(v, X) = d(X) + d(v). -/
theorem star_identity (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (X : Nat → Bool) (v : Nat) (hv : v < n) (hXv : X v = false) :
    dq n wt (union X (sing v)) + 2 * row n wt v X = dq n wt X + deg n wt v := by
  have hc := cross_query n wt X (sing v) (by intro u _; by_cases h : u = v <;> simp [sing, h, hXv])
  rw [q_eq_two_dq n wt hsym X, q_eq_two_dq n wt hsym (sing v), q_eq_two_dq n wt hsym (union X (sing v)),
    e_sing_right n wt hsym X v hv hXv, dq_sing n wt hsym hloop v hv] at hc
  omega

theorem row_setOf (hle1 : ∀ x y, wt x y ≤ 1) (v : Nat) :
    ∀ L : List Nat, L.Nodup → (∀ u, u ∈ L → u < n) →
      row n wt v (setOf L) = (L.filter (fun u => decide (1 ≤ wt v u))).length := by
  intro L
  induction L with
  | nil => intro _ _; unfold row setOf; simp [ind]; exact lsum_zero _
  | cons a L ih =>
    intro hnd hlt
    have haL : a ∉ L := (List.nodup_cons.mp hnd).1
    have ih' := ih (List.nodup_cons.mp hnd).2 (fun u hu => hlt u (by simp [hu]))
    have ha := hlt a (by simp)
    have hp := pick (fun y => wt v y) a n ha
    have hsplit : row n wt v (setOf (a :: L)) = lsum (List.range n) (fun y => ind (y == a) * wt v y)
        + row n wt v (setOf L) := by
      unfold row setOf
      rw [← lsum_add]; apply lsum_congr; intro y _
      by_cases hy : y = a
      · subst hy
        have : L.contains y = false := by simpa using haL
        simp [this, haL, ind]
      · have : (y == a) = false := by simp [hy]
        simp [List.contains_cons, this, hy, ind]
    rw [hsplit, hp, ih']
    have := hle1 v a
    by_cases h : 1 ≤ wt v a
    · simp [List.filter_cons, h]; omega
    · simp [List.filter_cons, h]; omega

/-- `countNb` is correct and costs two queries, on every sublist of a duplicate-free list of
    vertices other than v. -/
theorem countNb_spec (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) (v : Nat) (hv : v < n) (L0 : List Nat) (hnd : L0.Nodup)
    (hlt : ∀ u, u ∈ L0 → u < n) (hvL : v ∉ L0) :
    ∀ L, L.Sublist L0 →
      Alg.run (dq n wt) (countNb v (deg n wt v) L) = (L.filter (fun u => decide (1 ≤ wt v u))).length ∧
      Alg.cost (dq n wt) (countNb v (deg n wt v) L) ≤ 2 := by
  intro L hsub
  have hXv : setOf L v = false := by
    unfold setOf
    have : v ∉ L := fun h => hvL (hsub.subset h)
    simpa using this
  have hst := star_identity n wt hsym hloop (setOf L) v hv hXv
  have hrow := row_setOf n wt hle1 v L (hnd.sublist hsub) (fun u hu => hlt u (hsub.subset hu))
  unfold countNb
  simp only [Alg.run_bind, Alg.cost_bind, Alg.run_query, Alg.cost_query, Alg.run, Alg.cost]
  constructor
  · omega
  · omega

/-- The neighbours of v in L are recovered exactly, with at most 2(2m(⌈log₂|L|⌉+1)+1) queries
    once d(v) is known. -/
theorem recov_graph (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) (v : Nat) (hv : v < n) (L : List Nat) (hnd : L.Nodup)
    (hlt : ∀ u, u ∈ L → u < n) (hvL : v ∉ L) :
    Alg.run (dq n wt) (recov (countNb v (deg n wt v)) L) = L.filter (fun u => decide (1 ≤ wt v u)) ∧
    Alg.cost (dq n wt) (recov (countNb v (deg n wt v)) L)
      ≤ 2 * (2 * (L.filter (fun u => decide (1 ≤ wt v u))).length * (clog L.length + 1) + 1) :=
  recov_spec (dq n wt) _ _ L (fun L' hs => by
    obtain ⟨h1, h2⟩ := countNb_spec n wt hsym hloop hle1 v hv L hnd hlt hvL L' hs
    refine ⟨?_, h2⟩
    rw [h1]
    exact ⟨List.eq_nil_of_length_eq_zero, fun e => by rw [e]; rfl⟩) L (List.Sublist.refl L)

/-- Run an algorithm for every vertex of a list and collect the outputs. -/
def seqAll {β : Type} : List Nat → (Nat → Alg β) → Alg (List β)
  | [], _ => .ret []
  | v :: vs, f => Alg.bind (f v) fun b => Alg.bind (seqAll vs f) fun bs => .ret (b :: bs)

theorem seqAll_spec {β : Type} (O : (Nat → Bool) → Nat) (f : Nat → Alg β) :
    ∀ l : List Nat, Alg.run O (seqAll l f) = l.map (fun v => Alg.run O (f v)) ∧
      Alg.cost O (seqAll l f) = lsum l (fun v => Alg.cost O (f v)) := by
  intro l
  induction l with
  | nil => simp [seqAll, Alg.run, Alg.cost, lsum]
  | cons v vs ih =>
    simp only [seqAll, Alg.run_bind, Alg.cost_bind, ih.1, Alg.run, Alg.cost, lsum, List.map]
    refine ⟨by simp, ?_⟩
    rw [ih.2]; omega

/-- Lemma 8 (output-sensitive pair recovery), with its query count: for an oriented pair set,
    given as lists T v of vertices (duplicate-free, different from v), the algorithm queries d(v)
    and then bisects T v, for every vertex v. It returns exactly the neighbours of v in T v, and
    makes at most Σ_v (1 + 2(2 m_v (⌈log₂ n⌉ + 1) + 1)) cut queries, where m_v is the number of
    those neighbours: O(n + M log n) for M = Σ_v m_v. -/
theorem lemma8 (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) (T : Nat → List Nat)
    (hnd : ∀ v, (T v).Nodup) (hlt : ∀ v u, u ∈ T v → u < n) (hvT : ∀ v, v ∉ T v)
    (hlen : ∀ v, (T v).length ≤ n) :
    let A := seqAll (List.range n) (fun v =>
      Alg.bind (Alg.query (sing v)) fun d => recov (countNb v d) (T v))
    Alg.run (dq n wt) A = (List.range n).map (fun v => (T v).filter (fun u => decide (1 ≤ wt v u))) ∧
    Alg.cost (dq n wt) A ≤ lsum (List.range n) (fun v =>
      1 + 2 * (2 * ((T v).filter (fun u => decide (1 ≤ wt v u))).length * (clog n + 1) + 1)) := by
  intro A
  obtain ⟨hr, hc⟩ := seqAll_spec (dq n wt) (fun v =>
      Alg.bind (Alg.query (sing v)) fun d => recov (countNb v d) (T v)) (List.range n)
  have hstep : ∀ v, v < n →
      Alg.run (dq n wt) (Alg.bind (Alg.query (sing v)) fun d => recov (countNb v d) (T v))
        = (T v).filter (fun u => decide (1 ≤ wt v u)) ∧
      Alg.cost (dq n wt) (Alg.bind (Alg.query (sing v)) fun d => recov (countNb v d) (T v))
        ≤ 1 + 2 * (2 * ((T v).filter (fun u => decide (1 ≤ wt v u))).length * (clog n + 1) + 1) := by
    intro v hv
    rw [Alg.run_bind, Alg.cost_bind, Alg.run_query, Alg.cost_query, dq_sing n wt hsym hloop v hv]
    obtain ⟨r1, c1⟩ := recov_graph n wt hsym hloop hle1 v hv (T v) (hnd v) (hlt v) (hvT v)
    refine ⟨r1, ?_⟩
    have hcl := clog_mono _ _ (hlen v)
    have : 2 * ((T v).filter (fun u => decide (1 ≤ wt v u))).length * (clog (T v).length + 1)
        ≤ 2 * ((T v).filter (fun u => decide (1 ≤ wt v u))).length * (clog n + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  refine ⟨?_, ?_⟩
  · rw [hr]; apply List.map_congr_left; intro v hv; exact (hstep v (List.mem_range.mp hv)).1
  · rw [hc]; apply lsum_mono; intro v hv; exact (hstep v (List.mem_range.mp hv)).2

/-- Lemma 12, case d₁ < D: with d(u) known, a neighbour of u in a duplicate-free list B of other
    vertices is found, or its absence certified, with at most 2(⌈log₂|B|⌉ + 1) cut queries. -/
theorem findNb_graph (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) (u : Nat) (hu : u < n) (B : List Nat) (hnd : B.Nodup)
    (hlt : ∀ x, x ∈ B → x < n) (huB : u ∉ B) :
    (Alg.run (dq n wt) (findOne (countNb u (deg n wt u)) B) = none ↔
        B.filter (fun x => decide (1 ≤ wt u x)) = []) ∧
    (∀ x, Alg.run (dq n wt) (findOne (countNb u (deg n wt u)) B) = some x → x ∈ B ∧ 1 ≤ wt u x) ∧
    Alg.cost (dq n wt) (findOne (countNb u (deg n wt u)) B) ≤ 2 * (clog B.length + 1) := by
  obtain ⟨h1, h2, h3⟩ := findOne_spec (dq n wt) (countNb u (deg n wt u)) (fun x => decide (1 ≤ wt u x)) B 2
    (fun L' hs => by
      obtain ⟨a, b⟩ := countNb_spec n wt hsym hloop hle1 u hu B hnd hlt huB L' hs
      refine ⟨?_, b⟩
      rw [a]
      exact ⟨List.eq_nil_of_length_eq_zero, fun e => by rw [e]; rfl⟩)
  refine ⟨h1, fun x hx => ?_, h3⟩
  obtain ⟨m, g⟩ := h2 x hx
  exact ⟨m, by simpa using g⟩

end GraphOracle

/-! ### Spanning forests with cut queries (the query cost in Lemma 6)

  Prim-style growth: keep a current component C and the list R of untouched vertices. One test
  e(C, R) = d(C) + d(R) - d(C ∪ R) (3 queries) decides whether C can grow; if it can, a binary
  search over R finds a vertex y with a neighbour in C, d(y) is queried, and a binary search over
  C finds that neighbour x; the edge xy is added. Otherwise C is complete and the next component
  starts. Every step moves a vertex out of R, so there are at most n steps of O(log n) queries:
  at most n(6 + 5⌈log₂ n⌉) cut queries in total (`forest_by_queries`). -/

section CutForest

variable (n : Nat) (wt : Nat → Nat → Nat)

/-- e(C,R) (counted over ordered pairs) from three cut queries. -/
def cntE (C R : List Nat) : Alg Nat :=
  Alg.bind (Alg.query (setOf C)) fun a =>
    Alg.bind (Alg.query (setOf R)) fun b =>
      Alg.bind (Alg.query (union (setOf C) (setOf R))) fun c => .ret (a + b - c)

/-- y has a neighbour in C. -/
def hasNb (C : List Nat) (y : Nat) : Bool := C.any (fun x => decide (1 ≤ wt x y))

theorem setOf_true (L : List Nat) (x : Nat) : setOf L x = true ↔ x ∈ L := by
  unfold setOf; simp

theorem hasNb_false (C : List Nat) (y : Nat) (h : hasNb wt C y = false) :
    ∀ x, x ∈ C → wt x y = 0 := by
  intro x hx
  unfold hasNb at h
  have := List.any_eq_false.mp h x hx
  simp at this
  omega

theorem cntE_spec (hsym : ∀ x y, wt x y = wt y x) (C R : List Nat)
    (hCn : ∀ x, x ∈ C → x < n) (hRn : ∀ x, x ∈ R → x < n) (hdisj : ∀ x, x ∈ C → x ∉ R) :
    (Alg.run (dq n wt) (cntE C R) = 0 ↔ R.filter (hasNb wt C) = []) ∧
    Alg.cost (dq n wt) (cntE C R) = 3 := by
  have hcq := cross_query n wt (setOf C) (setOf R) (by
    intro u _
    cases h1 : setOf C u
    · rfl
    · have hu : u ∈ C := (setOf_true C u).mp h1
      have : setOf R u = false := by
        cases h2 : setOf R u
        · rfl
        · exact absurd ((setOf_true R u).mp h2) (hdisj u hu)
      simp [this])
  rw [q_eq_two_dq n wt hsym, q_eq_two_dq n wt hsym, q_eq_two_dq n wt hsym] at hcq
  unfold cntE
  simp only [Alg.run_bind, Alg.cost_bind, Alg.run_query, Alg.cost_query, Alg.run, Alg.cost]
  refine ⟨?_, by simp⟩
  have hval : dq n wt (setOf C) + dq n wt (setOf R) - dq n wt (union (setOf C) (setOf R))
      = e n wt (setOf C) (setOf R) := by omega
  rw [hval]
  constructor
  · intro h0
    apply List.filter_eq_nil_iff.mpr
    intro y hy hgood
    simp only [hasNb, List.any_eq_true, decide_eq_true_eq] at hgood
    obtain ⟨x, hx, hw⟩ := hgood
    have hge := D_ge_term n (fun a b => ind ((setOf C a && setOf R b) || (setOf R a && setOf C b)) * wt a b)
      x y (hCn x hx) (hRn y hy)
    have e1 : setOf C x = true := (setOf_true C x).mpr hx
    have e2 : setOf R y = true := (setOf_true R y).mpr hy
    have hterm : 1 ≤ ind ((setOf C x && setOf R y) || (setOf R x && setOf C y)) * wt x y := by
      rw [e1, e2]; simp [ind]; omega
    dsimp only at hge
    unfold e at h0
    omega
  · intro hnil
    have hR : ∀ y, y ∈ R → hasNb wt C y = false := by
      intro y hy
      cases h : hasNb wt C y
      · rfl
      · exact absurd (List.filter_eq_nil_iff.mp hnil y hy) (by simp [h])
    unfold e
    rw [D_congr n _ (fun _ _ => 0) (fun a b _ _ => by
      by_cases h1 : (setOf C a && setOf R b) = true
      · simp only [Bool.and_eq_true] at h1
        have ha := (setOf_true C a).mp h1.1
        have hb := (setOf_true R b).mp h1.2
        have := hasNb_false wt C b (hR b hb) a ha
        rw [this, Nat.mul_zero]
      · by_cases h2 : (setOf R a && setOf C b) = true
        · simp only [Bool.and_eq_true] at h2
          have ha := (setOf_true R a).mp h2.1
          have hb := (setOf_true C b).mp h2.2
          have := hasNb_false wt C a (hR a ha) b hb
          rw [hsym, this, Nat.mul_zero]
        · simp only [Bool.not_eq_true] at h1 h2
          rw [h1, h2]; simp [ind]), D_zero]

theorem nodup_len : ∀ (n : Nat) (L : List Nat), L.Nodup → (∀ x, x ∈ L → x < n) → L.length ≤ n := by
  intro n
  induction n with
  | zero => intro L _ h; cases L with
    | nil => simp
    | cons a L => exact absurd (h a (by simp)) (by omega)
  | succ n ih =>
    intro L hnd hlt
    have h1 := ih (L.erase n) (hnd.erase n) (by
      intro x hx
      have := (List.Nodup.mem_erase_iff hnd).mp hx
      have := hlt x this.2
      omega)
    by_cases hm : n ∈ L
    · rw [List.length_erase_of_mem hm] at h1; omega
    · rw [List.erase_of_not_mem hm] at h1; omega


/-- The forest of an edge list (symmetric 0/1 weights). -/
def Fw (E : List (Nat × Nat)) (a b : Nat) : Nat :=
  ind (E.any (fun p => (p.1 == a && p.2 == b) || (p.1 == b && p.2 == a)))

theorem Fw_symm (E : List (Nat × Nat)) (a b : Nat) : Fw E a b = Fw E b a := by
  unfold Fw
  have : (E.any (fun p => (p.1 == a && p.2 == b) || (p.1 == b && p.2 == a)))
      = (E.any (fun p => (p.1 == b && p.2 == a) || (p.1 == a && p.2 == b))) := by
    congr 1; funext p; cases (p.1 == a && p.2 == b) <;> cases (p.1 == b && p.2 == a) <;> rfl
  rw [this]

theorem Fw_le_one (E : List (Nat × Nat)) (a b : Nat) : Fw E a b ≤ 1 := by
  unfold Fw ind; split <;> omega

theorem Fw_cons (E : List (Nat × Nat)) (p : Nat × Nat) (a b : Nat) : Fw E a b ≤ Fw (p :: E) a b := by
  unfold Fw
  cases h : E.any (fun p => (p.1 == a && p.2 == b) || (p.1 == b && p.2 == a))
  · simp [ind]
  · simp [List.any_cons, h, ind]

theorem Fw_new (E : List (Nat × Nat)) (x y : Nat) : 1 ≤ Fw ((x, y) :: E) x y := by
  unfold Fw; simp [ind]

theorem Fw_pos (E : List (Nat × Nat)) (a b : Nat) (h : 1 ≤ Fw E a b) :
    ∃ p, p ∈ E ∧ ((p.1 = a ∧ p.2 = b) ∨ (p.1 = b ∧ p.2 = a)) := by
  unfold Fw ind at h
  split at h
  · rename_i hany
    obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp hany
    refine ⟨p, hp, ?_⟩
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hq
    exact hq
  · omega

def grow (C R : List Nat) (done : List (List Nat)) (E : List (Nat × Nat)) :
    Alg (List (List Nat) × List (Nat × Nat)) :=
  match R with
  | [] => .ret (C :: done, E)
  | r :: rest =>
    Alg.bind (cntE C (r :: rest)) fun t =>
      if t = 0 then grow [r] rest (C :: done) E
      else Alg.bind (descend (cntE C) (r :: rest)) fun oy =>
        match oy with
        | none => .ret (C :: done, E)
        | some y =>
          if _hy : y ∈ r :: rest then
            Alg.bind (Alg.query (sing y)) fun dy =>
              Alg.bind (findOne (countNb y dy) C) fun ox =>
                match ox with
                | none => .ret (C :: done, E)
                | some x => grow (y :: C) ((r :: rest).erase y) done ((x, y) :: E)
          else .ret (C :: done, E)
termination_by R.length
decreasing_by
  · simp_wf
  · simp_wf
    rw [List.length_erase_of_mem _hy]
    simp

/-- The invariant of `grow`. -/
def GrowInv (C R : List Nat) (done : List (List Nat)) (E : List (Nat × Nat)) : Prop :=
  (∀ p, p ∈ E → 1 ≤ wt p.1 p.2 ∧ p.1 < n ∧ p.2 < n) ∧
  (∀ x y, x ∈ C → y ∈ C → Reach (Fw E) x y) ∧
  (∀ D, D ∈ done → ∀ x y, x ∈ D → y ∈ D → Reach (Fw E) x y) ∧
  (∀ D, D ∈ done → ∀ x, x ∈ D → ∀ y, y < n → 1 ≤ wt x y → y ∈ D) ∧
  (∀ x, x < n → x ∈ C ∨ x ∈ R ∨ ∃ D, D ∈ done ∧ x ∈ D) ∧
  (C.Nodup ∧ R.Nodup ∧ (∀ x, x ∈ C → x ∉ R) ∧ (∀ x, x ∈ C → x < n) ∧ (∀ x, x ∈ R → x < n)) ∧
  (∀ D, D ∈ done → ∀ x, x ∈ D → x ∉ C ∧ x ∉ R)

/-- What `grow` returns: the components and the edges of a spanning forest. -/
def GrowOut (comps : List (List Nat)) (E : List (Nat × Nat)) : Prop :=
  (∀ p, p ∈ E → 1 ≤ wt p.1 p.2 ∧ p.1 < n ∧ p.2 < n) ∧
  (∀ D, D ∈ comps → ∀ x y, x ∈ D → y ∈ D → Reach (Fw E) x y) ∧
  (∀ D, D ∈ comps → ∀ x, x ∈ D → ∀ y, y < n → 1 ≤ wt x y → y ∈ D) ∧
  (∀ x, x < n → ∃ D, D ∈ comps ∧ x ∈ D)

theorem reach_Fw_cons (E : List (Nat × Nat)) (p : Nat × Nat) {x y : Nat} (h : Reach (Fw E) x y) :
    Reach (Fw (p :: E)) x y := reach_mono _ _ (Fw_cons E p) h

theorem grow_spec (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) :
    ∀ R C done E, GrowInv n wt C R done E →
      GrowOut n wt (Alg.run (dq n wt) (grow C R done E)).1 (Alg.run (dq n wt) (grow C R done E)).2 ∧
      (Alg.run (dq n wt) (grow C R done E)).2.length ≤ E.length + R.length ∧
      Alg.cost (dq n wt) (grow C R done E) ≤ R.length * (6 + 5 * clog n) := by
  intro R
  induction R using (measure List.length).wf.induction with
  | h R ih =>
  intro C done E hI
  obtain ⟨i1, i2, i3, i4, i5, ⟨hCnd, hRnd, hCR, hCn, hRn⟩, i7⟩ := hI
  match R, ih, i5, hRnd, hCR, hRn, i7 with
  | [], _, i5, _, _, _, i7 =>
    simp only [grow, Alg.run, Alg.cost]
    refine ⟨⟨i1, ?_, ?_, ?_⟩, by simp, by simp⟩
    · intro D hD x y hx hy
      rcases List.mem_cons.mp hD with h | h
      · subst h; exact i2 x y hx hy
      · exact i3 D h x y hx hy
    · intro D hD x hx y hy hw
      rcases List.mem_cons.mp hD with h | h
      · subst h
        rcases i5 y hy with h1 | h1 | ⟨D', hD', hyD'⟩
        · exact h1
        · simp at h1
        · have := i4 D' hD' y hyD' x (hCn x hx) (by rw [hsym]; exact hw)
          exact absurd hx (i7 D' hD' x this).1
      · exact i4 D h x hx y hy hw
    · intro x hx
      rcases i5 x hx with h1 | h1 | ⟨D', hD', hxD'⟩
      · exact ⟨C, List.mem_cons_self _ _, h1⟩
      · simp at h1
      · exact ⟨D', List.mem_cons_of_mem _ hD', hxD'⟩
  | r :: rest, ih, i5, hRnd, hCR, hRn, i7 =>
    obtain ⟨hz_iff, hcost3⟩ := cntE_spec n wt hsym C (r :: rest) hCn hRn hCR
    rw [grow, Alg.run_bind, Alg.cost_bind]
    have hrr : r ∉ rest := (List.nodup_cons.mp hRnd).1
    have hrestnd : rest.Nodup := (List.nodup_cons.mp hRnd).2
    by_cases ht : Alg.run (dq n wt) (cntE C (r :: rest)) = 0
    · -- C is complete
      simp only [ht, ite_true]
      have hnil := hz_iff.mp ht
      have hI' : GrowInv n wt [r] rest (C :: done) E := by
        refine ⟨i1, ?_, ?_, ?_, ?_, ⟨by simp, hrestnd, ?_, ?_, ?_⟩, ?_⟩
        · intro x y hx hy; simp at hx hy; subst hx; subst hy; exact Reach.refl _
        · intro D hD x y hx hy
          rcases List.mem_cons.mp hD with h | h
          · subst h; exact i2 x y hx hy
          · exact i3 D h x y hx hy
        · intro D hD x hx y hy hw
          rcases List.mem_cons.mp hD with h | h
          · subst h
            rcases i5 y hy with h1 | h1 | ⟨D', hD', hyD'⟩
            · exact h1
            · exfalso
              have := List.filter_eq_nil_iff.mp hnil y h1
              apply this
              simp only [hasNb, List.any_eq_true, decide_eq_true_eq]
              exact ⟨x, hx, hw⟩
            · have := i4 D' hD' y hyD' x (hCn x hx) (by rw [hsym]; exact hw)
              exact absurd hx (i7 D' hD' x this).1
          · exact i4 D h x hx y hy hw
        · intro x hx
          rcases i5 x hx with h1 | h1 | ⟨D', hD', hxD'⟩
          · exact Or.inr (Or.inr ⟨C, List.mem_cons_self _ _, h1⟩)
          · rcases List.mem_cons.mp h1 with h | h
            · left; simp [h]
            · right; left; exact h
          · exact Or.inr (Or.inr ⟨D', List.mem_cons_of_mem _ hD', hxD'⟩)
        · intro x hx; simp at hx; subst hx; exact hrr
        · intro x hx; simp at hx; subst hx; exact hRn x (List.mem_cons_self _ _)
        · intro x hx; exact hRn x (List.mem_cons_of_mem _ hx)
        · intro D hD x hx
          rcases List.mem_cons.mp hD with h | h
          · subst h
            have hxR := hCR x hx
            constructor
            · intro hxr; simp at hxr; subst hxr; exact hxR (List.mem_cons_self _ _)
            · intro hxr; exact hxR (List.mem_cons_of_mem _ hxr)
          · obtain ⟨a1, a2⟩ := i7 D h x hx
            constructor
            · intro hxr; simp at hxr; subst hxr; exact a2 (List.mem_cons_self _ _)
            · intro hxr; exact a2 (List.mem_cons_of_mem _ hxr)
      obtain ⟨o, hlen, hc⟩ := ih rest (by show rest.length < (r :: rest).length; simp) [r] (C :: done) E hI'
      refine ⟨o, by simp at hlen ⊢; omega, ?_⟩
      have : rest.length * (6 + 5 * clog n) + (6 + 5 * clog n) = (r :: rest).length * (6 + 5 * clog n) := by
        simp [Nat.add_mul]
      omega
    · -- C grows
      simp only [ht, ite_false]
      have hne : (r :: rest).filter (hasNb wt C) ≠ [] := fun e => ht (hz_iff.mpr e)
      have hcnt3 : ∀ L, L.Sublist (r :: rest) →
          (Alg.run (dq n wt) (cntE C L) = 0 ↔ L.filter (hasNb wt C) = []) ∧
          Alg.cost (dq n wt) (cntE C L) ≤ 3 := by
        intro L hL
        obtain ⟨a, b⟩ := cntE_spec n wt hsym C L hCn (fun x hx => hRn x (hL.subset hx))
          (fun x hx hxL => hCR x hx (hL.subset hxL))
        exact ⟨a, by omega⟩
      obtain ⟨⟨y, hy1, hyR, hyg⟩, hcd⟩ := descend_spec (dq n wt) (cntE C) (hasNb wt C) (r :: rest) 3 hcnt3
        (r :: rest) (List.Sublist.refl _) hne
      rw [Alg.run_bind, Alg.cost_bind, hy1]
      simp only [hyR, dite_true]
      rw [Alg.run_bind, Alg.cost_bind, Alg.run_query, Alg.cost_query]
      have hyn : y < n := hRn y hyR
      rw [dq_sing n wt hsym hloop y hyn]
      have hyC : y ∉ C := fun h => hCR y h hyR
      obtain ⟨f1, f2, f3⟩ := findNb_graph n wt hsym hloop hle1 y hyn C hCnd hCn hyC
      have hfne : C.filter (fun x => decide (1 ≤ wt y x)) ≠ [] := by
        intro e
        simp only [hasNb, List.any_eq_true, decide_eq_true_eq] at hyg
        obtain ⟨x, hx, hw⟩ := hyg
        have := List.filter_eq_nil_iff.mp e x hx
        apply this; simp; rw [hsym]; exact hw
      cases hox : Alg.run (dq n wt) (findOne (countNb y (deg n wt y)) C) with
      | none => exact absurd (f1.mp hox) hfne
      | some x =>
        obtain ⟨hxC, hwyx⟩ := f2 x hox
        rw [Alg.run_bind, Alg.cost_bind, hox]
        simp only
        have hxn : x < n := hCn x hxC
        -- the invariant after adding the edge xy
        have hE' : ∀ a b, a ∈ C → b ∈ C → Reach (Fw ((x, y) :: E)) a b :=
          fun a b ha hb => reach_Fw_cons E _ (i2 a b ha hb)
        have hxy : Reach (Fw ((x, y) :: E)) x y := Reach.step (Reach.refl x) (Fw_new E x y)
        have hyx : Reach (Fw ((x, y) :: E)) y x :=
          reach_symm _ (Fw_symm _) hxy
        have hI' : GrowInv n wt (y :: C) ((r :: rest).erase y) done ((x, y) :: E) := by
          refine ⟨?_, ?_, ?_, i4, ?_, ⟨?_, hRnd.erase y, ?_, ?_, ?_⟩, ?_⟩
          · intro p hp
            rcases List.mem_cons.mp hp with h | h
            · subst h; exact ⟨by simp; rw [hsym]; exact hwyx, hxn, hyn⟩
            · exact i1 p h
          · intro a b ha hb
            rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
            · subst h1; subst h2; exact Reach.refl _
            · subst h1; exact reach_trans _ hyx (hE' x b hxC h2)
            · subst h2; exact reach_trans _ (hE' a x h1 hxC) hxy
            · exact hE' a b h1 h2
          · intro D hD a b ha hb; exact reach_Fw_cons E _ (i3 D hD a b ha hb)
          · intro z hz
            rcases i5 z hz with h1 | h1 | h1
            · exact Or.inl (List.mem_cons_of_mem _ h1)
            · by_cases hzy : z = y
              · subst hzy; exact Or.inl (List.mem_cons_self _ _)
              · exact Or.inr (Or.inl ((List.mem_erase_of_ne hzy).mpr h1))
            · exact Or.inr (Or.inr h1)
          · exact List.nodup_cons.mpr ⟨hyC, hCnd⟩
          · intro z hz hzR
            have hzR' := (List.Nodup.mem_erase_iff hRnd).mp hzR
            rcases List.mem_cons.mp hz with h | h
            · exact hzR'.1 h
            · exact hCR z h hzR'.2
          · intro z hz
            rcases List.mem_cons.mp hz with h | h
            · rw [h]; exact hyn
            · exact hCn z h
          · intro z hz
            exact hRn z ((List.Nodup.mem_erase_iff hRnd).mp hz).2
          · intro D hD z hz
            obtain ⟨a1, a2⟩ := i7 D hD z hz
            have hzy : z ≠ y := fun e => a2 (e ▸ hyR)
            constructor
            · intro h; rcases List.mem_cons.mp h with h | h
              · exact hzy h
              · exact a1 h
            · intro h; exact a2 ((List.Nodup.mem_erase_iff hRnd).mp h).2
        have hlen' : ((r :: rest).erase y).length < (r :: rest).length := by
          rw [List.length_erase_of_mem hyR]; simp
        obtain ⟨o, hlen, hc⟩ := ih ((r :: rest).erase y) hlen' (y :: C) done ((x, y) :: E) hI'
        refine ⟨o, ?_, ?_⟩
        · rw [List.length_erase_of_mem hyR] at hlen; simp at hlen ⊢; omega
        · have hCl := nodup_len n C hCnd hCn
          have hRl := nodup_len n (r :: rest) hRnd hRn
          have k1 := clog_mono _ _ hCl
          have k2 := clog_mono _ _ hRl
          have m1 : 3 * clog (r :: rest).length ≤ 3 * clog n := Nat.mul_le_mul_left _ k2
          have m2 : 2 * (clog C.length + 1) ≤ 2 * (clog n + 1) := Nat.mul_le_mul_left _ (by omega)
          rw [List.length_erase_of_mem hyR] at hc
          have : ((r :: rest).length - 1) * (6 + 5 * clog n) + (6 + 5 * clog n)
              = (r :: rest).length * (6 + 5 * clog n) := by
            simp [Nat.add_mul]
          omega

/-- A spanning forest with cut queries: started from all vertices, `grow` returns the edges of a
    spanning forest of G (Spanning in the sense of Part I) with at most n edges, using at most
    n(6 + 5⌈log₂ n⌉) cut queries. -/
theorem forest_by_queries (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) :
    Spanning n (Fw (Alg.run (dq n wt) (grow [] (List.range n) [] [])).2) wt ∧
    (Alg.run (dq n wt) (grow [] (List.range n) [] [])).2.length ≤ n ∧
    Alg.cost (dq n wt) (grow [] (List.range n) [] []) ≤ n * (6 + 5 * clog n) := by
  have hI : GrowInv n wt [] (List.range n) [] [] := by
    refine ⟨by simp, by simp, by simp, by simp, ?_, ⟨by simp, List.nodup_range n, by simp, by simp, ?_⟩, by simp⟩
    · intro x hx; exact Or.inr (Or.inl (List.mem_range.mpr hx))
    · intro x hx; exact List.mem_range.mp hx
  obtain ⟨⟨o1, o2, o3, o4⟩, hlen, hc⟩ := grow_spec n wt hsym hloop hle1 (List.range n) [] [] [] hI
  simp only [List.length_range, List.length_nil, Nat.zero_add] at hlen hc
  refine ⟨⟨?_, ?_, ?_⟩, hlen, hc⟩
  · intro a b
    by_cases h : 1 ≤ Fw (Alg.run (dq n wt) (grow [] (List.range n) [] [])).2 a b
    · obtain ⟨p, hp, hpab⟩ := Fw_pos _ a b h
      have hw := (o1 p hp).1
      have := Fw_le_one (Alg.run (dq n wt) (grow [] (List.range n) [] [])).2 a b
      rcases hpab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hw; omega
      · rw [h1, h2, hsym] at hw; omega
    · omega
  · intro a b h
    obtain ⟨p, hp, hpab⟩ := Fw_pos _ a b h
    obtain ⟨_, h1, h2⟩ := o1 p hp
    rcases hpab with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1 ▸ h1, e2 ▸ h2⟩
    · exact ⟨e2 ▸ h2, e1 ▸ h1⟩
  · intro u v hu hv hw
    obtain ⟨D, hD, huD⟩ := o4 u hu
    exact o2 D hD u v huD (o3 D hD u huD v hv hw)

end CutForest

/-- Simulating an oracle that differs from the real one by a locally known amount: each query to
    O' = O - f is answered by one query to O. This is how the proof of Lemma 6 queries the
    residual graphs G_i (with f = d of the forests already found). -/
def adjust {α : Type} (f : (Nat → Bool) → Nat) : Alg α → Alg α
  | .ret a => .ret a
  | .ask S k => .ask S (fun r => adjust f (k (r - f S)))

theorem adjust_spec {α : Type} (O : (Nat → Bool) → Nat) (f : (Nat → Bool) → Nat) (A : Alg α) :
    Alg.run O (adjust f A) = Alg.run (fun S => O S - f S) A ∧
    Alg.cost O (adjust f A) = Alg.cost (fun S => O S - f S) A := by
  induction A with
  | ret a => exact ⟨rfl, rfl⟩
  | ask S k ih =>
    obtain ⟨h1, h2⟩ := ih (O S - f S)
    exact ⟨h1, by simp only [adjust, Alg.cost]; rw [h2]⟩

/-- The residual oracle: with the packed forests J known, d_{G_i}(S) = d_G(S) - d_J(S). -/
theorem residual_oracle (n : Nat) (G J : Nat → Nat → Nat) (hle : ∀ u v, J u v ≤ G u v)
    (S : Nat → Bool) : dq n (fun u v => G u v - J u v) S = dq n G S - dq n J S := by
  have h := dq_add n J (fun u v => G u v - J u v) S
  have e : (fun u v => J u v + (G u v - J u v)) = G := by
    funext u v; have := hle u v; omega
  rw [e] at h
  omega


/-! ### Lemma 12 in full -/

section Lemma12

variable (n : Nat) (wt : Nat → Nat → Nat)

theorem nodup_append_disj : ∀ (A B : List Nat), (A ++ B).Nodup → ∀ x, x ∈ A → x ∉ B := by
  intro A
  induction A with
  | nil => intro B _ x hx; simp at hx
  | cons a A ih =>
    intro B hnd x hx hxB
    have h1 := (List.nodup_cons.mp hnd).1
    have h2 := (List.nodup_cons.mp hnd).2
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact h1 (List.mem_append_right _ hxB)
    · exact ih B h2 x h hxB

theorem sum_setOf (f : Nat → Nat) : ∀ L : List Nat, L.Nodup → (∀ u, u ∈ L → u < n) →
    lsum (List.range n) (fun x => ind (setOf L x) * f x) = (L.map f).sum := by
  intro L
  induction L with
  | nil => intro _ _; unfold setOf; simp [ind]; exact lsum_zero _
  | cons a L ih =>
    intro hnd hlt
    have haL : a ∉ L := (List.nodup_cons.mp hnd).1
    have ih' := ih (List.nodup_cons.mp hnd).2 (fun u hu => hlt u (by simp [hu]))
    have hp := pick f a n (hlt a (by simp))
    have hsplit : lsum (List.range n) (fun x => ind (setOf (a :: L) x) * f x)
        = lsum (List.range n) (fun x => ind (x == a) * f x) + lsum (List.range n) (fun x => ind (setOf L x) * f x) := by
      unfold setOf
      rw [← lsum_add]; apply lsum_congr; intro y _
      by_cases hy : y = a
      · subst hy
        have : L.contains y = false := by simpa using haL
        simp [this, haL, ind]
      · have : (y == a) = false := by simp [hy]
        simp [List.contains_cons, this, hy, ind]
    rw [hsplit, hp, ih']
    simp

/-- Σ_{x ∈ X} d(x) = d(X) + (edges inside X, over ordered pairs). -/
theorem sumdeg_identity (X : Nat → Bool) :
    lsum (List.range n) (fun x => ind (X x) * deg n wt x) = dq n wt X + inner n wt X := by
  unfold dq inner D deg row
  rw [← lsum_add]
  apply lsum_congr; intro x _
  rw [← lsum_add, ← lsum_mul_left]
  apply lsum_congr; intro y _
  cases h1 : X x <;> cases h2 : X y <;> simp [ind, h1, h2]

/-- Twice the number of edges inside L, from one cut query (degrees known). -/
def cntIn (dg : Nat → Nat) (L : List Nat) : Alg Nat :=
  Alg.bind (Alg.query (setOf L)) fun a => .ret ((L.map dg).sum - a)

theorem cntIn_spec (_hsym : ∀ x y, wt x y = wt y x) (L : List Nat) (hnd : L.Nodup) (hlt : ∀ u, u ∈ L → u < n) :
    (Alg.run (dq n wt) (cntIn (deg n wt) L) = 0 ↔ ∀ x y, x ∈ L → y ∈ L → wt x y = 0) ∧
    Alg.cost (dq n wt) (cntIn (deg n wt) L) = 1 := by
  have hs := sum_setOf n (deg n wt) L hnd hlt
  have hi := sumdeg_identity n wt (setOf L)
  unfold cntIn
  simp only [Alg.run_bind, Alg.cost_bind, Alg.run_query, Alg.cost_query, Alg.run, Alg.cost]
  refine ⟨?_, by simp⟩
  have hv : (L.map (deg n wt)).sum - dq n wt (setOf L) = inner n wt (setOf L) := by omega
  rw [hv]
  constructor
  · intro h0 x y hx hy
    have := D_ge_term n (fun a b => ind (setOf L a && setOf L b) * wt a b) x y (hlt x hx) (hlt y hy)
    have e1 : setOf L x = true := (setOf_true L x).mpr hx
    have e2 : setOf L y = true := (setOf_true L y).mpr hy
    dsimp only at this
    rw [e1, e2] at this
    unfold inner at h0
    simp only [Bool.and_self, ind_true, Nat.one_mul] at this
    omega
  · intro h
    unfold inner
    rw [D_congr n _ (fun _ _ => 0) (fun a b _ _ => by
      by_cases h1 : (setOf L a && setOf L b) = true
      · simp only [Bool.and_eq_true] at h1
        rw [h (a) b ((setOf_true L a).mp h1.1) ((setOf_true L b).mp h1.2), Nat.mul_zero]
      · simp only [Bool.not_eq_true] at h1; rw [h1]; simp [ind]), D_zero]

/-- Find an edge inside X (assumed to exist): bisection on the halves, and a crossing search
    when neither half contains an edge. -/
def findIn (dg : Nat → Nat) (X : List Nat) : Alg (Option (Nat × Nat)) :=
  match X with
  | [a, b] => .ret (some (a, b))
  | a :: b :: c :: rest =>
    Alg.bind (cntIn dg ((a :: b :: c :: rest).take ((rest.length + 3) / 2))) fun t1 =>
      if t1 ≠ 0 then findIn dg ((a :: b :: c :: rest).take ((rest.length + 3) / 2)) else
      Alg.bind (cntIn dg ((a :: b :: c :: rest).drop ((rest.length + 3) / 2))) fun t2 =>
        if t2 ≠ 0 then findIn dg ((a :: b :: c :: rest).drop ((rest.length + 3) / 2)) else
        Alg.bind (descend (cntE ((a :: b :: c :: rest).take ((rest.length + 3) / 2)))
            ((a :: b :: c :: rest).drop ((rest.length + 3) / 2))) fun oy =>
          match oy with
          | none => .ret none
          | some y =>
            Alg.bind (findOne (countNb y (dg y)) ((a :: b :: c :: rest).take ((rest.length + 3) / 2)))
              fun ox =>
                match ox with
                | none => .ret none
                | some x => .ret (some (x, y))
  | _ => .ret none
termination_by X.length
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem findIn_spec (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) :
    ∀ X : List Nat, X.Nodup → (∀ u, u ∈ X → u < n) →
      (∃ x y, x ∈ X ∧ y ∈ X ∧ 1 ≤ wt x y) →
      (∃ p, Alg.run (dq n wt) (findIn (deg n wt) X) = some p ∧ p.1 ∈ X ∧ p.2 ∈ X ∧ 1 ≤ wt p.1 p.2) ∧
      Alg.cost (dq n wt) (findIn (deg n wt) X) ≤ 7 * (clog X.length + 1) := by
  intro X
  induction X using (measure List.length).wf.induction with
  | h X ih =>
  intro hnd hlt hedge
  match X, ih, hnd, hlt, hedge with
  | [], _, _, _, ⟨x, y, hx, _, _⟩ => simp at hx
  | [a], _, _, _, ⟨x, y, hx, hy, hw⟩ =>
    simp at hx hy; subst hx; subst hy; rw [hloop] at hw; omega
  | [a, b], _, _, _, ⟨x, y, hx, hy, hw⟩ =>
    simp only [findIn, Alg.run, Alg.cost]
    refine ⟨⟨(a, b), rfl, by simp, by simp, ?_⟩, by omega⟩
    simp at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rw [hloop] at hw; omega
    · exact hw
    · rw [hsym]; exact hw
    · rw [hloop] at hw; omega
  | a :: b :: c :: rest, ih, hnd, hlt, hedge =>
    generalize hX : a :: b :: c :: rest = X at *
    have hlen : X.length = rest.length + 3 := by rw [← hX]; simp
    generalize hh : (rest.length + 3) / 2 = h
    have hX12 : X.take h ++ X.drop h = X := List.take_append_drop h X
    have hnd12 : (X.take h ++ X.drop h).Nodup := by rw [hX12]; exact hnd
    have nd1 : (X.take h).Nodup := hnd.sublist (List.take_sublist _ _)
    have nd2 : (X.drop h).Nodup := hnd.sublist (List.drop_sublist _ _)
    have lt1 : ∀ u, u ∈ X.take h → u < n := fun u hu => hlt u ((List.take_sublist _ _).subset hu)
    have lt2 : ∀ u, u ∈ X.drop h → u < n := fun u hu => hlt u ((List.drop_sublist _ _).subset hu)
    have disj : ∀ x, x ∈ X.take h → x ∉ X.drop h := nodup_append_disj _ _ hnd12
    have l1 : (X.take h).length < X.length := by rw [List.length_take]; omega
    have l2 : (X.drop h).length < X.length := by rw [List.length_drop]; omega
    have hK := clog_step X.length (by omega)
    have k1 : clog (X.take h).length ≤ clog ((X.length + 1) / 2) :=
      clog_mono _ _ (by rw [List.length_take]; omega)
    have k2 : clog (X.drop h).length ≤ clog ((X.length + 1) / 2) :=
      clog_mono _ _ (by rw [List.length_drop]; omega)
    obtain ⟨c1z, c1c⟩ := cntIn_spec n wt hsym (X.take h) nd1 lt1
    obtain ⟨c2z, c2c⟩ := cntIn_spec n wt hsym (X.drop h) nd2 lt2
    rw [← hX, findIn, hX, hh, Alg.run_bind, Alg.cost_bind]
    by_cases t1 : Alg.run (dq n wt) (cntIn (deg n wt) (X.take h)) = 0
    · simp only [t1, ne_eq, not_true_eq_false, ite_false]
      rw [Alg.run_bind, Alg.cost_bind]
      by_cases t2 : Alg.run (dq n wt) (cntIn (deg n wt) (X.drop h)) = 0
      · simp only [t2, ne_eq, not_true_eq_false, ite_false]
        -- the edge crosses the halves
        have no1 := c1z.mp t1
        have no2 := c2z.mp t2
        obtain ⟨x, y, hx, hy, hw⟩ := hedge
        rw [← hX12] at hx hy
        have cross : ∃ x' y', x' ∈ X.take h ∧ y' ∈ X.drop h ∧ 1 ≤ wt x' y' := by
          rcases List.mem_append.mp hx with hx1 | hx2 <;> rcases List.mem_append.mp hy with hy1 | hy2
          · rw [no1 x y hx1 hy1] at hw; omega
          · exact ⟨x, y, hx1, hy2, hw⟩
          · exact ⟨y, x, hy1, hx2, by rw [hsym]; exact hw⟩
          · rw [no2 x y hx2 hy2] at hw; omega
        obtain ⟨x', y', hx', hy', hw'⟩ := cross
        have hne : (X.drop h).filter (hasNb wt (X.take h)) ≠ [] := by
          intro e
          have := List.filter_eq_nil_iff.mp e y' hy'
          apply this
          simp only [hasNb, List.any_eq_true, decide_eq_true_eq]
          exact ⟨x', hx', hw'⟩
        have hcnt3 : ∀ L, L.Sublist (X.drop h) →
            (Alg.run (dq n wt) (cntE (X.take h) L) = 0 ↔ L.filter (hasNb wt (X.take h)) = []) ∧
            Alg.cost (dq n wt) (cntE (X.take h) L) ≤ 3 := by
          intro L hL
          obtain ⟨p, q⟩ := cntE_spec n wt hsym (X.take h) L lt1 (fun z hz => lt2 z (hL.subset hz))
            (fun z hz hzL => disj z hz (hL.subset hzL))
          exact ⟨p, by omega⟩
        obtain ⟨⟨yy, hy1, hyR, hyg⟩, hcd⟩ := descend_spec (dq n wt) (cntE (X.take h)) (hasNb wt (X.take h))
          (X.drop h) 3 hcnt3 (X.drop h) (List.Sublist.refl _) hne
        rw [Alg.run_bind, Alg.cost_bind, hy1]
        simp only
        have hyyn := lt2 yy hyR
        have hyyC : yy ∉ X.take h := fun hc => disj yy hc hyR
        obtain ⟨f1, f2, f3⟩ := findNb_graph n wt hsym hloop hle1 yy hyyn (X.take h) nd1 lt1 hyyC
        have hfne : (X.take h).filter (fun z => decide (1 ≤ wt yy z)) ≠ [] := by
          intro e
          simp only [hasNb, List.any_eq_true, decide_eq_true_eq] at hyg
          obtain ⟨z, hz, hwz⟩ := hyg
          have := List.filter_eq_nil_iff.mp e z hz
          apply this; simp; rw [hsym]; exact hwz
        cases hox : Alg.run (dq n wt) (findOne (countNb yy (deg n wt yy)) (X.take h)) with
        | none => exact absurd (f1.mp hox) hfne
        | some xx =>
          obtain ⟨hxC, hwyx⟩ := f2 xx hox
          rw [Alg.run_bind, Alg.cost_bind, hox]
          simp only [Alg.run_ret, Alg.cost_ret]
          refine ⟨⟨(xx, yy), rfl, ?_, ?_, ?_⟩, ?_⟩
          · rw [← hX12]; exact List.mem_append_left _ hxC
          · rw [← hX12]; exact List.mem_append_right _ hyR
          · show 1 ≤ wt xx yy; rw [hsym]; exact hwyx
          · have m1 := Nat.mul_le_mul_left 3 (show clog (X.drop h).length ≤ clog X.length by omega)
            have m2 := Nat.mul_le_mul_left 2 (show clog (X.take h).length + 1 ≤ clog X.length + 1 by omega)
            rw [Nat.mul_succ, Nat.mul_succ] at *
            omega
      · simp only [t2, ne_eq, not_false_eq_true, ite_true]
        have hin : ∃ x y, x ∈ X.drop h ∧ y ∈ X.drop h ∧ 1 ≤ wt x y := by
          apply Classical.byContradiction
          intro hno
          apply t2
          apply c2z.mpr
          intro x y hx hy
          have : ¬ 1 ≤ wt x y := fun hw => hno ⟨x, y, hx, hy, hw⟩
          omega
        obtain ⟨⟨p, hp1, hp2, hp3, hp4⟩, hc⟩ := ih (X.drop h) l2 nd2 lt2 hin
        refine ⟨⟨p, hp1, (List.drop_sublist _ _).subset hp2, (List.drop_sublist _ _).subset hp3, hp4⟩, ?_⟩
        have m := Nat.mul_le_mul_left 7 (show clog (X.drop h).length + 1 ≤ clog X.length by omega)
        rw [Nat.mul_succ]
        omega
    · simp only [t1, ne_eq, not_false_eq_true, ite_true]
      have hin : ∃ x y, x ∈ X.take h ∧ y ∈ X.take h ∧ 1 ≤ wt x y := by
        apply Classical.byContradiction
        intro hno
        apply t1
        apply c1z.mpr
        intro x y hx hy
        have : ¬ 1 ≤ wt x y := fun hw => hno ⟨x, y, hx, hy, hw⟩
        omega
      obtain ⟨⟨p, hp1, hp2, hp3, hp4⟩, hc⟩ := ih (X.take h) l1 nd1 lt1 hin
      refine ⟨⟨p, hp1, (List.take_sublist _ _).subset hp2, (List.take_sublist _ _).subset hp3, hp4⟩, ?_⟩
      have m := Nat.mul_le_mul_left 7 (show clog (X.take h).length + 1 ≤ clog X.length by omega)
      rw [Nat.mul_succ]
      omega

/-- An index of least value of f in a list. -/
def amin (f : Nat → Nat) : List Nat → Nat
  | [] => 0
  | a :: l => l.foldl (fun m x => if f x < f m then x else m) a

theorem amin_foldl (f : Nat → Nat) : ∀ (l : List Nat) (m : Nat),
    (l.foldl (fun m x => if f x < f m then x else m) m = m ∨
      l.foldl (fun m x => if f x < f m then x else m) m ∈ l) ∧
    f (l.foldl (fun m x => if f x < f m then x else m) m) ≤ f m ∧
    ∀ x, x ∈ l → f (l.foldl (fun m x => if f x < f m then x else m) m) ≤ f x := by
  intro l
  induction l with
  | nil => intro m; simp
  | cons a l ih =>
    intro m
    simp only [List.foldl_cons]
    by_cases h : f a < f m
    · simp only [h, ite_true]
      obtain ⟨h1, h2, h3⟩ := ih a
      refine ⟨?_, by omega, ?_⟩
      · rcases h1 with e | e
        · right; rw [e]; simp
        · right; exact List.mem_cons_of_mem _ e
      · intro x hx
        rcases List.mem_cons.mp hx with e | e
        · rw [e]; exact h2
        · exact h3 x e
    · simp only [h, ite_false]
      obtain ⟨h1, h2, h3⟩ := ih m
      refine ⟨?_, h2, ?_⟩
      · rcases h1 with e | e
        · left; exact e
        · right; exact List.mem_cons_of_mem _ e
      · intro x hx
        rcases List.mem_cons.mp hx with e | e
        · rw [e]; omega
        · exact h3 x e

theorem amin_spec (f : Nat → Nat) (l : List Nat) (hl : l ≠ []) :
    amin f l ∈ l ∧ ∀ x, x ∈ l → f (amin f l) ≤ f x := by
  match l, hl with
  | a :: l, _ =>
    obtain ⟨h1, h2, h3⟩ := amin_foldl f l a
    refine ⟨?_, ?_⟩
    · rcases h1 with e | e
      · simp only [amin]; rw [e]; simp
      · simp only [amin]; exact List.mem_cons_of_mem _ e
    · intro x hx
      simp only [amin]
      rcases List.mem_cons.mp hx with e | e
      · rw [e]; exact h2
      · exact h3 x e

/-- The algorithm of Lemma 12 (degrees given), for a vertex u0 of least degree and a vertex
    v0 ≠ u0 of least degree among the others. -/
def twoSingCore (dg : Nat → Nat) (u0 v0 : Nat) : Alg (Nat × Nat) :=
  if dg u0 < dg v0 then
    Alg.bind (findOne (countNb u0 (dg u0)) ((List.range n).filter (fun x => dg x == dg v0))) fun o =>
      match o with
      | some v => .ret (u0, v)
      | none => .ret (u0, v0)
  else
    Alg.bind (cntIn dg ((List.range n).filter (fun x => dg x == dg v0))) fun t =>
      if t = 0 then .ret (u0, v0) else
      Alg.bind (findIn dg ((List.range n).filter (fun x => dg x == dg v0))) fun o =>
        match o with
        | some p => .ret p
        | none => .ret (u0, v0)

def twoSing (dg : Nat → Nat) : Alg (Nat × Nat) :=
  twoSingCore n dg (amin dg (List.range n)) (amin dg ((List.range n).filter (fun x => x != amin dg (List.range n))))

theorem twoSingCore_spec (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) (u0 v0 : Nat) (hu0n : u0 < n) (hv0n : v0 < n) (hv0u : v0 ≠ u0)
    (hmin_all : ∀ x, x < n → deg n wt u0 ≤ deg n wt x)
    (hmin_oth : ∀ x, x < n → x ≠ u0 → deg n wt v0 ≤ deg n wt x) :
    (Alg.run (dq n wt) (twoSingCore n (deg n wt) u0 v0)).1 ≠ (Alg.run (dq n wt) (twoSingCore n (deg n wt) u0 v0)).2 ∧
    (Alg.run (dq n wt) (twoSingCore n (deg n wt) u0 v0)).1 < n ∧
    (Alg.run (dq n wt) (twoSingCore n (deg n wt) u0 v0)).2 < n ∧
    (∀ x y, x < n → y < n → x ≠ y →
      cost n wt (labUV (Alg.run (dq n wt) (twoSingCore n (deg n wt) u0 v0)).1
        (Alg.run (dq n wt) (twoSingCore n (deg n wt) u0 v0)).2) ≤ cost n wt (labUV x y)) ∧
    Alg.cost (dq n wt) (twoSingCore n (deg n wt) u0 v0) ≤ 7 * (clog n + 1) + 1 := by
  have F1 : ∀ x y, x < n → y < n → x ≠ y → deg n wt u0 + deg n wt v0 ≤ deg n wt x + deg n wt y := by
    intro x y hx hy hxy
    by_cases h1 : x = u0
    · subst h1; have := hmin_oth y hy (fun e => hxy e.symm); omega
    · by_cases h2 : y = u0
      · subst h2; have := hmin_oth x hx h1; omega
      · have := hmin_oth x hx h1; have := hmin_oth y hy h2; have := hmin_all v0 hv0n; omega
  have hcost : ∀ x y, x < n → y < n → x ≠ y →
      cost n wt (labUV x y) + 2 * wt x y = 2 * (deg n wt x + deg n wt y) :=
    fun x y hx hy hxy => two_singleton_value n wt hsym hloop x y hx hy hxy
  have opt_edge : ∀ a b, a < n → b < n → a ≠ b → deg n wt a + deg n wt b = deg n wt u0 + deg n wt v0 →
      1 ≤ wt a b → ∀ x y, x < n → y < n → x ≠ y → cost n wt (labUV a b) ≤ cost n wt (labUV x y) := by
    intro a b ha hb hab hs hw x y hx hy hxy
    have := hcost a b ha hb hab; have := hcost x y hx hy hxy
    have := F1 x y hx hy hxy; have := hle1 a b; have := hle1 x y
    omega
  have opt_noedge : ∀ a b, a < n → b < n → a ≠ b → deg n wt a + deg n wt b = deg n wt u0 + deg n wt v0 →
      wt a b = 0 →
      (∀ x y, x < n → y < n → x ≠ y → deg n wt x + deg n wt y = deg n wt u0 + deg n wt v0 → wt x y = 0) →
      ∀ x y, x < n → y < n → x ≠ y → cost n wt (labUV a b) ≤ cost n wt (labUV x y) := by
    intro a b ha hb hab hs hw hall x y hx hy hxy
    have := hcost a b ha hb hab; have := hcost x y hx hy hxy
    have := F1 x y hx hy hxy; have := hle1 x y
    by_cases hsum : deg n wt x + deg n wt y = deg n wt u0 + deg n wt v0
    · have := hall x y hx hy hxy hsum; omega
    · omega
  unfold twoSingCore
  generalize hB : (List.range n).filter (fun x => deg n wt x == deg n wt v0) = B
  have hBdeg : ∀ x, x ∈ B ↔ x < n ∧ deg n wt x = deg n wt v0 := by
    intro x; rw [← hB]; simp [List.mem_filter, List.mem_range]
  have hBnd : B.Nodup := by rw [← hB]; exact (List.nodup_range n).filter _
  have hBlt : ∀ x, x ∈ B → x < n := fun x hx => ((hBdeg x).mp hx).1
  have hBlen : B.length ≤ n := by
    have := List.length_filter_le (fun x => deg n wt x == deg n wt v0) (List.range n)
    rw [hB] at this; simpa using this
  have hcl : clog B.length ≤ clog n := clog_mono _ _ hBlen
  by_cases hstrict : deg n wt u0 < deg n wt v0
  · rw [if_pos hstrict]
    have hu0B : u0 ∉ B := by intro h; have := ((hBdeg u0).mp h).2; omega
    obtain ⟨f1, f2, f3⟩ := findNb_graph n wt hsym hloop hle1 u0 hu0n B hBnd hBlt hu0B
    rw [Alg.run_bind, Alg.cost_bind]
    cases ho : Alg.run (dq n wt) (findOne (countNb u0 (deg n wt u0)) B) with
    | some v =>
      obtain ⟨hvB, hw⟩ := f2 v ho
      obtain ⟨hvn, hvd⟩ := (hBdeg v).mp hvB
      have hvu : u0 ≠ v := fun e => hu0B (e ▸ hvB)
      simp only [Alg.run_ret, Alg.cost_ret]
      refine ⟨hvu, hu0n, hvn, opt_edge u0 v hu0n hvn hvu (by omega) hw, ?_⟩
      have := Nat.mul_le_mul_left 2 (show clog B.length + 1 ≤ clog n + 1 by omega)
      omega
    | none =>
      have hnil := f1.mp ho
      simp only [Alg.run_ret, Alg.cost_ret]
      refine ⟨hv0u.symm, hu0n, hv0n, ?_, ?_⟩
      · apply opt_noedge u0 v0 hu0n hv0n hv0u.symm rfl
        · have := List.filter_eq_nil_iff.mp hnil v0 ((hBdeg v0).mpr ⟨hv0n, rfl⟩)
          simp at this; have := hle1 u0 v0; omega
        · intro x y hx hy hxy hs
          by_cases hxu : x = u0
          · subst hxu
            have hyB : y ∈ B := (hBdeg y).mpr ⟨hy, by omega⟩
            have := List.filter_eq_nil_iff.mp hnil y hyB
            simp at this; have := hle1 x y; omega
          · by_cases hyu : y = u0
            · subst hyu
              have hxB : x ∈ B := (hBdeg x).mpr ⟨hx, by omega⟩
              have := List.filter_eq_nil_iff.mp hnil x hxB
              simp at this; rw [hsym]; have := hle1 y x; omega
            · have := hmin_oth x hx hxu; have := hmin_oth y hy hyu; omega
      · have := Nat.mul_le_mul_left 2 (show clog B.length + 1 ≤ clog n + 1 by omega)
        omega
  · rw [if_neg hstrict]
    have heq : deg n wt u0 = deg n wt v0 := by have := hmin_all v0 hv0n; omega
    obtain ⟨cz, cc⟩ := cntIn_spec n wt hsym B hBnd hBlt
    rw [Alg.run_bind, Alg.cost_bind]
    have pairB : ∀ x y, x < n → y < n → deg n wt x + deg n wt y = deg n wt u0 + deg n wt v0 →
        x ∈ B ∧ y ∈ B := by
      intro x y hx hy hs
      have := hmin_all x hx; have := hmin_all y hy
      exact ⟨(hBdeg x).mpr ⟨hx, by omega⟩, (hBdeg y).mpr ⟨hy, by omega⟩⟩
    by_cases ht : Alg.run (dq n wt) (cntIn (deg n wt) B) = 0
    · rw [if_pos ht]
      have hnone := cz.mp ht
      simp only [Alg.run_ret, Alg.cost_ret]
      refine ⟨hv0u.symm, hu0n, hv0n, ?_, by omega⟩
      apply opt_noedge u0 v0 hu0n hv0n hv0u.symm rfl
      · exact hnone u0 v0 ((hBdeg u0).mpr ⟨hu0n, heq⟩) ((hBdeg v0).mpr ⟨hv0n, rfl⟩)
      · intro x y hx hy _ hs
        obtain ⟨hxB, hyB⟩ := pairB x y hx hy hs
        exact hnone x y hxB hyB
    · rw [if_neg ht]
      have hin : ∃ x y, x ∈ B ∧ y ∈ B ∧ 1 ≤ wt x y := by
        apply Classical.byContradiction
        intro hno
        apply ht; apply cz.mpr
        intro x y hx hy
        have : ¬ 1 ≤ wt x y := fun hw => hno ⟨x, y, hx, hy, hw⟩
        omega
      obtain ⟨⟨q, hq1, hq2, hq3, hq4⟩, hqc⟩ := findIn_spec n wt hsym hloop hle1 B hBnd hBlt hin
      rw [Alg.run_bind, Alg.cost_bind, hq1]
      simp only [Alg.run_ret, Alg.cost_ret]
      have hqne : q.1 ≠ q.2 := by intro e; rw [e, hloop] at hq4; omega
      obtain ⟨hq1n, hq1d⟩ := (hBdeg q.1).mp hq2
      obtain ⟨hq2n, hq2d⟩ := (hBdeg q.2).mp hq3
      refine ⟨hqne, hq1n, hq2n, opt_edge q.1 q.2 hq1n hq2n hqne (by omega) hq4, ?_⟩
      have := Nat.mul_le_mul_left 7 (show clog B.length + 1 ≤ clog n + 1 by omega)
      omega

/-- Lemma 12 (optimizing two-singleton cuts). For every simple graph on n ≥ 2 vertices, once the
    degrees are known, `twoSing` returns two distinct vertices u, v such that the partition
    ({u}, {v}, V ∖ {u,v}) has least cost among all two-singleton partitions, using at most
    7(⌈log₂ n⌉ + 1) + 1 = O(log n) further cut queries. -/
theorem lemma12 (hsym : ∀ x y, wt x y = wt y x) (hloop : ∀ x, wt x x = 0)
    (hle1 : ∀ x y, wt x y ≤ 1) (hn : 2 ≤ n) :
    (Alg.run (dq n wt) (twoSing n (deg n wt))).1 ≠ (Alg.run (dq n wt) (twoSing n (deg n wt))).2 ∧
    (Alg.run (dq n wt) (twoSing n (deg n wt))).1 < n ∧
    (Alg.run (dq n wt) (twoSing n (deg n wt))).2 < n ∧
    (∀ x y, x < n → y < n → x ≠ y →
      cost n wt (labUV (Alg.run (dq n wt) (twoSing n (deg n wt))).1
        (Alg.run (dq n wt) (twoSing n (deg n wt))).2) ≤ cost n wt (labUV x y)) ∧
    Alg.cost (dq n wt) (twoSing n (deg n wt)) ≤ 7 * (clog n + 1) + 1 := by
  have hr : List.range n ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  obtain ⟨hu0m, hu0min⟩ := amin_spec (deg n wt) (List.range n) hr
  generalize hu : amin (deg n wt) (List.range n) = u0 at hu0m hu0min
  have hu0n : u0 < n := List.mem_range.mp hu0m
  have hoth : (List.range n).filter (fun x => x != u0) ≠ [] := by
    intro h
    have hx : (if u0 = 0 then 1 else 0) ∈ (List.range n).filter (fun x => x != u0) := by
      simp only [List.mem_filter, List.mem_range, bne_iff_ne, ne_eq, decide_eq_true_eq]
      constructor
      · split <;> omega
      · split <;> omega
    rw [h] at hx; simp at hx
  obtain ⟨hv0m, hv0min⟩ := amin_spec (deg n wt) _ hoth
  generalize hv : amin (deg n wt) ((List.range n).filter (fun x => x != u0)) = v0 at hv0m hv0min
  have hv0n : v0 < n := List.mem_range.mp (List.mem_filter.mp hv0m).1
  have hv0u : v0 ≠ u0 := by have := (List.mem_filter.mp hv0m).2; simpa using this
  have hall : ∀ x, x < n → deg n wt u0 ≤ deg n wt x := fun x hx => hu0min x (List.mem_range.mpr hx)
  have hoth' : ∀ x, x < n → x ≠ u0 → deg n wt v0 ≤ deg n wt x := by
    intro x hx hxu; apply hv0min
    simp only [List.mem_filter, List.mem_range, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨hx, hxu⟩
  unfold twoSing
  rw [hu, hv]
  exact twoSingCore_spec n wt hsym hloop hle1 u0 v0 hu0n hv0n hv0u hall hoth'

end Lemma12


/-! ### Lemma 6 with its query cost -/

section Lemma6Queries

variable (n : Nat) (G : Nat → Nat → Nat)

/-- The forests found so far, as weight functions. -/
def FL (acc : List (List (Nat × Nat))) (i : Nat) : Nat → Nat → Nat := Fw (acc.getD i [])

/-- r rounds: in each, run `grow` against the residual oracle d_G - d_J, simulated with one
    query to d_G per query (J = the forests found so far, known locally). -/
def rounds : Nat → List (List (Nat × Nat)) → Alg (List (List (Nat × Nat)))
  | 0, acc => .ret acc
  | k + 1, acc =>
    Alg.bind (adjust (fun S => dq n (packed (FL acc) acc.length) S) (grow [] (List.range n) [] []))
      fun res => rounds k (acc ++ [res.2])

def Fit (acc : List (List (Nat × Nat))) : Prop :=
  (∀ a b, packed (FL acc) acc.length a b ≤ G a b) ∧
  (∀ i, i < acc.length → Spanning n (FL acc i) (residual G (FL acc) i))

theorem FL_append (acc : List (List (Nat × Nat))) (E : List (Nat × Nat)) (i : Nat) (hi : i < acc.length) :
    FL (acc ++ [E]) i = FL acc i := by
  unfold FL; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem FL_last (acc : List (List (Nat × Nat))) (E : List (Nat × Nat)) :
    FL (acc ++ [E]) acc.length = Fw E := by
  unfold FL; simp [List.getD_eq_getElem?_getD]

theorem packed_symm (acc : List (List (Nat × Nat))) (i a b : Nat) :
    packed (FL acc) i a b = packed (FL acc) i b a := by
  unfold packed; apply lsum_congr; intro j _; unfold FL; exact Fw_symm _ _ _

theorem rounds_spec (hsym : ∀ x y, G x y = G y x) (hloop : ∀ x, G x x = 0) (hle1 : ∀ x y, G x y ≤ 1) :
    ∀ k acc, Fit n G acc →
      let L := Alg.run (dq n G) (rounds n k acc)
      L.length = acc.length + k ∧ Fit n G L ∧
      Alg.cost (dq n G) (rounds n k acc) ≤ k * (n * (6 + 5 * clog n)) := by
  intro k
  induction k with
  | zero => intro acc h; simp [rounds, Alg.run, Alg.cost, h]
  | succ k ih =>
    intro acc hfit
    obtain ⟨hpk, hsp⟩ := hfit
    -- the residual graph is simple
    let Rw := residual G (FL acc) acc.length
    have rs : ∀ x y, Rw x y = Rw y x := by
      intro x y; show G x y - _ = G y x - _; rw [hsym, packed_symm]
    have rl : ∀ x, Rw x x = 0 := by intro x; show G x x - _ = 0; rw [hloop]; simp
    have r1 : ∀ x y, Rw x y ≤ 1 := by intro x y; show G x y - _ ≤ 1; have := hle1 x y; omega
    obtain ⟨hspan, _, hcost⟩ := forest_by_queries n Rw rs rl r1
    -- the simulated oracle is the residual oracle
    have horacle : (fun S => dq n G S - dq n (packed (FL acc) acc.length) S) = dq n Rw := by
      funext S
      show _ = dq n (fun u v => G u v - packed (FL acc) acc.length u v) S
      rw [residual_oracle n G (packed (FL acc) acc.length) hpk S]
    obtain ⟨ar, ac⟩ := adjust_spec (dq n G) (fun S => dq n (packed (FL acc) acc.length) S)
      (grow [] (List.range n) [] [])
    rw [horacle] at ar ac
    simp only [rounds, Alg.run_bind, Alg.cost_bind, ar, ac]
    generalize hE : (Alg.run (dq n Rw) (grow [] (List.range n) [] [])).2 = E at hspan
    -- the extended list still fits
    have hfit' : Fit n G (acc ++ [E]) := by
      constructor
      · intro a b
        have e1 : packed (FL (acc ++ [E])) (acc ++ [E]).length a b
            = packed (FL acc) acc.length a b + Fw E a b := by
          simp only [List.length_append, List.length_singleton]
          unfold packed
          rw [List.range_succ, lsum_append]
          simp only [lsum, Nat.add_zero]
          rw [← FL_last acc E]
          have : lsum (List.range acc.length) (fun j => FL (acc ++ [E]) j a b)
              = lsum (List.range acc.length) (fun j => FL acc j a b) := by
            apply lsum_congr; intro j hj; rw [FL_append acc E j (List.mem_range.mp hj)]
          rw [this]
        rw [e1]
        have := hspan.1 a b
        show _ ≤ G a b
        have h2 := hpk a b
        simp only [Rw, residual] at this
        omega
      · intro i hi
        simp only [List.length_append, List.length_singleton] at hi
        have hres : residual G (FL (acc ++ [E])) i = residual G (FL acc) i := by
          funext a b; unfold residual
          rw [packed_congr (FL (acc ++ [E])) (FL acc) acc.length
            (fun j hj => FL_append acc E j hj) i (by omega) a b]
        rw [hres]
        by_cases hlt : i < acc.length
        · rw [FL_append acc E i hlt]; exact hsp i hlt
        · have : i = acc.length := by omega
          subst this
          rw [FL_last]; exact hspan
    obtain ⟨hl, hf, hc⟩ := ih (acc ++ [E]) hfit'
    refine ⟨by simp at hl ⊢; omega, hf, ?_⟩
    have : (k + 1) * (n * (6 + 5 * clog n)) = k * (n * (6 + 5 * clog n)) + n * (6 + 5 * clog n) := by
      rw [Nat.succ_mul]
    omega

/-- Lemma 6 with its query cost: r rounds of cut-query spanning forests, each run against the
    residual graph (simulated with one cut query of G per query), use at most
    r·n(6 + 5⌈log₂ n⌉) = O(rn log n) cut queries, and the union J of the r forests found
    satisfies min{r, d_J(S)} = min{r, d_G(S)} for every vertex set S. -/
theorem lemma6_queries (hsym : ∀ x y, G x y = G y x) (hloop : ∀ x, G x x = 0) (hle1 : ∀ x y, G x y ≤ 1)
    (r : Nat) :
    let L := Alg.run (dq n G) (rounds n r [])
    (∀ S : Nat → Bool, min r (dq n (packed (FL L) r) S) = min r (dq n G S)) ∧
    Alg.cost (dq n G) (rounds n r []) ≤ r * (n * (6 + 5 * clog n)) := by
  have h0 : Fit n G [] := ⟨fun a b => by simp [packed, lsum], fun i hi => absurd hi (by simp)⟩
  obtain ⟨hl, ⟨hpk, hsp⟩, hc⟩ := rounds_spec n G hsym hloop hle1 r [] h0
  simp only [List.length_nil, Nat.zero_add] at hl
  refine ⟨?_, hc⟩
  intro S
  have := forest_certificate n G (FL (Alg.run (dq n G) (rounds n r []))) r
    (fun a b => by have := hpk a b; rwa [hl] at this) (fun i hi => hsp i (by omega)) S
  exact this

end Lemma6Queries



end MinKCut
