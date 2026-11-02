/-! # Basic definitions (sums, cuts, costs) and Part A: cut identities -/

namespace MinKCut


/-! ## Finite sums -/

def ind (b : Bool) : Nat := if b then 1 else 0

def lsum : List Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | a :: l, f => f a + lsum l f

theorem lsum_mono (l : List Nat) (f g : Nat → Nat) (h : ∀ a, a ∈ l → f a ≤ g a) :
    lsum l f ≤ lsum l g := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih =>
    simp only [lsum]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    omega

theorem lsum_add (l : List Nat) (f g : Nat → Nat) :
    lsum l (fun a => f a + g a) = lsum l f + lsum l g := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih => simp only [lsum, ih]; omega

theorem lsum_congr (l : List Nat) (f g : Nat → Nat) (h : ∀ a, a ∈ l → f a = g a) :
    lsum l f = lsum l g := by
  have h1 := lsum_mono l f g (fun a ha => Nat.le_of_eq (h a ha))
  have h2 := lsum_mono l g f (fun a ha => Nat.le_of_eq (h a ha).symm)
  omega

theorem lsum_append (l₁ l₂ : List Nat) (f : Nat → Nat) :
    lsum (l₁ ++ l₂) f = lsum l₁ f + lsum l₂ f := by
  induction l₁ with
  | nil => simp [lsum]
  | cons a l ih =>
    rw [List.cons_append]
    simp only [lsum]
    rw [ih]
    omega

theorem lsum_zero (l : List Nat) : lsum l (fun _ => 0) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [lsum, ih]

theorem lsum_mul (l : List Nat) (f : Nat → Nat) (w : Nat) :
    lsum l (fun a => f a * w) = lsum l f * w := by
  induction l with
  | nil => simp [lsum]
  | cons a l ih => simp only [lsum, ih, Nat.add_mul]

theorem count_one (a : Nat) (c : Bool) :
    ∀ k, lsum (List.range k) (fun i => ind ((a == i) && c)) = ind (decide (a < k) && c) := by
  intro k
  induction k with
  | zero => simp [lsum, ind]
  | succ k ih =>
    rw [List.range_succ, lsum_append, ih]
    simp only [lsum]
    cases c
    · simp [ind]
    · by_cases h1 : a < k
      · have h2 : a ≠ k := by omega
        have h3 : a < k + 1 := by omega
        simp [ind, h1, h2, h3]
      · by_cases h2 : a = k
        · subst h2; simp [ind]
        · have h3 : ¬ a < k + 1 := by omega
          simp [ind, h1, h2, h3]

theorem pt_count (a b i : Nat) :
    ind ((a == i) != (b == i)) = ind ((a == i) && (a != b)) + ind ((b == i) && (a != b)) := by
  by_cases ha : a = i
  · subst ha
    by_cases hb : b = a
    · subst hb; simp [ind]
    · have hb' : a ≠ b := fun h => hb h.symm
      simp [ind, hb, hb']
  · by_cases hb : b = i
    · subst hb
      simp [ind, ha]
    · have h1 : (a == i) = false := by simpa using ha
      have h2 : (b == i) = false := by simpa using hb
      rw [h1, h2]; simp [ind]

/-- Σ_{i<k} [ (a = i) ≠ (b = i) ] = 2·[a ≠ b] for a, b < k. -/
theorem count_parts (a b k : Nat) (ha : a < k) (hb : b < k) :
    lsum (List.range k) (fun i => ind ((a == i) != (b == i))) = 2 * ind (a != b) := by
  rw [lsum_congr _ _ _ (fun i _ => pt_count a b i), lsum_add, count_one, count_one]
  simp [ha, hb]
  omega

section Graph

variable (n : Nat) (wt : Nat → Nat → Nat)

/-- Double sum over ordered pairs of vertices 0, ..., n-1. -/
def D (f : Nat → Nat → Nat) : Nat :=
  lsum (List.range n) (fun u => lsum (List.range n) (fun v => f u v))

theorem D_mono (f g : Nat → Nat → Nat) (h : ∀ u v, u < n → v < n → f u v ≤ g u v) :
    D n f ≤ D n g := by
  unfold D
  apply lsum_mono
  intro u hu
  apply lsum_mono
  intro v hv
  exact h u v (List.mem_range.mp hu) (List.mem_range.mp hv)

theorem D_add (f g : Nat → Nat → Nat) :
    D n (fun u v => f u v + g u v) = D n f + D n g := by
  unfold D
  rw [← lsum_add]
  apply lsum_congr
  intro u _
  exact lsum_add _ _ _

theorem D_congr (f g : Nat → Nat → Nat) (h : ∀ u v, u < n → v < n → f u v = g u v) :
    D n f = D n g := by
  have h1 := D_mono n f g (fun u v hu hv => Nat.le_of_eq (h u v hu hv))
  have h2 := D_mono n g f (fun u v hu hv => Nat.le_of_eq (h u v hu hv).symm)
  omega

/-- A sum over a list of double sums is the double sum of the sums. -/
theorem lsum_D (l : List Nat) (f : Nat → Nat → Nat → Nat) :
    lsum l (fun i => D n (f i)) = D n (fun u v => lsum l (fun i => f i u v)) := by
  induction l with
  | nil =>
    simp only [lsum, D]
    rw [lsum_congr (List.range n) _ (fun _ => 0) (fun u _ => lsum_zero _), lsum_zero]
  | cons a l ih =>
    simp only [lsum]
    rw [ih, ← D_add]

/-! ## Part A: cut identities

  `q X` is the cut value of X, `e P Q` the weight between P and Q, and `cost lab` the cost of the
  partition in which vertex u lies in part `lab u`. All three count each edge once per ordered
  pair of endpoints, i.e. twice for symmetric weights. -/

def q (X : Nat → Bool) : Nat := D n (fun u v => ind (X u != X v) * wt u v)

def e (P Q : Nat → Bool) : Nat := D n (fun u v => ind ((P u && Q v) || (Q u && P v)) * wt u v)

def cost (lab : Nat → Nat) : Nat := D n (fun u v => ind (lab u != lab v) * wt u v)

/-- Part i of a labelled partition. -/
def part (lab : Nat → Nat) (i : Nat) : Nat → Bool := fun u => lab u == i

def sing (v : Nat) : Nat → Bool := fun u => u == v

def union (X Y : Nat → Bool) : Nat → Bool := fun u => X u || Y u

/-- Shore-sum identity (equation (1) of the paper): for every partition with parts labelled
    0, ..., k-1, the sum of the k shore cuts is twice the partition cost. -/
theorem shore_sum (k : Nat) (lab : Nat → Nat) (hk : ∀ u, u < n → lab u < k) :
    lsum (List.range k) (fun i => q n wt (part lab i)) = 2 * cost n wt lab := by
  unfold q cost part
  rw [lsum_D]
  have h2 : 2 * D n (fun u v => ind (lab u != lab v) * wt u v)
      = D n (fun u v => 2 * (ind (lab u != lab v) * wt u v)) := by
    have := D_add n (fun u v => ind (lab u != lab v) * wt u v)
      (fun u v => ind (lab u != lab v) * wt u v)
    simp only [← Nat.two_mul] at this
    omega
  rw [h2]
  apply D_congr
  intro u v hu hv
  rw [lsum_mul, count_parts (lab u) (lab v) k (hk u hu) (hk v hv), Nat.mul_assoc]

/-- Cross-query identity (equation (2)); with X = {v} it is the star identity (3). -/
theorem cross_query (X Y : Nat → Bool) (hd : ∀ u, u < n → (X u && Y u) = false) :
    q n wt X + q n wt Y = q n wt (union X Y) + 2 * e n wt X Y := by
  unfold q e union
  rw [← D_add, Nat.two_mul, ← D_add, ← D_add]
  apply D_congr
  intro u v hu hv
  have h1 := hd u hu
  have h2 := hd v hv
  revert h1 h2
  cases X u <;> cases Y u <;> cases X v <;> cases Y v <;> simp [ind] <;> omega

/-- The 3-partition ({u},{v},V∖{u,v}). -/
def labUV (u v : Nat) : Nat → Nat := fun x => if x == u then 0 else if x == v then 1 else 2

def lab3 (a b : Bool) : Nat := if a then 0 else if b then 1 else 2

theorem pt_two (A B C E : Bool) (w : Nat) (h1 : (A && B) = false) (h2 : (C && E) = false) :
    ind (lab3 A B != lab3 C E) * w + ind ((A && E) || (B && C)) * w
      = ind (A != C) * w + ind (B != E) * w := by
  revert h1 h2
  cases A <;> cases B <;> cases C <;> cases E <;> simp [ind, lab3] <;> omega

theorem beq_excl (x u v : Nat) (huv : u ≠ v) : ((x == u) && (x == v)) = false := by
  by_cases h : x = u
  · subst h; simp [huv]
  · simp [h]

/-- Two-singleton cost (equation (4)): cost(P_{u,v}) + w(u,v) = d(u) + d(v)
    (all three terms doubled). -/
theorem two_singleton (u v : Nat) (huv : u ≠ v) :
    cost n wt (labUV u v) + e n wt (sing u) (sing v) = q n wt (sing u) + q n wt (sing v) := by
  unfold cost e q sing labUV
  rw [← D_add, ← D_add]
  apply D_congr
  intro x y _ _
  have := pt_two (x == u) (x == v) (y == u) (y == v) (wt x y)
    (beq_excl x u v huv) (beq_excl y u v huv)
  simpa [lab3] using this

/-- The 3-partition ({s}, A∖{s}, V∖(A∪{s})). -/
def labS (s : Nat) (A : Nat → Bool) : Nat → Nat :=
  fun x => if x == s then 0 else if A x then 1 else 2

theorem pt_one (S1 A1 S2 A2 : Bool) (w : Nat) :
    ind (lab3 S1 A1 != lab3 S2 A2) * w
      = ind (S1 != S2) * w + ind (((!S1 && A1) && (!S2 && !A2)) || ((!S1 && !A1) && (!S2 && A2))) * w := by
  cases S1 <;> cases A1 <;> cases S2 <;> cases A2 <;> simp [ind, lab3]

/-- One-singleton cost (equation (17)): cost({s},A,B) = d(s) + e(A,B). -/
theorem one_singleton (s : Nat) (A : Nat → Bool) :
    cost n wt (labS s A)
      = q n wt (sing s) + e n wt (fun x => !(x == s) && A x) (fun x => !(x == s) && !A x) := by
  unfold cost e q sing labS
  rw [← D_add]
  apply D_congr
  intro x y _ _
  have := pt_one (x == s) (A x) (y == s) (A y) (wt x y)
  simpa [lab3] using this

/-- Each shore of a partition is crossed only by edges cut by the partition. -/
theorem shore_le_cost (lab : Nat → Nat) (i : Nat) :
    q n wt (part lab i) ≤ cost n wt lab := by
  unfold q cost part
  apply D_mono
  intro u v _ _
  apply Nat.mul_le_mul_right
  by_cases h : lab u = lab v
  · simp [ind, h]
  · simp only [ind]
    split <;> simp_all

/-- Corollary 7 (optimizer transfer), cost part: if every cut below r is preserved by J, then
    every k-partition of G-cost below r has the same J-cost. (Units are doubled throughout.) -/
theorem transfer_cost (wtG wtJ : Nat → Nat → Nat) (r k : Nat) (lab : Nat → Nat)
    (hcert : ∀ X : Nat → Bool, min r (q n wtJ X) = min r (q n wtG X))
    (hk : ∀ u, u < n → lab u < k) (hlt : cost n wtG lab < r) :
    cost n wtJ lab = cost n wtG lab := by
  have hJ := shore_sum n wtJ k lab hk
  have hG := shore_sum n wtG k lab hk
  have heq : lsum (List.range k) (fun i => q n wtJ (part lab i))
      = lsum (List.range k) (fun i => q n wtG (part lab i)) := by
    apply lsum_congr
    intro i _
    have h1 := shore_le_cost n wtG lab i
    have h2 := hcert (part lab i)
    have h3 : q n wtG (part lab i) < r := by omega
    rw [Nat.min_eq_right (Nat.le_of_lt h3)] at h2
    have h4 : q n wtJ (part lab i) < r := by
      rcases Nat.le_total r (q n wtJ (part lab i)) with h | h
      · rw [Nat.min_eq_left h] at h2; omega
      · exact Nat.lt_of_le_of_lt (Nat.le_of_eq (by rw [Nat.min_eq_right h] at h2; exact h2)) h3
    rw [Nat.min_eq_right (Nat.le_of_lt h4)] at h2
    exact h2
  omega

/-- Corollary 7 (optimizer transfer). Let `adm` be the admissible k-partitions (labels below
    k), let P minimize the G-cost and Q the J-cost over `adm`, and suppose λ_k(G) = cost_G(P) < r.
    Then cost_J(P) = cost_G(P) and cost_G(Q) = cost_G(P): every minimum k-cut of J is a minimum
    k-cut of G. -/
theorem optimizer_transfer (wtG wtJ : Nat → Nat → Nat) (r k : Nat)
    (adm : (Nat → Nat) → Prop) (hadm : ∀ lab, adm lab → ∀ u, u < n → lab u < k)
    (hcert : ∀ X : Nat → Bool, min r (q n wtJ X) = min r (q n wtG X))
    (P Q : Nat → Nat) (hP : adm P) (hQ : adm Q)
    (hPopt : ∀ lab, adm lab → cost n wtG P ≤ cost n wtG lab)
    (hQopt : ∀ lab, adm lab → cost n wtJ Q ≤ cost n wtJ lab)
    (hlt : cost n wtG P < r) :
    cost n wtJ P = cost n wtG P ∧ cost n wtG Q = cost n wtG P := by
  have h1 := transfer_cost n wtG wtJ r k P hcert (hadm P hP) hlt
  have h2 := hQopt P hP
  have hcert' : ∀ X : Nat → Bool, min r (q n wtG X) = min r (q n wtJ X) := fun X => (hcert X).symm
  have h3 := transfer_cost n wtJ wtG r k Q hcert' (hadm Q hQ) (by omega)
  have h4 := hPopt Q hQ
  constructor
  · exact h1
  · omega

end Graph

end MinKCut
