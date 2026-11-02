import MinKCut.Queries
/-! # Part G: the triangle structure of Γ_t (Lemma 24) -/

namespace MinKCut

/-! ## Part G: the triangle structure of Γ_t (Lemma 24)

  Vertices a_i, b_j, c_i; public matching a_i c_i; Alice's edges a_i b_j (x i j = true);
  Bob's edges b_j c_i (y i j = true). -/

inductive Gv where
  | a (i : Nat)
  | b (j : Nat)
  | c (i : Nat)

def gadj (x y : Nat → Nat → Bool) : Gv → Gv → Bool
  | .a i, .c i' => i == i'
  | .c i', .a i => i == i'
  | .a i, .b j => x i j
  | .b j, .a i => x i j
  | .b j, .c i => y i j
  | .c i, .b j => y i j
  | _, _ => false

/-- Γ_t has a triangle exactly when the disjointness inputs intersect. -/
theorem gamma_triangle (x y : Nat → Nat → Bool) :
    (∃ u v w, gadj x y u v = true ∧ gadj x y v w = true ∧ gadj x y u w = true) ↔
      ∃ i j, x i j = true ∧ y i j = true := by
  constructor
  · rintro ⟨u, v, w, h1, h2, h3⟩
    cases u <;> cases v <;> cases w <;> simp [gadj] at h1 h2 h3
    all_goals first
      | (subst h3; exact ⟨_, _, h1, h2⟩)
      | (subst h3; exact ⟨_, _, h2, h1⟩)
      | (subst h2; exact ⟨_, _, h1, h3⟩)
      | (subst h2; exact ⟨_, _, h3, h1⟩)
      | (subst h1; exact ⟨_, _, h2, h3⟩)
      | (subst h1; exact ⟨_, _, h3, h2⟩)
  · rintro ⟨i, j, hx, hy⟩
    exact ⟨.a i, .b j, .c i, by simp [gadj, hx], by simp [gadj, hy], by simp [gadj]⟩

/-- Γ_t has no K₄, so its clique number is at most three (used in Lemma 27). -/
theorem gamma_no_k4 (x y : Nat → Nat → Bool) (u v w z : Gv)
    (h1 : gadj x y u v = true) (h2 : gadj x y u w = true) (h3 : gadj x y u z = true)
    (h4 : gadj x y v w = true) (h5 : gadj x y v z = true) (h6 : gadj x y w z = true) : False := by
  cases u <;> cases v <;> cases w <;> cases z <;> simp [gadj] at h1 h2 h3 h4 h5 h6


end MinKCut
