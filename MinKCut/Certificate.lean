import MinKCut.Switching
/-! # Part I: the forest-packing certificate (Lemma 6) -/

namespace MinKCut

/-! ## Part I: the forest-packing certificate (Lemma 6)

  Let F₀, ..., F_{r-1} be edge sets (weight functions) packed into G, and let G_i be what remains
  of G after removing F₀, ..., F_{i-1}. If every F_i is a *spanning* subgraph of G_i (a subgraph
  in which the endpoints of every edge of G_i are joined by a path), then J = F₀ + ... + F_{r-1}
  satisfies min{r, d_J(S)} = min{r, d_G(S)} for every S (equation (certificate)). A spanning
  forest is a spanning subgraph, so this is Lemma 6; acyclicity only bounds the size of J.
  Cuts are counted once per edge here: dq(S) = Σ_{u ∈ S, v ∉ S} w(u,v). -/

section Certificate

variable (n : Nat)

/-- Directed cut: each crossing edge counted once (for symmetric weights, the usual cut). -/
def dq (w : Nat → Nat → Nat) (S : Nat → Bool) : Nat := D n (fun u v => ind (S u && !S v) * w u v)

theorem dq_add (w1 w2 : Nat → Nat → Nat) (S : Nat → Bool) :
    dq n (fun u v => w1 u v + w2 u v) S = dq n w1 S + dq n w2 S := by
  unfold dq; rw [← D_add]; apply D_congr; intro u v _ _; rw [Nat.mul_add]

theorem dq_mono (w1 w2 : Nat → Nat → Nat) (S : Nat → Bool) (h : ∀ u v, w1 u v ≤ w2 u v) :
    dq n w1 S ≤ dq n w2 S := by
  unfold dq; apply D_mono; intro u v _ _; exact Nat.mul_le_mul_left _ (h u v)

/-- The packed sum F₀ + ... + F_{i-1}. -/
def packed (F : Nat → Nat → Nat → Nat) (i : Nat) (u v : Nat) : Nat :=
  lsum (List.range i) (fun j => F j u v)

/-- The residual graph G_i = G - (F₀ + ... + F_{i-1}). -/
def residual (G : Nat → Nat → Nat) (F : Nat → Nat → Nat → Nat) (i : Nat) (u v : Nat) : Nat :=
  G u v - packed F i u v

theorem dq_packed (F : Nat → Nat → Nat → Nat) (S : Nat → Bool) : ∀ i,
    dq n (packed F i) S = lsum (List.range i) (fun j => dq n (F j) S) := by
  intro i
  induction i with
  | zero =>
    unfold dq packed
    simp only [List.range_zero, lsum, Nat.mul_zero]
    exact D_zero n
  | succ i ih =>
    have e : packed F (i + 1) = fun u v => packed F i u v + F i u v := by
      funext u v; unfold packed; rw [List.range_succ, lsum_append]; simp [lsum]
    rw [e, dq_add, ih, List.range_succ, lsum_append]
    simp [lsum]

theorem packed_mono (F : Nat → Nat → Nat → Nat) (i j : Nat) (hij : i ≤ j) (u v : Nat) :
    packed F i u v ≤ packed F j u v := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  unfold packed
  rw [lsum_range_add]
  omega

/-- The certificate property from the crossing property of each packed subgraph. -/
theorem certificate (G : Nat → Nat → Nat) (F : Nat → Nat → Nat → Nat) (r : Nat)
    (hfit : ∀ u v, packed F r u v ≤ G u v)
    (hcross : ∀ i, i < r → ∀ S : Nat → Bool, 1 ≤ dq n (residual G F i) S → 1 ≤ dq n (F i) S)
    (S : Nat → Bool) :
    min r (dq n (packed F r) S) = min r (dq n G S) := by
  -- G = J + G_r
  have hsplit : dq n G S = dq n (packed F r) S + dq n (residual G F r) S := by
    rw [← dq_add]
    unfold dq; apply D_congr; intro u v _ _
    unfold residual
    dsimp only
    rw [Nat.add_sub_cancel' (hfit u v)]
  by_cases h0 : dq n (residual G F r) S = 0
  · rw [hsplit, h0, Nat.add_zero]
  · -- every residual graph G_i (i < r) still has a crossing edge, so every F_i crosses S
    have hall : ∀ i, i < r → 1 ≤ dq n (F i) S := by
      intro i hi
      apply hcross i hi S
      have hm : dq n (residual G F r) S ≤ dq n (residual G F i) S := by
        apply dq_mono; intro u v; unfold residual
        have := packed_mono F i r (by omega) u v
        omega
      omega
    have hJ : r ≤ dq n (packed F r) S := by
      rw [dq_packed]
      have : lsum (List.range r) (fun _ => 1) ≤ lsum (List.range r) (fun j => dq n (F j) S) :=
        lsum_mono _ _ _ (fun j hj => hall j (List.mem_range.mp hj))
      rw [lsum_ones] at this
      exact this
    rw [Nat.min_eq_left hJ, Nat.min_eq_left (by omega)]

/-- Paths in F. -/
inductive Reach (F : Nat → Nat → Nat) : Nat → Nat → Prop
  | refl (u : Nat) : Reach F u u
  | step {u v w : Nat} : Reach F u v → 1 ≤ F v w → Reach F u w

/-- A path from S to its complement uses an edge leaving S. -/
theorem reach_cross (F : Nat → Nat → Nat) (S : Nat → Bool) {u v : Nat} (h : Reach F u v) :
    S u = true → S v = false → ∃ a b, S a = true ∧ S b = false ∧ 1 ≤ F a b := by
  induction h with
  | refl => intro h1 h2; rw [h1] at h2; exact absurd h2 (by simp)
  | @step v w _ hvw ih =>
    intro h1 h2
    cases hv : S v
    · exact ih h1 hv
    · exact ⟨v, w, hv, h2, hvw⟩

/-- F is a spanning subgraph of G' on the vertices 0, ..., n-1: F ⊆ G', F lives on the
    vertices, and the endpoints of every edge of G' are joined by a path in F. A spanning forest
    of G' (as computed in the proof of Lemma 6) is such a subgraph. -/
def Spanning (F G' : Nat → Nat → Nat) : Prop :=
  (∀ u v, F u v ≤ G' u v) ∧ (∀ a b, 1 ≤ F a b → a < n ∧ b < n) ∧
  (∀ u v, u < n → v < n → 1 ≤ G' u v → Reach F u v)

theorem D_ge_term (f : Nat → Nat → Nat) (a b : Nat) (ha : a < n) (hb : b < n) : f a b ≤ D n f := by
  unfold D
  have h1 := lsum_ge_term (fun v => f a v) b n hb
  have h2 := lsum_ge_term (fun u => lsum (List.range n) (fun v => f u v)) a n ha
  dsimp only at h1 h2
  omega

/-- A spanning subgraph crosses every cut that G' crosses. -/
theorem spanning_cross (F G' : Nat → Nat → Nat) (hF : Spanning n F G') (S : Nat → Bool)
    (h : 1 ≤ dq n G' S) : 1 ≤ dq n F S := by
  obtain ⟨_, hsupp, hreach⟩ := hF
  unfold dq at h
  obtain ⟨x, y, hx, hy, hxy⟩ := D_pos n _ h
  have hSx : S x = true := by cases h' : S x <;> simp_all [ind]
  have hSy : S y = false := by cases h' : S y <;> simp_all [ind]
  have hG : 1 ≤ G' x y := by simp [hSx, hSy, ind] at hxy; exact hxy
  obtain ⟨a, b, ha, hb, hab⟩ := reach_cross F S (hreach x y hx hy hG) hSx hSy
  obtain ⟨han, hbn⟩ := hsupp a b hab
  have := D_ge_term n (fun u v => ind (S u && !S v) * F u v) a b han hbn
  dsimp only at this
  have hterm : 1 ≤ ind (S a && !S b) * F a b := by simp [ha, hb, ind]; omega
  unfold dq
  omega

/-- Lemma 6 (low-cut certificate): if F_i is a spanning subgraph (for instance a spanning
    forest) of the residual graph G_i for every i < r, then J = F₀ + ... + F_{r-1} satisfies
    min{r, d_J(S)} = min{r, d_G(S)} for every vertex set S. -/
theorem forest_certificate (G : Nat → Nat → Nat) (F : Nat → Nat → Nat → Nat) (r : Nat)
    (hfit : ∀ u v, packed F r u v ≤ G u v)
    (hspan : ∀ i, i < r → Spanning n (F i) (residual G F i)) (S : Nat → Bool) :
    min r (dq n (packed F r) S) = min r (dq n G S) :=
  certificate n G F r hfit (fun i hi S h => spanning_cross n (F i) _ (hspan i hi) S h) S

/-- For symmetric weights the doubled cut q of Part A is twice dq. -/
theorem q_eq_two_dq (w : Nat → Nat → Nat) (hsym : ∀ u v, w u v = w v u) (S : Nat → Bool) :
    q n w S = 2 * dq n w S := by
  have h1 : q n w S = dq n w S + dq n w (fun u => !S u) := by
    unfold q dq; rw [← D_add]; apply D_congr; intro u v _ _
    dsimp only
    cases h1 : S u <;> cases h2 : S v <;> simp [ind]
  have h2 : dq n w (fun u => !S u) = dq n w S := by
    unfold dq D
    rw [lsum_swap]
    apply lsum_congr; intro u _; apply lsum_congr; intro v _
    rw [hsym v u]
    cases h1 : S u <;> cases h2 : S v <;> simp [ind, h1, h2]
  omega

/-- Lemma 6 + Corollary 7: with symmetric packed subgraphs, if λ_k(G) < r then every minimum
    k-cut of J is a minimum k-cut of G (stated in the doubled units of Part A). -/
theorem certificate_transfer (G : Nat → Nat → Nat) (F : Nat → Nat → Nat → Nat) (r k : Nat)
    (hsymG : ∀ u v, G u v = G v u) (hsymF : ∀ i u v, F i u v = F i v u)
    (hfit : ∀ u v, packed F r u v ≤ G u v)
    (hspan : ∀ i, i < r → Spanning n (F i) (residual G F i))
    (adm : (Nat → Nat) → Prop) (hadm : ∀ lab, adm lab → ∀ u, u < n → lab u < k)
    (P Q : Nat → Nat) (hP : adm P) (hQ : adm Q)
    (hPopt : ∀ lab, adm lab → cost n G P ≤ cost n G lab)
    (hQopt : ∀ lab, adm lab → cost n (packed F r) Q ≤ cost n (packed F r) lab)
    (hlt : cost n G P < 2 * r) :
    cost n (packed F r) P = cost n G P ∧ cost n G Q = cost n G P := by
  have hsymJ : ∀ u v, packed F r u v = packed F r v u := by
    intro u v; unfold packed; apply lsum_congr; intro j _; exact hsymF j u v
  have hcert : ∀ X : Nat → Bool, min (2 * r) (q n (packed F r) X) = min (2 * r) (q n G X) := by
    intro X
    have h := forest_certificate n G F r hfit hspan X
    rw [q_eq_two_dq n _ hsymJ, q_eq_two_dq n _ hsymG]
    omega
  exact optimizer_transfer n G (packed F r) (2 * r) k adm hadm hcert P Q hP hQ hPopt hQopt hlt

/-! ### Spanning forests exist and have at most n - 1 edges

  The greedy (Kruskal-style) construction: scan all pairs (u,v); keep a component label c
  (a union-find map with c(c x) = c x) and add the edge uv to F whenever G'(u,v) ≥ 1 and u, v
  carry different labels, merging the two labels. Each added edge reduces the number of roots
  {x : c x = x} by one, so at most n - 1 edges are added; at the end the endpoints of every
  edge of G' carry the same label, and equal labels are joined by paths in F. -/

theorem reach_mono (F F' : Nat → Nat → Nat) (hle : ∀ a b, F a b ≤ F' a b) {x y : Nat}
    (h : Reach F x y) : Reach F' x y := by
  induction h with
  | refl => exact Reach.refl _
  | step _ hvw ih => exact Reach.step ih (Nat.le_trans hvw (hle _ _))

theorem reach_trans (F : Nat → Nat → Nat) {x y z : Nat} (h1 : Reach F x y) (h2 : Reach F y z) :
    Reach F x z := by
  induction h2 with
  | refl => exact h1
  | step _ hvw ih => exact Reach.step ih hvw

theorem reach_symm (F : Nat → Nat → Nat) (hs : ∀ a b, F a b = F b a) {x y : Nat}
    (h : Reach F x y) : Reach F y x := by
  induction h with
  | refl => exact Reach.refl _
  | @step v w _ hvw ih =>
    have e : Reach F w v := Reach.step (Reach.refl w) (by rw [hs]; exact hvw)
    exact reach_trans F e ih

/-- Relabel the class rv as ru. -/
def relabel (c : Nat → Nat) (rv ru : Nat) : Nat → Nat := fun x => if c x = rv then ru else c x

/-- One greedy step on the pair (u,v). State: labels, forest, number of edges. -/
def gstep (G' : Nat → Nat → Nat) (st : (Nat → Nat) × (Nat → Nat → Nat) × Nat) (p : Nat × Nat) :
    (Nat → Nat) × (Nat → Nat → Nat) × Nat :=
  if 1 ≤ G' p.1 p.2 ∧ st.1 p.1 ≠ st.1 p.2 then
    (relabel st.1 (st.1 p.2) (st.1 p.1), fun a b => st.2.1 a b + bridge p.1 p.2 a b, st.2.2 + 1)
  else st

def roots (c : Nat → Nat) : Nat := cnt n (fun x => decide (c x = x))

/-- The invariant of the greedy construction. -/
def GInv (G' : Nat → Nat → Nat) (st : (Nat → Nat) × (Nat → Nat → Nat) × Nat) : Prop :=
  (∀ x, x < n → st.1 x < n ∧ st.1 (st.1 x) = st.1 x) ∧
  (∀ x y, x < n → y < n → st.1 x = st.1 y → Reach st.2.1 x y) ∧
  (∀ a b, 1 ≤ st.2.1 a b → a < n ∧ b < n ∧ st.1 a = st.1 b) ∧
  (∀ a b, st.2.1 a b ≤ G' a b) ∧
  (∀ a b, st.2.1 a b = st.2.1 b a) ∧
  st.2.2 + roots n st.1 = n ∧
  D n st.2.1 = 2 * st.2.2

theorem bridge_symm (u v a b : Nat) : bridge u v a b = bridge u v b a := by
  unfold bridge
  cases h1 : (a == u) <;> cases h2 : (b == v) <;> cases h3 : (a == v) <;> cases h4 : (b == u) <;> simp

theorem pt_bridge (a b u v : Nat) (huv : u ≠ v) :
    ind ((if a = u then 0 else 1) != (if b = u then 0 else 1)) * bridge u v a b = bridge u v a b := by
  unfold bridge
  simp only [ind, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  repeat' split
  all_goals omega

theorem D_bridge (u v : Nat) (hu : u < n) (hv : v < n) (huv : u ≠ v) : D n (bridge u v) = 2 := by
  have h := cost_bridge n (fun x => if x = u then 0 else 1) u v hu hv huv
  have e : cost n (bridge u v) (fun x => if x = u then 0 else 1) = D n (bridge u v) := by
    unfold cost; apply D_congr; intro a b _ _
    exact pt_bridge a b u v huv
  have e2 : ind ((if u = u then 0 else 1) != (if v = u then 0 else 1)) = 1 := by
    have : v ≠ u := fun z => huv z.symm
    simp [this, ind]
  rw [e] at h; rw [h, e2]

theorem roots_relabel (c : Nat → Nat) (ru rv : Nat) (_hru : ru < n) (hrv : rv < n) (hne : ru ≠ rv)
    (hroot_u : c ru = ru) (hroot_v : c rv = rv) :
    roots n (relabel c rv ru) + 1 = roots n c := by
  unfold roots cnt
  have hp := pick (fun _ => 1) rv n hrv
  dsimp only at hp
  rw [← hp, ← lsum_add]
  apply lsum_congr
  intro x _
  unfold relabel
  by_cases hx : x = rv
  · subst hx; simp [hroot_v, hne, ind]
  · by_cases hcx : c x = rv
    · have : ru ≠ x := by intro e; subst e; exact hne (hroot_u ▸ hcx)
      have h2 : x ≠ ru := fun z => this z.symm
      have h3 : c x ≠ x := by rw [hcx]; exact fun z => hx z.symm
      have hx' : rv ≠ x := fun z => hx z.symm
      simp [hcx, h2, h3, hx, hx', this, ind]
    · simp [hcx, hx, ind]

theorem gstep_inv (G' : Nat → Nat → Nat) (hsym : ∀ a b, G' a b = G' b a)
    (st : (Nat → Nat) × (Nat → Nat → Nat) × Nat) (p : Nat × Nat) (hp1 : p.1 < n) (hp2 : p.2 < n)
    (hI : GInv n G' st) : GInv n G' (gstep G' st p) := by
  obtain ⟨c, F, m⟩ := st
  obtain ⟨u, v⟩ := p
  simp only at hp1 hp2
  obtain ⟨I0, I1, I2, I3, I4, I5, I6⟩ := hI
  dsimp only at I0 I1 I2 I3 I4 I5 I6
  unfold gstep
  simp only
  by_cases hc : 1 ≤ G' u v ∧ c u ≠ c v
  · rw [if_pos hc]
    obtain ⟨hG, hne⟩ := hc
    have huv : u ≠ v := by intro e; subst e; exact hne rfl
    have ⟨cu_lt, cu_root⟩ := I0 u hp1
    have ⟨cv_lt, cv_root⟩ := I0 v hp2
    -- the new pair is not yet in F
    have F0 : F u v = 0 := by
      cases h : F u v
      · rfl
      · have := I2 u v (by omega); exact absurd this.2.2 hne
    have F0' : F v u = 0 := by rw [I4]; exact F0
    unfold GInv
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨h1, h2⟩ := I0 x hx
      unfold relabel
      by_cases hcx : c x = c v
      · simp only [hcx, ite_true]
        refine ⟨cu_lt, ?_⟩
        rw [cu_root]; simp [hne]
      · simp only [hcx, ite_false]
        refine ⟨h1, ?_⟩
        rw [h2]; simp [hcx]
    · intro x y hx hy hxy
      have hle : ∀ a b, F a b ≤ F a b + bridge u v a b := fun a b => Nat.le_add_right _ _
      have hsF : ∀ a b, F a b + bridge u v a b = F b a + bridge u v b a := by
        intro a b; rw [I4, bridge_symm]
      have euv : Reach (fun a b => F a b + bridge u v a b) v u := by
        have : 1 ≤ F v u + bridge u v v u := by simp [bridge, ind]
        exact Reach.step (Reach.refl v) this
      unfold relabel at hxy
      by_cases hx' : c x = c v <;> by_cases hy' : c y = c v <;> simp only [hx', hy', ite_true, ite_false] at hxy
      · exact reach_mono _ _ hle (I1 x y hx hy (by rw [hx', hy']))
      · -- x ~ v, y ~ u
        have r1 := reach_mono _ _ hle (I1 x v hx hp2 hx')
        have r2 := reach_mono _ _ hle (I1 u y hp1 hy (by rw [hxy]))
        exact reach_trans _ (reach_trans _ r1 euv) r2
      · have r1 := reach_mono _ _ hle (I1 x u hx hp1 hxy)
        have r2 := reach_mono _ _ hle (I1 v y hp2 hy hy'.symm)
        exact reach_trans _ (reach_trans _ r1 (reach_symm _ hsF euv)) r2
      · exact reach_mono _ _ hle (I1 x y hx hy hxy)
    · intro a b hab
      unfold relabel
      by_cases hb : bridge u v a b = 0
      · rw [hb, Nat.add_zero] at hab
        obtain ⟨ha, hb', he⟩ := I2 a b hab
        refine ⟨ha, hb', ?_⟩
        rw [he]
      · have : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
          unfold bridge at hb
          by_cases h1 : a = u <;> by_cases h2 : b = v <;> by_cases h3 : a = v <;> by_cases h4 : b = u <;>
            simp_all [ind]
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨hp1, hp2, ?_⟩
          simp [hne]
        · refine ⟨hp2, hp1, ?_⟩
          simp [hne]
    · intro a b
      by_cases hb : bridge u v a b = 0
      · rw [hb, Nat.add_zero]; exact I3 a b
      · have : (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
          unfold bridge at hb
          by_cases h1 : a = u <;> by_cases h2 : b = v <;> by_cases h3 : a = v <;> by_cases h4 : b = u <;>
            simp_all [ind]
        have hb1 : bridge u v a b ≤ 1 := by unfold bridge ind; split <;> omega
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [F0]; omega
        · rw [F0', hsym]; omega
    · intro a b; rw [I4, bridge_symm]
    · have := roots_relabel n c (c u) (c v) cu_lt cv_lt hne cu_root cv_root
      omega
    · have hD := D_add n F (bridge u v)
      rw [D_bridge n u v hp1 hp2 huv] at hD
      show D n (fun a b => F a b + bridge u v a b) = 2 * (m + 1)
      omega
  · rw [if_neg hc]
    exact ⟨I0, I1, I2, I3, I4, I5, I6⟩

/-- After a greedy step, labels that were equal stay equal. -/
theorem gstep_keep (G' : Nat → Nat → Nat) (st : (Nat → Nat) × (Nat → Nat → Nat) × Nat)
    (p : Nat × Nat) (x y : Nat) (h : st.1 x = st.1 y) : (gstep G' st p).1 x = (gstep G' st p).1 y := by
  unfold gstep
  split
  · simp only [relabel, h]
  · exact h

/-- After a greedy step on (u,v) with G'(u,v) ≥ 1, the labels of u and v agree. -/
theorem gstep_joins (G' : Nat → Nat → Nat) (st : (Nat → Nat) × (Nat → Nat → Nat) × Nat)
    (p : Nat × Nat) (hG : 1 ≤ G' p.1 p.2) : (gstep G' st p).1 p.1 = (gstep G' st p).1 p.2 := by
  unfold gstep
  by_cases hc : st.1 p.1 = st.1 p.2
  · have : ¬(1 ≤ G' p.1 p.2 ∧ st.1 p.1 ≠ st.1 p.2) := fun h => h.2 hc
    rw [if_neg this]; exact hc
  · rw [if_pos ⟨hG, hc⟩]
    simp [relabel]

def gfold (G' : Nat → Nat → Nat) (l : List (Nat × Nat)) (st : (Nat → Nat) × (Nat → Nat → Nat) × Nat) :
    (Nat → Nat) × (Nat → Nat → Nat) × Nat := l.foldl (gstep G') st

theorem gfold_inv (G' : Nat → Nat → Nat) (hsym : ∀ a b, G' a b = G' b a) :
    ∀ (l : List (Nat × Nat)) st, (∀ p, p ∈ l → p.1 < n ∧ p.2 < n) → GInv n G' st →
      GInv n G' (gfold G' l st) := by
  intro l
  induction l with
  | nil => intro st _ h; exact h
  | cons p l ih =>
    intro st hl h
    unfold gfold
    simp only [List.foldl_cons]
    have hp := hl p (by simp)
    exact ih _ (fun q hq => hl q (by simp [hq])) (gstep_inv n G' hsym st p hp.1 hp.2 h)

theorem gfold_keep (G' : Nat → Nat → Nat) :
    ∀ (l : List (Nat × Nat)) st x y, st.1 x = st.1 y → (gfold G' l st).1 x = (gfold G' l st).1 y := by
  intro l
  induction l with
  | nil => intro st x y h; exact h
  | cons p l ih =>
    intro st x y h
    unfold gfold; simp only [List.foldl_cons]
    exact ih _ x y (gstep_keep G' st p x y h)

theorem gfold_joins (G' : Nat → Nat → Nat) :
    ∀ (l : List (Nat × Nat)) st p, p ∈ l → 1 ≤ G' p.1 p.2 →
      (gfold G' l st).1 p.1 = (gfold G' l st).1 p.2 := by
  intro l
  induction l with
  | nil => intro st p hp; simp at hp
  | cons q l ih =>
    intro st p hp hG
    unfold gfold; simp only [List.foldl_cons]
    rcases List.mem_cons.mp hp with h | h
    · subst h
      exact gfold_keep G' l _ p.1 p.2 (gstep_joins G' st p hG)
    · exact ih _ p h hG

def allPairs : List (Nat × Nat) := (List.range n).flatMap (fun u => (List.range n).map (fun v => (u, v)))

theorem mem_allPairs (u v : Nat) : (u, v) ∈ allPairs n ↔ u < n ∧ v < n := by
  unfold allPairs; simp

/-- Every graph on 0..n-1 (symmetric weights) has a spanning forest: a symmetric spanning
    subgraph with at most n - 1 edges (D counts each edge twice). -/
theorem spanning_forest_exists (G' : Nat → Nat → Nat) (hsym : ∀ a b, G' a b = G' b a) (hn : 1 ≤ n) :
    ∃ F : Nat → Nat → Nat, Spanning n F G' ∧ (∀ a b, F a b = F b a) ∧ D n F ≤ 2 * (n - 1) := by
  let st0 : (Nat → Nat) × (Nat → Nat → Nat) × Nat := (fun x => x, fun _ _ => 0, 0)
  have hroots0 : roots n (fun x : Nat => x) = n := by
    unfold roots cnt
    rw [lsum_congr _ _ (fun _ => 1) (fun x _ => by simp [ind])]
    exact lsum_ones n
  have h0 : GInv n G' st0 := by
    refine ⟨fun x hx => ⟨hx, rfl⟩, fun x y _ _ h => by simp only [st0] at h; subst h; exact Reach.refl _,
      fun a b h => by simp [st0] at h, fun a b => Nat.zero_le _, fun _ _ => rfl, ?_, ?_⟩
    · show 0 + roots n (fun x : Nat => x) = n
      omega
    · exact D_zero n
  have hl : ∀ p, p ∈ allPairs n → p.1 < n ∧ p.2 < n := by
    intro p hp; exact (mem_allPairs n p.1 p.2).mp hp
  have hI := gfold_inv n G' hsym (allPairs n) st0 hl h0
  obtain ⟨I0, I1, I2, I3, I4, I5, I6⟩ := hI
  refine ⟨(gfold G' (allPairs n) st0).2.1, ⟨I3, fun a b h => ⟨(I2 a b h).1, (I2 a b h).2.1⟩, ?_⟩, I4, ?_⟩
  · intro u v hu hv hG
    apply I1 u v hu hv
    exact gfold_joins G' (allPairs n) st0 (u, v) ((mem_allPairs n u v).mpr ⟨hu, hv⟩) hG
  · -- at least one root survives
    have hr : 1 ≤ roots n (gfold G' (allPairs n) st0).1 := by
      let c := (gfold G' (allPairs n) st0).1
      obtain ⟨h1, h2⟩ := I0 0 (by omega)
      have := lsum_ge_term (fun x => ind (decide (c x = x))) (c 0) n h1
      have e : ind (decide (c (c 0) = c 0)) = 1 := by unfold ind; rw [decide_eq_true h2]; rfl
      dsimp only at this
      unfold roots cnt
      rw [e] at this
      exact this
    omega

theorem packed_congr (F F' : Nat → Nat → Nat → Nat) (r : Nat) (h : ∀ i, i < r → F i = F' i) :
    ∀ i, i ≤ r → ∀ u v, packed F i u v = packed F' i u v := by
  intro i hi u v
  unfold packed
  apply lsum_congr
  intro j hj
  rw [h j (by have := List.mem_range.mp hj; omega)]

/-- Lemma 6 (low-cut certificate), complete: for every graph G on 0..n-1 with symmetric weights
    and every r there are r edge-disjoint spanning forests F₀, ..., F_{r-1}, each a spanning
    forest of what remains of G after removing the previous ones and each with at most n - 1
    edges, whose union J satisfies min{r, d_J(S)} = min{r, d_G(S)} for every vertex set S. -/
theorem lemma6 (G : Nat → Nat → Nat) (hsym : ∀ a b, G a b = G b a) (hn : 1 ≤ n) :
    ∀ r, ∃ F : Nat → Nat → Nat → Nat,
      (∀ u v, packed F r u v ≤ G u v) ∧
      (∀ i, i < r → Spanning n (F i) (residual G F i) ∧ D n (F i) ≤ 2 * (n - 1)) ∧
      (∀ i u v, F i u v = F i v u) ∧
      (∀ S : Nat → Bool, min r (dq n (packed F r) S) = min r (dq n G S)) := by
  intro r
  have main : ∀ r, ∃ F : Nat → Nat → Nat → Nat,
      (∀ u v, packed F r u v ≤ G u v) ∧
      (∀ i, i < r → Spanning n (F i) (residual G F i) ∧ D n (F i) ≤ 2 * (n - 1)) ∧
      (∀ i u v, F i u v = F i v u) := by
    intro r
    induction r with
    | zero =>
      refine ⟨fun _ _ _ => 0, ?_, fun i hi => absurd hi (by omega), fun _ _ _ => rfl⟩
      intro u v; unfold packed; simp [lsum]
    | succ r ih =>
      obtain ⟨F, hfit, hspan, hsF⟩ := ih
      have hsymR : ∀ a b, residual G F r a b = residual G F r b a := by
        intro a b; unfold residual packed
        rw [hsym a b, lsum_congr _ _ (fun j => F j b a) (fun j _ => hsF j a b)]
      obtain ⟨F', hF', hsF', hD'⟩ := spanning_forest_exists n (residual G F r) hsymR hn
      let F'' : Nat → Nat → Nat → Nat := fun i => if i < r then F i else F'
      have hagree : ∀ i, i < r → F'' i = F i := by intro i hi; simp [F'', hi]
      have hpk : ∀ i, i ≤ r → ∀ u v, packed F'' i u v = packed F i u v :=
        packed_congr F'' F r hagree
      have hres : ∀ i, i ≤ r → residual G F'' i = residual G F i := by
        intro i hi; funext u v; unfold residual; rw [hpk i hi u v]
      have hFr : F'' r = F' := by simp [F'']
      refine ⟨F'', ?_, ?_, ?_⟩
      · intro u v
        have e : packed F'' (r + 1) u v = packed F'' r u v + F'' r u v := by
          unfold packed; rw [List.range_succ, lsum_append]; simp [lsum]
        rw [e, hpk r (Nat.le_refl r), hFr]
        have := hF'.1 u v
        unfold residual at this
        have := hfit u v
        omega
      · intro i hi
        by_cases hir : i < r
        · rw [hagree i hir, hres i (by omega)]; exact hspan i hir
        · have : i = r := by omega
          subst this
          rw [hFr, hres i (Nat.le_refl i)]
          exact ⟨hF', hD'⟩
      · intro i u v
        by_cases hir : i < r
        · rw [hagree i hir]; exact hsF i u v
        · simp only [F'', hir, ite_false]; exact hsF' u v
  obtain ⟨F, hfit, hspan, hsF⟩ := main r
  exact ⟨F, hfit, hspan, hsF, forest_certificate n G F r hfit (fun i hi => (hspan i hi).1)⟩

end Certificate


end MinKCut
