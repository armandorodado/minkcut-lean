import MinKCut.Basic
import MinKCut.Arith
import MinKCut.Cover
import MinKCut.Switching
import MinKCut.Certificate
import MinKCut.Queries
import MinKCut.Gamma
import MinKCut.Weighted
import MinKCut.Simulation
import MinKCut.Disjointness
import MinKCut.LowerBounds
import MinKCut.Truncation
import MinKCut.Bridge

/-
  Formal proofs for "Query Complexity of Exact Minimum k-Cut":
  the combinatorial and graph-theoretic cores of the proofs.

  Plain Lean 4 core (tested with Lean 4.15.0), no Mathlib, no `sorry`, no `native_decide`.
  Only Lean's standard axioms (propext, Classical.choice, Quot.sound) are used.
  Build with `lake build` (about two minutes; thirteen modules under MinKCut/).

  The theorems of the paper are statements about query algorithms (randomized, communication
  and quantum query complexity). Those models are not available in plain Lean, so this file
  formalizes the deterministic mathematics that the proofs rest on. Graphs have vertices
  0, ..., n-1 and natural-number edge weights `wt`; a *simple* graph is one with `wt` symmetric,
  zero on the diagonal and at most 1. Cut values and costs count every edge once per ordered
  pair of endpoints (i.e. twice), so no halving is needed.

  Part A  Cut identities (Lemma 4), for arbitrary weights: `shore_sum` (every k-partition),
          `cross_query` (contains the star identity), `two_singleton`, `one_singleton`;
          optimizer transfer (Corollary 7): `transfer_cost`, `optimizer_transfer`.
  Part B  The potential argument bounding the number of selected partitions (Lemma 13):
          `selection_bound`, `selection_count`.
  Part C  Exchange arithmetic and the sparsifier constant (Lemmas 11, 14, 15, Theorem 18).
  Part D  Arithmetic of Li's gadget (Lemma 25): `convexity`, `li_identity`, `li_lower`,
          `li_equality`.
  Part E  Complete graphs and parameter arithmetic (Proposition 29, Theorem 20, Lemma 27,
          Corollary 28).
  Part F  Graph-level proofs:
          * `move`: moving one vertex changes the cost by 2(e(u,P_i) - e(u,P_j));
          * Lemma 14 (no-singleton cover) `cover_no_singleton`, Lemma 15 (one-singleton cover)
            `cover_one_singleton`, Theorem 18 (≤ 2 singleton parts, every fixed k)
            `cover_general_k`: a non-exceptional vertex of degree ≥ D in a near-optimal
            candidate meets its own part of its final atom in at least αD vertices;
            `mask_le_sum_cost` (|F| ≤ Σ cost of selected partitions) and `exceptional_volume`;
          * Lemma 12: `q_sing`, `e_sing`, `two_singleton_value`, `two_singleton_opt`;
          * λ₃(K_m) = 2m - 3: `kn_cut`, `kn_lambda3`;
          * strict monotonicity λ_{j+1} ≥ λ_j + 1 on connected graphs (Corollary 28):
            `merge_step`, `strict_mono`;
          * Lemma 25 (Li's gadget) at graph level: the cost identity `li_cost_identity`, the
            lower bound `li_gadget_lower`, the equality case `li_gadget_equality` (cost = T forces
            the base vertices outside part 0 to be a clique of size ≥ k-1), attainment
            `li_gadget_attain`, and `clique_split` (splitting the clique W costs ≥ |W| - 1).
          * Theorem 20, from the minimum-cut facts of H_x and J = K_{2k}: (Hx-three-parts)
            `three_parts_unique`, and (bridge-min3) `bridge_lower`, `bridge_upper_H`,
            `bridge_upper_J` (with `cost_bridge`).
  Part H  The switching graphs H_x of Theorem 20, for every t ≥ 1 and every x with 4|x| ≤ t:
          H_x is simple (`wx_simple`) and (2t-1)-regular (`Hx_regular`); q(A) = 2|x|
          (`q_halfA`); every other proper shore except B costs at least 2|x| + 1 (`Hx_cuts`),
          so λ₂(H_x) = 2|x| is attained exactly by A and B (`Hx_mincut`); and every 3-partition
          costs at least λ₂ + 2 (`Hx_three_parts`), equation (Hx-three-parts).
  Part G  Lemma 24: `gamma_triangle` (Γ_t has a triangle iff the disjointness inputs intersect)
          and `gamma_no_k4` (Γ_t has clique number at most 3).

  Part I  The forest-packing certificate (Lemma 6): `certificate` (from the crossing property),
          `spanning_cross` (spanning subgraphs cross every cut the graph crosses),
          `spanning_forest_exists` (a greedy union-find construction gives a spanning forest
          with at most n - 1 edges), `lemma6` (r packed spanning forests satisfy
          min{r, d_J(S)} = min{r, d_G(S)} for all S), and `certificate_transfer`
          (Lemma 6 + Corollary 7).

  Part J  Query costs. A deterministic cut-query algorithm is a decision tree `Alg`; `Alg.run`
          is its output and `Alg.cost` the number of queries, against an arbitrary oracle (so
          the bounds are worst case). Verified, for every simple graph:
          * `lemma8`: output-sensitive pair recovery returns E ∩ Q exactly with at most
            Σ_v (1 + 2(2 m_v (⌈log₂ n⌉ + 1) + 1)) = O(n + M log n) queries
            (`countNb`, `star_identity`, `recov_spec`, `recov_graph`);
          * `lemma12`: Lemma 12 in full: once the degrees are known, `twoSing` returns a
            least-cost two-singleton partition with at most 7(⌈log₂ n⌉ + 1) + 1 queries
            (`findNb_graph` for d₁ < D; `cntIn`, `findIn_spec` for the edge search inside B
            when d₁ = D);
          * `forest_by_queries`: a spanning forest with at most n edges from at most
            n(6 + 5⌈log₂ n⌉) cut queries (Prim-style growth with binary searches);
          * `adjust_spec`, `residual_oracle`: a query to a residual graph is simulated by one
            query to G;
          * `lemma6_queries`: Lemma 6 with its cost: r residual spanning forests from at most
            r·n(6 + 5⌈log₂ n⌉) cut queries, and their union is a certificate.

  Part K  Proposition 29 (weighted deterministic lower bound), in full. `homogB`: a homogeneous
          integer linear system with fewer equations than free unknowns has a nonzero integer
          solution, with entries bounded by a function of the size of the system (Gaussian
          elimination). `trace`, `trace_agree`: an oracle that agrees on every query of the
          transcript yields the same run (determinism and adaptivity). `pair_sum`,
          `pair_perturb`, `deg_pairs`: a perturbation z orthogonal to the query vectors and to
          the vertex-edge incidence rows keeps every recorded answer and every degree.
          `weighted_lb`: every deterministic algorithm that returns the minimum 3-cut value of
          every complete graph on n ≥ 3 vertices with positive integer weights asks at least
          C(n,2) - n queries on some such graph (`free_pairs`: n(n-1) ≤ 2(cost + n)).

  Part L  Simulations. `Prot` is a two-party protocol tree (`exec`, `bits`); public coins are a
          family of protocols indexed by the random string, so a statement for every seed
          transfers error probabilities exactly.
          * `simQ_spec`: if every answer is pub(S) + a(S) + b(S), the algorithm becomes a
            protocol with the same output and 2c bits per query (`numA_spec`, `numB_spec`);
            `q_lt_pow`: simple-graph cut values fit in 2⌈log₂ n⌉ + 1 bits;
          * Lemma 24: `gamma_triangle_nat` (Γ_t on vertices < 3t has a triangle iff x, y
            intersect) and `triangle_protocol`;
          * Lemma 26: the canonical gadget `liG` (attachments determined by the base degrees)
            is simple with base degrees p (`liG_shape`), and `li_protocol` simulates it after
            exchanging the degree contributions (`vecA_spec`, `vecB_spec`);
          * Lemma 27: `kge4_protocol`, the composition DISJ → Γ_t → L_{k,M}(Γ_t);
          * the upper bound of Theorem 3: `additive_from_cut` (n degree queries, then one cut
            query per additive query);
          * Theorem 20: the fixed-slot adjacency array `nbr` of H_x: every entry depends on
            one bit of x (`nbr_local`), is a neighbour (`nbr_adj`), entries are distinct
            (`nbr_inj`), and every neighbour appears (`nbr_complete`).

  Part M  Deterministic communication complexity of disjointness, by a fooling set:
          `fooling_bound` (a fooling family of size m forces log₂ m bits), `allVecs_spec`,
          `disj_lower` (every deterministic protocol for DISJ_N sends ≥ N bits on some input),
          and `triangle_det_lb`: Lemma 24 for deterministic algorithms with no cited input,
          t² ≤ 2(2⌈log₂ 3t⌉ + 1)·(number of cut queries) on some Γ_t(x, y).

  Part N  Lemma 25 as a threshold and Lemma 27 for deterministic algorithms:
          `liK_lower`, `liK_attain`, `li_threshold` (for the canonical gadget with M ≥ k²p:
          λ_k + (k-1)(k-2) = 2(k-1)p, doubled, iff F has a (k-1)-clique; optimal partitions
          that split W are excluded by `clique_split`); `base_clique` (Γ_t joined to a
          (k-4)-clique U has a (k-1)-clique iff x and y intersect); and `kge4_det_lb`:
          every deterministic algorithm returning λ_k on these n-vertex simple graphs asks q
          queries on some input with t² ≤ 2p(⌈log₂ p⌉ + 1) + 2(2⌈log₂ n⌉ + 1)q.

  Part O  Remaining deterministic statements: `kge4_det_lb_part` (Lemma 27 for algorithms
          that output an optimum partition, via k shore queries, `valueOf_spec`);
          `weighted_ub` (Proposition 29, upper bound: n + n² cut queries reconstruct the
          weights, `q_pair`, `reconAlg_spec`, so λ₃ is computed exactly; with `weighted_lb` the
          deterministic complexity is Θ(n²)); `liG_connected` (Lemma 25: the gadget is
          connected); `iso_lambda3` (Proposition 22: λ₃(F + isolated vertex) = 0 iff F is
          disconnected, and the added vertex has no array entries).

  Part P  Corollary 28 (the singleton threshold) for deterministic algorithms. Base Γ_t + P₃
          (`path_clique`), H = L_{4,M}(Γ_t + P₃) with an optimum having exactly three singleton
          parts and λ₄(H) ≤ 3p - 2 (`H_facts`, via `iso3_cost`, `cost_even`, `li_threshold`);
          G = H plus q bridged public cliques of size 3p + q: λ_{4+q}(G) = λ₄(H) + q, with an
          optimum having exactly three singletons (`G_lamk`, using `compact`, `iter_mono` built
          on `strict_mono`, `cnt_image`, `clique_split`); G simple and connected
          (`cor28G_simple_conn`); `cor28_promise` and `cor28_det_lb`: every deterministic
          algorithm returning λ_{4+q} on these graphs asks q' queries on some input with
          t² ≤ 2p(⌈log₂ p⌉ + 1) + 2(2⌈log₂(p+M)⌉ + 1)q' (`simAdd_spec`, `det_lb_generic`).

  Part Q  Expected to worst-case query bounds (end of the proof of Lemma 27): `trunc`,
          `trunc_cost`, `trunc_run`, `markov_count` (Markov's inequality over S equally likely
          seeds), and `truncate_errors` (truncating at T queries adds at most C·S/(T+1) wrong
          seeds to a randomized algorithm of expected cost C).

  Part R  Theorem 20 on the concrete graphs G_x = H_x + K_m + bridge (`Gx`): equation
          (bridge-min3), λ₃(G_x) = 1 + min{λ₂(H_x), m - 1} (`Gx_lambda3`), and the structure
          of the optima: for 2|x| ≤ m - 2 every optimum keeps J whole and cuts H_x exactly along
          (A, B) (`Gx_opt_small`); for 2|x| ≥ m every optimum keeps H_x whole (`Gx_opt_large`).
          Reciprocity of the fixed-slot arrays: `nbr_recip`.
          With m = 2k and |x| ∈ {k-1, k} these are the cases used in the proof.

  Not formalized: the randomized sparsifier and its query cost, the Grebinski–Kucherov
  reconstruction bound, Razborov's randomized disjointness bound and the quantum adjacent-weight bound
  (cited), and the quantum-circuit step that turns a classical bit-local array entry into a
  coherent oracle call with O(1) queries (compute and uncompute).
-/

