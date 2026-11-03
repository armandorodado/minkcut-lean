# MinKCut: Lean 4 formalization for "Query Complexity of Exact Minimum k-Cut"

[![Lean](https://github.com/armandorodado/minkcut-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/armandorodado/minkcut-lean/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23900203.svg)](https://doi.org/10.5281/zenodo.23900203)

Plain Lean 4 (v4.15.0, core library only: no Mathlib, no `sorry`, no `native_decide`).
Only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) are used.

## Build

```
lake build                         # about 2 minutes
lake env lean scripts/Axioms.lean  # axioms used by the main theorems
```

The toolchain is pinned in `lean-toolchain`; with [elan](https://github.com/leanprover/elan)
installed, `lake build` fetches it automatically. The GitHub workflow in
`.github/workflows/lean.yml` runs both commands on every push and fails if any main theorem
depends on `sorryAx`.

## Layout

| Module | Contents |
|---|---|
| `MinKCut/Basic.lean` | sums, cut values, costs; Part A: cut identities (Lemma 4, Corollary 7) |
| `MinKCut/Arith.lean` | Parts B–E: potential argument (Lemma 13), exchange inequalities, Li's gadget arithmetic, complete graphs |
| `MinKCut/Cover.lean` | Part F: covering lemmas (Lemmas 14, 15, Theorem 18), Lemma 12, λ₃(K_m), strict monotonicity, Li's gadget (Lemma 25), Theorem 20 |
| `MinKCut/Switching.lean` | Part H: switching graphs H_x (Theorem 20) |
| `MinKCut/Certificate.lean` | Part I: forest-packing certificate (Lemma 6) |
| `MinKCut/Queries.lean` | Part J: query costs of Lemmas 6, 8, 12 |
| `MinKCut/Gamma.lean` | Part G: triangles of Γ_t (Lemma 24) |
| `MinKCut/Weighted.lean` | Part K: Proposition 29 (weighted deterministic lower bound) |
| `MinKCut/Simulation.lean` | Part L: communication, additive-query and fixed-slot simulations |
| `MinKCut/Disjointness.lean` | Part M: deterministic communication complexity of set disjointness |
| `MinKCut/LowerBounds.lean` | Parts N–P: Lemma 25 threshold, Lemma 27 and Corollary 28 (deterministic), Propositions 22 and 29 (upper bound) |
| `MinKCut/Truncation.lean` | Part Q: expected to worst-case query bounds |
| `MinKCut/Bridge.lean` | Part R: Theorem 20 on the graphs G_x — equation (bridge-min3) and the structure of the optima |

`MinKCut.lean` imports everything and contains the overview of what is and is not formalized.
Section 7 of the paper maps each result to its Lean theorems.

## Citation

Archived on Zenodo: [doi:10.5281/zenodo.23900203](https://doi.org/10.5281/zenodo.23900203)
(see also `CITATION.cff`).

## License

MIT (see `LICENSE`).

## Not formalized

The randomized sparsifier and its query cost, the Grebinski–Kucherov reconstruction bound,
Razborov's randomized disjointness bound, the quantum adjacent-weight bound, and the
compute–uncompute step of the quantum simulation (all cited or standard).
