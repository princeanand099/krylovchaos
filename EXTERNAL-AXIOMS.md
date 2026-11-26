# External Axioms Audit

## Custom Axioms & External Literature Hypotheses: None (`0`)

`KrylovChaos` and `comparator/Solution.lean` contain **zero** `axiom` declarations, **zero** `sorry`s, **zero** `admit`s, **zero** `native_decide` calls, and **zero** external literature hypotheses. Every theorem — including the four classical background theorems from the mathematical physics literature — is proved **ground-up from standard Mathlib `v4.35.0` alone**, depending strictly on a subset of Lean 4's three standard logical axioms:

- `propext`
- `Classical.choice`
- `Quot.sound`

### Ground-Up Formalization of Literature Theorems

| Literature Theorem | Ground-Up Module | Proved Declarations |
|---|---|---|
| Carleman's essential self-adjointness criterion (infinite Jacobi operators) | `KrylovChaos/CarlemanJacobi.lean` | `carleman_divergence_of_linear_growth`, `carleman_deficiency_zero`, `carleman_flux_liminf_zero` |
| Kotecký–Preiss (1986) polymer cluster-expansion convergence | `KrylovChaos/KoteckyPreiss.lean` | `polymerZ_eq_add_incompat`, `kotecky_preiss_convergence`, `kotecky_preiss_log_bound` |
| Vitali / Montel normal-family analytic convergence on disks and strips | `KrylovChaos/VitaliAnalytic.lean` | `vitali_power_series_convergence`, `vitali_uniform_bound_preserved`, `vitali_strip_uniform_convergence` |
| Araki (1969) 1D complex-time analyticity structural & entire-series bounds | `KrylovChaos/ArakiOneDim.lean` | `araki_1d_boundary_count`, `araki_1d_block_commutator_indep`, `araki_1d_entire_expansional` |

Verify directly via:

```bash
lake env lean KrylovChaos/AuditAxioms.lean
```
