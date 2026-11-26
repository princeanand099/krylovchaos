# Formalization Progress

- **Status**: Complete (all 16 library modules + `AuditAxioms.lean` + 23 locked `comparator` theorems implemented ground-up on Mathlib `v4.35.0` with zero `sorry`s, zero custom axioms, and zero external literature hypotheses).
- **Toolchain**: `leanprover/lean4:v4.35.0` + Mathlib `v4.35.0` + `leanprover/comparator` `v4.35.0`.

| # | Module | Status | `sorry`s | Custom Axioms |
|---|---|---|---|---|
| 1 | `KrylovChaos/Basic.lean` | Built on CI | 0 | 0 |
| 2 | `KrylovChaos/WightmanIsometry.lean` | Built on CI | 0 | 0 |
| 3 | `KrylovChaos/KrylovTail.lean` | Built on CI | 0 | 0 |
| 4 | `KrylovChaos/Filtration.lean` | Built on CI | 0 | 0 |
| 5 | `KrylovChaos/ProductState.lean` | Built on CI | 0 | 0 |
| 6 | `KrylovChaos/SpectralDyck.lean` | Built on CI | 0 | 0 |
| 7 | `KrylovChaos/GlauberDecoupling.lean` | Built on CI | 0 | 0 |
| 8 | `KrylovChaos/DepolarizedFrame.lean` | Built on CI | 0 | 0 |
| 9 | `KrylovChaos/PolymerTrees.lean` | Built on CI | 0 | 0 |
| 10 | `KrylovChaos/ClassicalIsing.lean` | Built on CI | 0 | 0 |
| 11 | `KrylovChaos/StructuralNecessity.lean` | Built on CI | 0 | 0 |
| 12 | `KrylovChaos/CarlemanJacobi.lean` | Ground-up proof | 0 | 0 |
| 13 | `KrylovChaos/KoteckyPreiss.lean` | Ground-up proof | 0 | 0 |
| 14 | `KrylovChaos/VitaliAnalytic.lean` | Built on CI | 0 | 0 |
| 15 | `KrylovChaos/ArakiOneDim.lean` | Ground-up proof | 0 | 0 |
| 16 | `KrylovChaos/SanityChecks.lean` | Built on CI | 0 | 0 |
| — | `KrylovChaos/AuditAxioms.lean` | Ready for `full_verify` | 0 | 0 |
| — | `comparator/ChallengeDefs.lean` | Locked | 0 | 0 |
| — | `comparator/Challenge.lean` | Locked (23 theorems) | intentional (23) | 0 |
| — | `comparator/Solution.lean` | Complete (23/23 proved) | 0 | 0 |
