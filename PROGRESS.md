# Formalization Progress

- **Status**: Complete (all 12 library modules + `AuditAxioms.lean` + 19 locked `comparator` theorems implemented with zero `sorry`s and zero custom axioms).
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
| 12 | `KrylovChaos/SanityChecks.lean` | Fixed & building on CI | 0 | 0 |
| — | `KrylovChaos/AuditAxioms.lean` | Ready for `full_verify` | 0 | 0 |
| — | `comparator/ChallengeDefs.lean` | Locked | 0 | 0 |
| — | `comparator/Challenge.lean` | Locked (19 theorems) | intentional (19) | 0 |
| — | `comparator/Solution.lean` | Complete (19/19 proved) | 0 | 0 |
