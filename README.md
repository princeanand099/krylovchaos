# KrylovChaos — Lean 4 Formalization

Ground-up Lean 4 (`v4.35.0`) formalization of **Prince Anand**, *Finite-Temperature Bounds on Operator Growth and Quantum Chaos* (November 2026), built strictly on standard Mathlib (`v4.35.0`) with **zero custom axioms**, **zero `sorry`s**, and **zero external literature hypotheses** across all 23 library modules.

## Verification Status

- **Toolchain**: Lean `v4.35.0` / Mathlib `v4.35.0` / `comparator` `v4.35.0`
- **Build**: `lake build` — **23 library modules**, **0 `sorry`s**, **0 custom axioms**, **0 orphan modules** (`Build completed successfully (3577 jobs). LAKE_BUILD_EXIT=0`)
- **Axiom Footprint**: Strictly standard Lean/Mathlib core axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Module Architecture (23 Modules)

| Module | Manuscript Scope | Key Verified Results |
|---|---|---|
| `KrylovChaos.Basic` | Preliminaries | Real/combinatorial helpers, exponential/logarithmic bounds |
| `KrylovChaos.QubitAlgebra` | Section 2.1, Eq. (2.8) | Concrete `QubitOp N`, Pauli string algebra, partial trace `ℰ_x`, `siteSizeOp`, `totalSizeOp`, **Eq. (2.8)** `eq_2_8_hs_commutator_size_identity`, concrete $r$-local commutator step `filtration_comm_step` |
| `KrylovChaos.MajoranaAlgebra` | Section 2.1, Eq. (2.10) | Concrete Jordan–Wigner $2n$-mode Majorana probes & generators, exact Clifford anticommutation `majoranaProbe_clifford` / `majoranaGen_clifford`, Majorana size identity, **full $2n$-Majorana Proposition 2.3 (Eq. 2.10)** `prop_2_3_full_majorana_thermal_size` |
| `KrylovChaos.WightmanIsometry` | Section 2.1–2.3 | Wightman inner product, isometry `jBeta`, causal-sequence scalar induction, Taylor majorant bounds |
| `KrylovChaos.ManyBodySetup` | Section 1–2, 9 | Concrete `LocalTerm` / `LocalHamiltonian N r`, `GibbsData N`, `otocCW`, `mssThermalSize`, **Prop 2.2(3)** `prop_2_2_lanczos_invariance`, **full $N$-qubit Prop 2.3 (Eq. 2.9)** `prop_2_3_full_qubit_thermal_size`, concrete `bimodalState` (Eq. 9.1), concrete `doubleWellMatrix` |
| `KrylovChaos.KrylovTail` | Section 3, Theorem 1.1(a) | Differential inequality, finite-chain and infinite-chain Krylov tail and complexity bounds |
| `KrylovChaos.Filtration` | Section 4.1–4.2, Theorem 1.1(b) | Krylov–filtration inclusion, static-to-dynamical reduction |
| `KrylovChaos.WightmanProjectors` | Section 4.1–4.2, Prop 4.1 & Lemma 4.2 | Self-adjointness & idempotence of `partialTraceSite`, **exact operator bounds** `0 ⪯ 𝒮 ⪯ N 1` (`totalSizeOp_bounds`), Cauchy–Schwarz (`totalSizeOp_cauchy_schwarz`), **operator-level Lemma 4.2 (Eq. 4.3)** `lemma_4_2_operator_thermal_size_truncation`, concrete Wightman orthogonal projectors `wightmanProj` (`Submodule.starProjection`), Loewner monotonicity & **Prop 4.1 Loewner dominance** `prop_4_1_loewner_dominance` |
| `KrylovChaos.ProductState` | Section 4.3, Prop 4.3 | Full $N$-qubit product-state static complexity bound `𝒮_β(A) ≤ s + m_max √(N s)` |
| `KrylovChaos.ProductStateDerivation` | Section 4.3, Eq. (4.6) | Concrete `singleSiteRho` roots, unitary invariance of `S_x`, Wightman Gram–Schmidt basis `gsBasis`, exact orthonormality `gsBasis_wightman_orthonormal`, **ground-up derivation of all 16 entries of `singleSiteM` (Eq. 4.6)** `gsBasis_derives_singleSiteM` |
| `KrylovChaos.SpectralDyck` | Section 5, Theorem 1.2 | Dyck-path shifting (`shiftDyckPath_isDyck`, `shiftDyckPath_injective`), Lemma 5.1 path-weight monotonicity, Theorem 1.2(b) rate bound, ground-up Theorem 1.2(c) OTOC dominance (`trace_mul_quad_bound`) |
| `KrylovChaos.LanczosMoments` | Section 5, Eqs. (5.4)–(5.5) | Concrete symmetric tridiagonal `jacobiMat D b`, **exact Dyck-path moment expansion** `jacobiMat_moment_eq_dyck_sum`, **full summed Lemma 5.1 moment bound** `lemma_5_1_moment_lower_bound`, **ground-up Meixner `sech` moment lower bound (Eq. 5.5)** `meixner_sech_moment_lower_bound` |
| `KrylovChaos.GlauberDecoupling` | Section 6, Lemma 6.1–6.2 | Finite-temperature Glauber decoupling and commutator-size bounds |
| `KrylovChaos.DepolarizedFrame` | Section 7, Theorem 1.3 | Depolarized-frame reduction and trace-distance stability |
| `KrylovChaos.PolymerTrees` | Section 7, Lemma 7.2–7.3 | Connected polymer-tree bounds and cluster-expansion decay |
| `KrylovChaos.ClassicalIsing` | Section 8, Theorem 1.4 | Classical Ising model thermal-size and Krylov complexity bounds |
| `KrylovChaos.StructuralNecessity` | Section 9, Prop 9.1–9.2 | Bimodal counterexample and double-well optimality bounds |
| `KrylovChaos.CarlemanJacobi` | Literature (Ground-Up) | Carleman divergence criterion & deficiency-index zero for Jacobi operators |
| `KrylovChaos.KoteckyPreiss` | Literature (Ground-Up) | Kotecký–Preiss cluster-expansion convergence |
| `KrylovChaos.VitaliAnalytic` | Literature (Ground-Up) | Vitali–Montel analytic continuation & normal-family convergence |
| `KrylovChaos.ArakiOneDim` | Literature (Ground-Up) | Araki 1D analyticity and transfer-matrix bounds |
| `KrylovChaos.OperatorBridges` | Cross-Section Integration | Imports all 4 literature modules, `theorem_1_1a_limsup_rate_bound` (`Filter.limsup`), `theorem_1_1a_carleman_esa`, `prop_4_1_concrete_qubit_filtration`, **Corollary 6.5 (Eq. 6.11)** `corollary_6_5_krylov_lieb_robinson`, global $N$-qubit 2-design frame (`globalDepolP`), `lemma_7_1_dual_trace_bound`, `lemma_8_2_multi_edge_hs` |
| `KrylovChaos.SanityChecks` | Verification | End-to-end instantiation and consistency checks |

## Honest Scope Notes

All finite-dimensional many-body operator-algebraic constructions (`QubitOp N`, Pauli strings, $2n$-Majorana Clifford algebra, partial trace, `0 ⪯ 𝒮 ⪯ N 1`, Wightman orthogonal projectors `Π_s^{(β)}`, Gram–Schmidt derivation of Eq. 4.6, operator-level Lemma 4.2, exact Dyck-path expansion of `jacobiMat ^ (2n)`, and the Gamma-integral Meixner `sech` lower bound Eq. 5.5) are formally verified from Mathlib `v4.35.0` with zero custom axioms. Infinite-dimensional operator-semigroup machinery (unbounded Trotter–Kato strong resolvent convergence on $\ell^2(\mathbb{N})$ and full $C^*$-algebraic KMS spectral measures in the $N \to \infty$ thermodynamic limit) remains represented at the level of its finite-dimensional Jacobi/Wightman reductions and Carleman/Vitali analytic criteria.
