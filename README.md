# KrylovChaos — Lean 4 Formalization of *Finite-Temperature Bounds on Operator Growth and Quantum Chaos*

Lean 4 (`v4.35.0`, strictly Mathlib-only, **zero custom axioms**, **zero `sorry`s**) formalization of *Finite-Temperature Bounds on Operator Growth and Quantum Chaos* (`finite_temp_krylov_chaos.tex`).

## Verification Status

- **Toolchain**: `leanprover/lean4:v4.35.0` with standard Mathlib (`v4.35.0`).
- **Modules**: 47 modules under `KrylovChaos/`.
- **Axioms & `sorry`s**: Zero custom axioms and zero `sorry`s across `KrylovChaos/` (verified via `KrylovChaos/AuditAxioms.lean` using `#print axioms` across 101 headline theorems, depending solely on Lean 4's three standard axioms `propext`, `Classical.choice`, and `Quot.sound`).
- **Comparator**: `comparator/ChallengeDefs.lean` imports the exact union of Mathlib modules used across `KrylovChaos/` so `lake comparator` synthesizes identical kernel typeclass instances in `Challenge` and `Solution`.

## Concrete Operator-Level Formalization Map

| Manuscript Section / Result | Concrete Lean 4 Module(s) | Key Formalized Theorems |
|---|---|---|
| **Section 1 & 3** (Thm. 1.1(a), Lemma 3.1) | `KrylovTail.lean`, `JacobiSemigroup.lean`, `InfiniteChainLimit.lean`, `ConcreteEndToEndWiring.lean` | Finite- and infinite-chain Krylov tail bound Eq. (1.12), Krylov complexity bound Eq. (1.13), explicit `θ₀ = 4` closed-form constant (`theorem_1_1a_infinite_exact_constant`) |
| **Section 2** (Lemma 2.1, Props. 2.2–2.3, Gibbs & Lanczos) | `GibbsConstruction.lean`, `WightmanIsometry.lean`, `QubitAlgebra.lean` | Concrete spectral functional calculus `hermFunc`, `gibbsRho`, `concreteGibbsData`, `localHamiltonianGibbs`, `[H, ρ_β^{1/4}] = 0`, Heisenberg evolution `heisenbergEvol` + ODE, concrete Wightman Lanczos recursion Eq. (2.6) (`lanczosOp`, `lanczosCoeff`, `lanczos_three_term`, `concreteKrylovComplexity`), `wightmanQ`, `quantumGlauberGen`, `otocI`, `otocCW`, `lambdaMSS` |
| **Section 4** (Prop. 4.1, Lemma 4.2, Prop. 4.3, Thm. 1.1(b) core) | `OperatorGlauberAndLanczosFiltration.lean`, `ConcreteEndToEndWiring.lean`, `ProductStateMultiSite.lean`, `Filtration.lean` | `matComm_mem_filtration`, `lanczosOp_mem_filtration`, `lanczosTrunc_mem_filtration`, `prop_4_1_concrete_operator`, `lemma_4_2_concrete_operator`, `prop_4_3_concrete_product_state_bound` wired to `mssThermalSize` |
| **Section 5** (Thm. 1.2(a)–(c), Lemma 5.1) | `Theorem12Concrete.lean`, `SpectralDyck.lean`, `CausalNormBounds.lean`, `CarlemanJacobi.lean`, `VitaliAnalytic.lean` | Concrete operator-level strip-cosh identity Eq. (5.2) `theorem_1_2a_concrete_strip_cosh`, exponential spectral moment bound `theorem_1_2a_concrete_exp_moment`, Dyck-path lower bound `lemma_5_1_path_weight_lower`, Lanczos rate bound `theorem_1_2b_lanczos_rate_bound`, spectral OTOC dominance `theorem_1_2c_otoc_dominance` |
| **Section 6** (Lemma 6.1, Lemma 6.3, Prop. 6.4(2), Cor. 6.5) | `OperatorGlauberAndLanczosFiltration.lean`, `ClusterCumulantAndDecoupling.lean` | `lemma_6_1_concrete_operator`, `quantumRelEntropy_nonneg`, `gibbs_variational_bound` (Eq. 6.9), `power_series_schwarz_bound`, `normalizedTrace_mul_of_disjoint`, **Lemma 6.3** `lemma_6_3_trace_polymer_kp`, `gibbsRelEntropy_unitary_invariant`, `gibbsRelEntropy_heisenberg_invariant`, `gibbsRelEntropy_le_log_of_renyi2`, **Prop. 6.4(2)** `prop_6_4_2_concrete_entropic_decoupling`, and **Cor. 6.5** `lieb_robinson_concrete_opNorm` |
| **Section 7** (Lemmas 7.1–7.3, Thm. 1.3(a)–(c)) | `SupportAndDualFrame.lean`, `PolymerExpansionConcrete.lean`, `Lemma72Concrete.lean`, `HighTempConditioning.lean`, `HighTempReversePoincare.lean`, `MultiSiteCommutator.lean`, `CausalExpansion.lean`, `ShiftedCommutatorAndThm13c.lean`, `KoteckyPreiss.lean` | Concrete dual-frame `depol_global_reconstruct`, polymer expansion `opNorm_polyOp_le`, `depolDualWeight_exp_eq_polymerZ`, **Lemma 7.2** `lemma_7_2_concrete_positive_frame`, **unconditional Theorem 1.3(a)** `theorem_1_3a_unconditional`, **unconditional Theorem 1.3(b)** `theorem_1_3b_CW_unconditional` & `theorem_1_3b_otocI_unconditional` (`I(A) ≤ 216 Q(A)`), and **concrete end-to-end Theorem 1.3(c)** `theorem_1_3c_concrete_end_to_end` |
| **Section 8.1 & 8.2** (1D Araki Expansional & Classical Ising Prop. 8.3) | `Araki1DConcrete.lean`, `ArakiOneDim.lean`, `ThermodynamicKMS.lean`, `ClassicalIsingConcrete.lean` | Concrete 1D finite-range spin chain (`is1DFiniteRange`), uniform-in-`N` `opNorm_boundaryOp_le` and `heisenbergEvol_concrete_norm_bound`, plus `prop_8_3_concrete_convex_mixture_reverse_poincare` (Eq. 8.4) |
| **Section 9 & Appendix B** (Prop. 9.1(1)–(3), Lemma B.1) | `SpectralSmearingAndDoubleWell.lean`, `BimodalExact.lean` | Concrete `gaussianSmear`, exact spectral weight law `prop_9_1_part1_spectral_density` (Eq. 9.2), sub-Gaussian moments `prop_9_1_part1_subgaussian_moments`, exact bimodal counterexample (`BimodalExact.lean`), `doubleWell_even_odd_eigenpairs`, `schur_complement_eigen_eq`, `lemma_B_1_barrier_neumann_tunneling` |
| **Appendix A** (Lemmas A.1–A.3) | `ConcreteCombinatorics.lean` | Self-contained Catalan recurrence `catalanRec_le_four_pow`, `lemma_A_1_concrete_bin_tree_sum`, `lemma_A_1_concrete_exp_bound`, `lemma_A_2_concrete_causal_seq_sum`, `lemma_A_3_concrete_unordered_tree_sum` |

## Building Locally

```bash
lake build
```
