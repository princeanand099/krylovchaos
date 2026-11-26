# KrylovChaos — Lean 4 Formalization of *Finite-Temperature Bounds on Operator Growth and Quantum Chaos*

Lean 4 (`v4.35.0`, strictly Mathlib-only, **zero custom axioms**, **zero `sorry`s**) formalization of *Finite-Temperature Bounds on Operator Growth and Quantum Chaos* (`finite_temp_krylov_chaos.tex`).

## Verification Status

- **Toolchain**: `leanprover/lean4:v4.35.0` with standard Mathlib (`v4.35.0`).
- **Modules**: 39 modules under `KrylovChaos/`.
- **Axioms & `sorry`s**: Zero custom axioms and zero `sorry`s across `KrylovChaos/` (verified via `KrylovChaos/AuditAxioms.lean` using `#print axioms`, depending solely on Lean 4's three standard axioms `propext`, `Classical.choice`, and `Quot.sound`).
- **Comparator**: `comparator/ChallengeDefs.lean` imports the exact union of Mathlib modules used across `KrylovChaos/` so `lake comparator` synthesizes identical kernel typeclass instances in `Challenge` and `Solution`.

## Concrete Operator-Level Formalization Map

| Manuscript Section / Result | Concrete Lean 4 Module(s) | Key Formalized Theorems |
|---|---|---|
| **Section 1 & 3** (Thm. 1.1(a), Lemma 3.1) | `KrylovTail.lean`, `JacobiSemigroup.lean`, `InfiniteChainLimit.lean`, `ConcreteEndToEndWiring.lean` | Finite- and infinite-chain Krylov tail bound Eq. (1.12), Krylov complexity bound Eq. (1.13), explicit `θ₀ = 4` closed-form constant (`theorem_1_1a_infinite_exact_constant`) |
| **Section 2** (Lemma 2.1, Props. 2.2–2.3, Gibbs & Lanczos) | `GibbsConstruction.lean`, `WightmanIsometry.lean`, `QubitAlgebra.lean` | Concrete spectral functional calculus `hermFunc`, `gibbsRho`, `concreteGibbsData`, `localHamiltonianGibbs`, `[H, ρ_β^{1/4}] = 0`, Heisenberg evolution `heisenbergEvol` + ODE, concrete Wightman Lanczos recursion Eq. (2.6) (`lanczosOp`, `lanczosCoeff`, `lanczos_three_term`, `concreteKrylovComplexity`), `wightmanQ`, `quantumGlauberGen`, `otocI`, `otocCW`, `lambdaMSS` |
| **Section 4** (Prop. 4.1, Lemma 4.2, Prop. 4.3, Thm. 1.1(b) core) | `OperatorGlauberAndLanczosFiltration.lean`, `ConcreteEndToEndWiring.lean`, `ProductStateMultiSite.lean`, `Filtration.lean` | `matComm_mem_filtration`, `lanczosOp_mem_filtration`, `lanczosTrunc_mem_filtration`, `prop_4_1_concrete_operator`, `lemma_4_2_concrete_operator`, `prop_4_3_concrete_product_state_bound` wired to `mssThermalSize` |
| **Section 5** (Thm. 1.2(a)–(c), Lemma 5.1) | `Theorem12Concrete.lean`, `SpectralDyck.lean`, `CausalNormBounds.lean`, `CarlemanJacobi.lean`, `VitaliAnalytic.lean` | Concrete operator-level strip-cosh identity Eq. (5.2) `theorem_1_2a_concrete_strip_cosh`, exponential spectral moment bound `theorem_1_2a_concrete_exp_moment`, Dyck-path lower bound `lemma_5_1_path_weight_lower`, Lanczos rate bound `theorem_1_2b_lanczos_rate_bound`, spectral OTOC dominance `theorem_1_2c_otoc_dominance` |
| **Section 6** (Lemma 6.1, Gibbs–Donsker–Varadhan Eq. 6.9) | `OperatorGlauberAndLanczosFiltration.lean` | Concrete HS commutator identity `hsNormSq_siteSizeOp_eq_comm_avg`, `lemma_6_1_concrete_operator`, quantum relative entropy `quantumRelEntropy`, Klein's inequality `quantumRelEntropy_nonneg`, Gibbs–Donsker–Varadhan variational inequality Eq. (6.9) `gibbs_variational_bound` |
| **Section 7** (Lemmas 7.1 & 7.3, Thm. 1.3(a), Thm. 1.3(b) `C_W`) | `HighTempConditioning.lean`, `HighTempReversePoincare.lean`, `KoteckyPreiss.lean` | Concrete `depolPHalf`, `lemma_7_3_operator_conditioning`, `lemma_7_3_operator_best_approx`, concrete 4-step Gram–Schmidt `prodDepolBasis`, `lemma_7_3_operator_filtration_identity`, full operator-level **Theorem 1.3(a)** `theorem_1_3a_concrete_operator`, operator-level **Theorem 1.3(b)** `theorem_1_3b_concrete_CW` (`otocCW G A ≤ 54 Re (A | 𝒬^{(β)} A)_β^W`), abstract Kotecký–Preiss convergence `kotecky_preiss_convergence` |
| **Section 8.2** (Classical Ising & Convex-Mixture Reverse Poincaré, Prop. 8.3) | `ClassicalIsingConcrete.lean` | Concrete `SpinConfig N`, `prodBernoulli`, `p`-biased orthonormal Fourier basis `chiBasis`, `glauberDirichlet`, `degreeFiltrationQ`, `prop_8_3_concrete_convex_mixture_reverse_poincare` (Eq. 8.4) |
| **Section 9 & Appendix B** (Prop. 9.1(1)–(3), Lemma B.1) | `SpectralSmearingAndDoubleWell.lean`, `BimodalExact.lean` | Concrete `gaussianSmear`, exact spectral weight law `prop_9_1_part1_spectral_density` (Eq. 9.2), sub-Gaussian moments `prop_9_1_part1_subgaussian_moments`, exact bimodal counterexample (`BimodalExact.lean`), concrete `ℤ₂` double-well parity splitting `doubleWell_even_odd_eigenpairs`, Schur complement `schur_complement_eigen_eq`, Neumann-series exponential tunneling suppression `lemma_B_1_barrier_neumann_tunneling` |
| **Appendix A** (Lemmas A.1–A.3) | `ConcreteCombinatorics.lean` | Self-contained Catalan recurrence `catalanRec_le_four_pow`, `lemma_A_1_concrete_bin_tree_sum`, `lemma_A_1_concrete_exp_bound`, `lemma_A_2_concrete_causal_seq_sum`, `lemma_A_3_concrete_unordered_tree_sum` |

## Explicitly Open Sub-Gaps

See [`EXTERNAL-AXIOMS.md`](EXTERNAL-AXIOMS.md) for a transparent, itemized list of the remaining deep analytic sub-steps that are explicitly marked as open rather than hidden behind scalar-wrapper hypotheses (specifically: the concrete non-commutative Dyson/polymer operator expansion `Q_γ` for Lemma 7.2, the imaginary-time shifted commutator bound `I(A) ≤ 216 (A | 𝒬^{(β)} A)_β^W` and full `{H_N}` derivation of Theorem 1.3(c), the trace cluster expansion of Lemma 6.3 / shell expansion of Prop. 6.4(2) / geometric Lieb–Robinson of Cor. 6.5, and the non-commutative 1D Araki transfer-operator expansional).

## Building Locally

```bash
lake build
```
