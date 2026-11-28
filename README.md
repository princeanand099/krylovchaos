# KrylovChaos — Lean 4 Formalization

Ground-up Lean 4 (`v4.35.0`) formalization of **Prince Anand**, *Finite-Temperature Bounds on Operator Growth and Quantum Chaos* (2026), built strictly on standard Mathlib `v4.35.0` with **zero custom axioms**, **zero `sorry`s**, and **zero external literature hypotheses**.

- Manuscript PDF: [`FiniteTempKrylovChaos.pdf`](FiniteTempKrylovChaos.pdf)
- Manuscript TeX: [`finite_temp_krylov_chaos.tex`](finite_temp_krylov_chaos.tex)
- Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`, `leanprover/comparator` `v4.35.0`
- Coverage: **82** library modules under `KrylovChaos/` (**13** concrete non-vacuity checks in `KrylovChaos/SanityChecks.lean`), **296** headline theorems verified via `#print axioms` in `KrylovChaos/AuditAxioms.lean`, and **33** locked headline theorems verified by `lake comparator`.
- Axioms: Strictly a subset of `[propext, Classical.choice, Quot.sound]`.

## Headline Theorem-to-Lean Mapping

| Manuscript Result | Concrete Lean Declaration(s) | Module(s) | Locked in `comparator` |
|---|---|---|---|
| Thm. 1.1(a), Lemma 3.1 (Infinite-chain Krylov ODE, Carleman uniqueness, Eqs. 1.12–1.13, `limsup ≤ 2α`) | `theorem_1_1a_infinite_chain_complete`, `theorem_1_1a_finite_tail`, `theorem_1_1a_finite_complexity` | `InfiniteChainUnconditional.lean`, `KrylovTail.lean` | Yes (4) |
| Prop. 2.2, Prop. 2.3, Lemma 2.1 (Wightman isometry, Eq. 2.8, Majorana Eq. 2.10, causal norm bounds) | `prop_2_2_wightman_isometry_inner`, `eq_2_8_hs_commutator_size_identity`, `prop_2_3_part2_majorana_from_even_H`, `lemma_2_1_qubit_exp_bound` | `QubitAlgebra.lean`, `WightmanIsometry.lean`, `MajoranaAlgebra.lean`, `CausalNormBounds.lean` | — |
| Prop. 4.1, Lemma 4.2, Prop. 4.3, Thm. 1.1(b) (Krylov filtration, product-state bound, static reduction) | `prop_4_1_krylov_filtration`, `theorem_1_1b_static_reduction`, `theorem_1_1b_family_concrete_qubit_bounded_s`, `prop_4_3_product_state_static_bound`, `prop_4_3_lambdaMSS_arbitrary_product_state` | `Filtration.lean`, `ProductStateLambdaMSS.lean`, `Theorem11bConcrete.lean` | Yes (3) |
| Thm. 1.2(a) (Concrete `QubitOp N` spectral measure, `cosh` integrability, Eq. 1.15, `β/2 + κ ≤ r_W`) | `theorem_1_2a_concrete_family_holoStrip`, `theorem_1_2a_laplace_identity`, `theorem_1_2a_even_exp_moment` | `ConcreteSpectralStrip.lean`, `SpectralDyck.lean` | Yes (3) |
| Thm. 1.2(b), Lemma 5.1 (Integral differentiation, Meixner `sech` identity, Eq. 1.16 `EReal` & finite `r_W`) | `iteratedDeriv_holo_eq_spectral_moment`, `theorem_1_2b_from_holoStripHalfWidth_ereal`, `theorem_1_2b_from_holoStripHalfWidth_finite`, `theorem_1_2b_lanczos_rate_bound`, `theorem_1_2b_rate_chain` | `MainTheoremPackaging.lean`, `MeixnerMomentIdentity.lean`, `SpectralDyck.lean` | Yes (4) |
| Thm. 1.2(c) (Three-way Eq. 1.17 `liminf` & `S_OTOC = (1/2) max(r_W, r_V)` strip analyticity) | `theorem_1_2c_thermo_limit_otoc_strip_three_way`, `theorem_1_2c_general_otoc_strip_max_width`, `theorem_1_2c_otoc_dominance` | `MainTheoremPackaging.lean`, `ConcreteOTOCStrip.lean`, `TimeOrderedOTOC.lean` | Yes (2) |
| Lemmas 6.1–6.3, Prop. 6.2 & 6.4, Cor. 6.5 (Sharp `3/2` bound, polymer cumulant, entropic decoupling, all-time LR) | `prop_6_2_sharp_r_local_high_temp`, `lemma_6_3_combined_cumulant_bound`, `prop_6_4_part2_extended`, `prop_6_4_decoupling_combine`, `cor_6_5_all_time_eq_6_10` | `HighTempSharpBounds.lean`, `HighTempCumulant.lean`, `EntropicDecoupling.lean`, `Cor65LatticeBound.lean` | Yes (1) |
| Lemmas 7.1–7.3, Thm. 1.3(a)–(c) (Normalized dual frame, exact two-sided Eq. 1.20, `54`/`216`, Eq. 1.24 chaos bound) | `lemma_7_2_high_temp_normalized`, `theorem_1_3a_high_temp_eq_1_20`, `theorem_1_3b_constants`, `theorem_1_3c_concrete_family_complete`, `theorem_1_3c_mss_lyapunov_bound` | `HighTempParams.lean`, `MainTheoremPackaging.lean`, `HighTempChaosFull.lean`, `ConcreteSpectralStrip.lean` | Yes (4) |
| Prop. 8.1, Lemma 8.2, Prop. 8.3 (All-temp 1D Araki `(r, R)`, active-edge Ising Eq. 8.4 `cosh²`) | `prop_8_1_araki_1d_independent_r_R`, `lemma_8_2_hubbard_stratonovich_identity`, `prop_8_3_ising_explicit_eq_8_4_cosh`, `prop_8_3_product_bernoulli_reverse_poincare` | `ArakiOneDimAllTemp.lean`, `ClassicalIsingConcrete.lean`, `MainTheoremPackaging.lean` | Yes (4) |
| Prop. 9.1(1)–(3), Lemma B.1 (2D Gaussian OTOC smearing, bimodal Eq. 9.1, `D × D` double-well Eq. 9.3 & bulk localization) | `prop_9_1_part1_concrete_2d_otoc_smearing`, `prop_9_1_part2_eq91_violates_H2`, `prop_9_1_part3_doubleWell_end_to_end_eq_9_3`, `lemma_B_1_bulk_eigenvalues_in_band`, `lemma_B_1_neumann_tail_sum` | `GaussianSmearingBridge.lean`, `BimodalFullRank.lean`, `DoubleWellKrylovLimit.lean`, `Section9EndToEnd.lean` | Yes (4) |
| Ground-up classical foundations (Carleman, Kotecký–Preiss, Vitali/Montel, Araki 1D) | `carleman_deficiency_zero`, `kotecky_preiss_convergence`, `vitali_power_series_convergence`, `araki_1d_entire_expansional` | `CarlemanJacobi.lean`, `KoteckyPreiss.lean`, `VitaliAnalytic.lean`, `ArakiOneDim.lean` | Yes (4) |
| Non-vacuity witnesses & concrete small-case checks | **13** concrete checks (`N = 2`, `N = 4` with `Δ = 2`, `D = 4`, `r = 2`) | `KrylovChaos/SanityChecks.lean` | — |

## Check It Yourself

```bash
lake build
lake env lean KrylovChaos/AuditAxioms.lean
lake comparator
```
