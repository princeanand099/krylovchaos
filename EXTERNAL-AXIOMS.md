# External Axioms & Kernel Soundness

## 1. Custom Axiom & `sorry` Summary
- **Custom axioms in `KrylovChaos/`**: **0** (`#print axioms` verified via `KrylovChaos/AuditAxioms.lean` across **232 headline theorems** to depend exclusively on Lean 4's three standard axioms `propext`, `Classical.choice`, and `Quot.sound`).
- **`sorry` / `admit` in `KrylovChaos/`**: **0** across all **69** library modules.
- **Standalone verification**: Strictly Mathlib `v4.35.0` (`leanprover/lean4:v4.35.0`), verified by `lake build`, `lake env lean KrylovChaos/AuditAxioms.lean`, and `lake comparator`.

## 2. Concrete Operator-Level Coverage Against `finite_temp_krylov_chaos.tex`

- **Sections 1 & 3 (Theorem 1.1(a), Lemma 3.1)**:
  - Infinite-chain Krylov ODE satisfaction and initial condition `φ m 0 = δ_{m0}` (`infinite_krylov_ode_of_pointwise_limit`), Carleman $\ell^2$-uniqueness (`infinite_krylov_ode_carleman_l2_unique`, `infinite_krylov_ode_linear_growth_l2_unique`), single-exponential Fatou Eqs. (1.12)–(1.13) (`theorem_1_1a_infinite_fatou_exact_single_exp`), and `limsup` rate bound including `b 1 = 0` (`theorem_1_1a_limsup_rate_bound_nonneg`).
- **Section 2 (Lemma 2.1, Propositions 2.2–2.3, Concrete Gibbs, Lanczos & Majoranas)**:
  - Spectral functional calculus `hermFunc`, `gibbsRho`, `[H, ρ_β^{1/4}] = 0`, `NormedSpace.exp` bridge (`qubitOpToCLM_heisenbergEvol_eq_tsum_adPow`), standalone `jBeta` bijectivity/`LinearEquiv` (`jBetaLinearEquiv`, `prop_2_2_part1_jBeta_bijective`), Majorana `LocalInteractionDecomp` & Lemma 2.1(1)–(3) (`majoranaLocalInteractionDecomp`), `isEvenParity H → isEvenParity ρQuarter` wired into Prop. 2.3(2) Eq. (2.10) (`isEvenParity_concreteGibbsRhoQuarter`, `prop_2_3_part2_majorana_from_even_H`), and Hilbert–Schmidt commutator size identity (`hsNormSq_siteSizeOp_jBeta_eq_comm_avg`).
- **Section 4 (Proposition 4.1, Lemma 4.2, Proposition 4.3, Theorem 1.1(b))**:
  - Concrete qubit & Majorana Prop. 4.1(1)–(2) Eq. (4.2), Lemma 4.2 Eq. (4.3), concrete & family-level Thm. 1.1(b) (`theorem_1_1b_family_concrete_qubit`, `theorem_1_1b_majorana_concrete`, `theorem_1_1b_family_majorana`), and Prop. 4.3 `lambdaMSS` bound for arbitrary non-diagonal full-rank product states (`prop_4_3_lambdaMSS_arbitrary_product_state`).
- **Section 5 (Theorem 1.2(a)–(c), Lemma 5.1)**:
  - Asymmetric Eq. (5.2)–(5.4) chain, `Integrable (cosh (r * ω))`, Eq. (1.15) & `r_W ≥ β/2 + κ` (`theorem_1_2a_thermo_limit_eq_1_15_and_rW`, `wightmanStripHalfWidth_ge_beta_half_add_kappa`), concrete Lanczos tridiagonalization moment identity + Cauchy–Hadamard from strip integrability (`concrete_lanczos_moment_eq_jacobi`, `theorem_1_2b_from_strip_measure`), concrete time-ordered correlator `T_{τ,N}(t)` dominance Eq. (1.17) (`TimeOrderedOTOC.lean`: `concreteOTOC_norm_le_timeOrderedT`, `theorem_1_2c_concrete_eq_1_17`), and Montel + Vitali strip extension (`vitali_montel_strip_extension`).
- **Section 6 (Lemma 6.1, Proposition 6.2, Lemma 6.3, Proposition 6.4, Corollary 6.5)**:
  - Concrete operator-level Lemma 6.1, Prop. 6.2 `3/2` prefactor (`prop_6_2_exact_three_halves`), Kotecký–Preiss polymer partition function & Cauchy order-2 Schwarz Lemma 6.3 Eq. (6.3) (`HighTempPolymerZ.lean`, `HighTempCumulant.lean`: `lemma_6_3_combined_cumulant_bound`), shifted-commutator `S_β = I + II + III` with `III(A) = Re Tr((ρ_A - ρ_β) ℬ_β)` (`ShiftedThermalSize.lean`: `prop_6_4_part1_shifted_eq_6_4`), entropic background decoupling Prop. 6.4(2) Eq. (6.7) (`EntropicDecoupling.lean`: `prop_6_4_part2_unconditional`), and all-time Duhamel Lieb–Robinson & lattice Cor. 6.5 Eq. (6.10) (`AllTimeLiebRobinson.lean`, `Cor65LatticeBound.lean`: `all_time_lieb_robinson_exp`, `cor_6_5_all_time_eq_6_10`).
- **Section 7 (Lemmas 7.1–7.3, Theorem 1.3(a)–(c))**:
  - High-temperature parameter bridge (`HighTempParams.lean`: `highTempBetaWC_discharges_params`, `lemma_7_2_high_temp`, `theorem_1_3a_high_temp`, `theorem_1_3b_high_temp`) discharging Lemma 7.2 and Theorem 1.3(a)–(b) directly from `β ∈ [0, betaWC]`, and concrete Eq. (1.24) + family-level Theorem 1.3(c) (`HighTempChaosBound.lean`: `theorem_1_3c_eq_1_24_concrete`, `theorem_1_3c_unconditional_family`).
- **Section 8 (1D Araki Expansional & Classical Ising)**:
  - All-temperature 1D Araki complex-time norm bound via concentric range-`r` shell causality (`ArakiOneDimAllTemp.lean`: `heisenbergEvol_1d_all_temp_bound`, `opNorm_heisenbergEvol_pauliSite_1d_all_temp`, `prop_8_1_araki_1d_unconditional`), strict `i < j` Classical Ising Gibbs measure, multi-edge discrete Hubbard–Stratonovich Prop. 8.3 Eq. (8.4), and diagonal qubit $L^2$ bridge.
- **Section 9 & Appendix B (Proposition 9.1(1)–(3), Lemma B.1)**:
  - Gaussian time-smearing Bochner integral & fixed-`σ` OTOC Lyapunov preservation (`DoubleWellTunneling.lean`: `prop_9_1_part1_fixed_sigma_otoc_lyapunov`), bimodal $\Theta(N)$ size & direct (H2) violation for all `δ ∈ [0, 1)` (`prop_9_1_part2_bimodal_direct_H2_violation`), and `D × D` symmetric tridiagonal double-well matrix Sturm simplicity, parity, Rayleigh bounds, eigenvector decay Eqs. (B.2)–(B.3), and Prop. 9.1(3) Eq. (9.3) (`lemma_B_1_eigenvec_decay_eq_B2_B3`, `prop_9_1_part3_exact_D_limit_eq_9_3`).
- **Appendix A (Lemmas A.1–A.3)**:
  - Sharp `4^(m-1)` Catalan bound, Knuth `forestSum`, polymer-to-bintree bridge, root-reversal exponential bound, and multi-type heterogeneous-locality Lemma A.3 (`lemma_A_3_multiType_unordered_tree_sum`).

## 3. Compatibility Helper Modules
Earlier modules (`DepolarizedFrame.lean`, `GlauberDecoupling.lean`, `PolymerTrees.lean`, `OperatorBridges.lean`) retain algebraic helper lemmas referenced by `comparator/Challenge.lean`; all headline manuscript theorems are proved directly on concrete operator-level objects in the modules listed above.
