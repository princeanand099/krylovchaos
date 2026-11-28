# External Axioms & Kernel Soundness

## 1. Custom Axiom & `sorry` Summary
- **Custom axioms in `KrylovChaos/`**: **0** (`#print axioms` verified via `KrylovChaos/AuditAxioms.lean` across **280 headline theorems** to depend exclusively on Lean 4's three standard axioms `propext`, `Classical.choice`, and `Quot.sound`).
- **`sorry` / `admit` in `KrylovChaos/`**: **0** across all **80** library modules.
- **Non-vacuity checks**: **12** concrete instantiations (`N = 2`, `D = 4`, `r = 2`) in `KrylovChaos/SanityChecks.lean`.
- **Standalone verification**: Strictly Mathlib `v4.35.0` (`leanprover/lean4:v4.35.0`), verified by `lake build`, `lake env lean KrylovChaos/AuditAxioms.lean`, and `lake comparator`.

## 2. Concrete Operator-Level Coverage Against `finite_temp_krylov_chaos.tex`

- **Sections 1 & 3 (Theorem 1.1(a), Lemma 3.1)**:
  - Unconditional infinite-chain Krylov ODE existence, Carleman $\ell^2$-uniqueness, all-time convergence, single-exponential Fatou Eqs. (1.12)–(1.13), and `limsup` rate bound (`InfiniteChainUnconditional.lean`: `theorem_1_1a_infinite_chain_complete`, `infiniteKrylovWavefn_tendsto_all_time`, `realInfiniteKrylovWavefn_tendsto`).
- **Section 2 (Lemma 2.1, Propositions 2.2–2.3, Concrete Gibbs, Lanczos & Majoranas)**:
  - Spectral functional calculus `hermFunc`, `gibbsRho`, `[H, ρ_β^{1/4}] = 0`, `NormedSpace.exp` bridge, qubit and Majorana `LocalInteractionDecomp` & Lemma 2.1(1)–(3) (`lemma_2_1_qubit_exp_bound`, `majoranaLocalInteractionDecomp`), standalone `jBeta` bijectivity/`LinearEquiv`, `isEvenParity H → isEvenParity ρQuarter` wired into Prop. 2.3(2) Eq. (2.10), and Hilbert–Schmidt commutator size identity.
- **Section 4 (Proposition 4.1, Lemma 4.2, Proposition 4.3, Theorem 1.1(b))**:
  - Concrete qubit & Majorana Prop. 4.1(1)–(2) Eq. (4.2), Lemma 4.2 Eq. (4.3), family-level bounded-`s` qubit & `2n`-normalized Majorana Thm. 1.1(b) (`HighTempSharpBounds.lean`: `theorem_1_1b_family_concrete_qubit_bounded_s`, `theorem_1_1b_family_majorana_2n_normalized`), and Prop. 4.3 `lambdaMSS` bound for arbitrary full-rank product states.
- **Section 5 (Theorem 1.2(a)–(c), Lemma 5.1)**:
  - Concrete `QubitOp N` spectral measure `cosh` bound and holomorphic strip half-width `r_W ≥ β/2 + κ` (`ConcreteSpectralStrip.lean`: `theorem_1_2a_concrete_spectralMeasure_cosh_bound`, `theorem_1_2a_concrete_family_holoStrip`), exact Meixner/sech moment identity & Lemma 5.1 Eq. (5.5) (`MeixnerMomentIdentity.lean`: `jacobiMat_meixner_even_moment_eq_sech_integral`, `lemma_5_1_eq_5_5_exact_sech_comparison`), concrete Lanczos moment bridge & Cauchy–Hadamard from `holoStripHalfWidth`, concrete time-ordered correlator `T_{τ,N}(t)` dominance Eq. (1.17) (`TimeOrderedOTOC.lean`), and thermodynamic-limit OTOC strip analyticity via Vitali–Montel (`ConcreteOTOCStrip.lean`: `theorem_1_2c_general_otoc_strip_analyticity`, `theorem_1_2c_thermo_limit_otoc_strip`).
- **Section 6 (Lemma 6.1, Proposition 6.2, Lemma 6.3, Proposition 6.4, Corollary 6.5)**:
  - Concrete operator-level Lemma 6.1, sharp Prop. 6.2 prefactor `(3/2)(1 - β/(4κ))⁻²` (`HighTempSharpBounds.lean`: `prop_6_2_sharp_r_local_high_temp`), Kotecký–Preiss polymer partition function & Cauchy order-2 Schwarz Lemma 6.3 Eq. (6.3) (`HighTempPolymerZ.lean`, `HighTempCumulant.lean`), shifted-commutator `S_β = I + II + III` (`ShiftedThermalSize.lean`), entropic background decoupling Prop. 6.4(2) Eq. (6.7) (`EntropicDecoupling.lean`, `HighTempSharpBounds.lean`: `prop_6_4_part2_unconditional`, `prop_6_4_part2_extended`), and all-time Duhamel Lieb–Robinson & lattice Cor. 6.5 Eq. (6.10) (`AllTimeLiebRobinson.lean`, `Cor65LatticeBound.lean`).
- **Section 7 (Lemmas 7.1–7.3, Theorem 1.3(a)–(c))**:
  - High-temperature parameter bridge (`HighTempParams.lean`, `HighTempSharpBounds.lean`) discharging Lemma 7.2, multi-site Lemma 7.3(1) Eq. (7.11) (`lemma_7_3_part1_multisite_eq_7_11`), two-sided Theorem 1.3(a) (`theorem_1_3a_high_temp_two_sided`), and Theorem 1.3(b) directly from `β ∈ [0, betaWC]`, plus concrete Eq. (1.24) and end-to-end family-level Theorem 1.3(c) (`HighTempChaosBound.lean`, `ConcreteOTOCStrip.lean`: `theorem_1_3c_eq_1_24_concrete`, `theorem_1_3c_concrete_family_complete`).
- **Section 8 (1D Araki Expansional & Classical Ising)**:
  - Complete all-temperature 1D finite-range Araki complex-time & Glauber bounds (`ArakiOneDimAllTemp.lean`, `HighTempSharpBounds.lean`: `prop_8_1_araki_1d_complete`), multi-edge discrete Hubbard–Stratonovich mixture Lemma 8.2 (`lemma_8_2_ising_hs_mixture`), explicit `2^Δ exp(2 β H_max)` Prop. 8.3 Eq. (8.4) (`prop_8_3_ising_explicit_eq_8_4`), and quantum diagonal-Ising `Q̃ = D` / `𝒬 = L_G` operator reverse Poincaré equivalence (`prop_8_3_quantum_diag_ising_reverse_poincare`).
- **Section 9 & Appendix B (Proposition 9.1(1)–(3), Lemma B.1)**:
  - Concrete 2D Gaussian-smeared `concreteOTOC` Bochner convolution & geometric-mean `√n` bound (`Section9EndToEnd.lean`: `concreteOTOC_gaussianSmearBochner_eq_2d_conv`, `prop_9_1_part1_concrete_2d_otoc_smearing`, `prop_9_1_part1_geom_mean_sqrt_n`), exact Eq. (9.1) qubit-1-conditioned bimodal state & `A = √2 |1⟩⟨1|_1` violation of (H2) (`eq91Bimodal_lambdaMSS_lower`, `prop_9_1_part2_eq91_violates_H2`), `D × D` double-well Lanczos basis `{|K₀⟩, |K₁⟩}` tridiagonal closure & `K(t) = sin²(Δ t / 2)` (`doubleWell_lanczos_tridiag_closure`, `doubleWell_krylov_complexity_from_lanczos`), Courant–Fischer bulk eigenvalue localization (`lemma_B_1_bulk_eigenvalues_in_band`), and Prop. 9.1(3) Eq. (9.3) (`DoubleWellTunneling.lean`).
- **Appendix A (Lemmas A.1–A.3)**:
  - Sharp `4^(m-1)` Catalan bound, Knuth `forestSum`, polymer-to-bintree bridge, root-reversal exponential bound, and multi-type heterogeneous-locality Lemma A.3 (`lemma_A_3_multiType_unordered_tree_sum`).

## 3. Compatibility Helper Modules
Earlier modules (`DepolarizedFrame.lean`, `GlauberDecoupling.lean`, `PolymerTrees.lean`, `OperatorBridges.lean`) retain algebraic helper lemmas referenced by `comparator/Challenge.lean`; all headline manuscript theorems are proved directly on concrete operator-level objects in the modules listed above.
