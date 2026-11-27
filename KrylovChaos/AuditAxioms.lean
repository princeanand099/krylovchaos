/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos

/-!
# Comprehensive Kernel Axiom Audit for `KrylovChaos` (All 52 Modules)

Run with `lake env lean KrylovChaos/AuditAxioms.lean`.
Every listed headline theorem must depend strictly on a subset of
`[propext, Classical.choice, Quot.sound]` — zero `sorryAx`, zero custom axioms.
-/

-- Original Headline & Literature Theorems
#print axioms KrylovChaos.theorem_1_1a_finite_tail
#print axioms KrylovChaos.theorem_1_1a_finite_complexity
#print axioms KrylovChaos.theorem_1_1a_infinite_tail_and_complexity
#print axioms KrylovChaos.theorem_1_1b_static_reduction
#print axioms KrylovChaos.prop_4_3_product_state_static_bound
#print axioms KrylovChaos.theorem_1_2a_laplace_identity
#print axioms KrylovChaos.theorem_1_2b_lanczos_rate_bound
#print axioms KrylovChaos.theorem_1_2c_otoc_dominance
#print axioms KrylovChaos.prop_6_4_decoupling_combine
#print axioms KrylovChaos.theorem_1_3a_reverse_poincare
#print axioms KrylovChaos.theorem_1_3c_mss_lyapunov_bound
#print axioms KrylovChaos.prop_8_3_product_bernoulli_reverse_poincare
#print axioms KrylovChaos.prop_9_1_bimodal_exact_size
#print axioms KrylovChaos.prop_9_1_double_well_tunneling_limit
#print axioms KrylovChaos.carleman_deficiency_zero
#print axioms KrylovChaos.kotecky_preiss_convergence
#print axioms KrylovChaos.vitali_strip_uniform_convergence
#print axioms KrylovChaos.araki_1d_entire_expansional

-- Concrete Operator-Algebraic, Infinite-Chain & Thermodynamic-Limit Theorems
#print axioms KrylovChaos.eq_2_8_hs_commutator_size_identity
#print axioms KrylovChaos.prop_2_3_full_qubit_thermal_size
#print axioms KrylovChaos.prop_2_3_part1_qubit_eq_2_9
#print axioms KrylovChaos.prop_2_3_full_majorana_thermal_size
#print axioms KrylovChaos.prop_2_3_part2_majorana_eq_2_10
#print axioms KrylovChaos.gsBasis_wightman_orthonormal
#print axioms KrylovChaos.gsBasis_derives_singleSiteM
#print axioms KrylovChaos.totalSizeOp_bounds
#print axioms KrylovChaos.lemma_4_2_operator_thermal_size_truncation
#print axioms KrylovChaos.prop_4_1_loewner_dominance
#print axioms KrylovChaos.jacobiMat_moment_eq_dyck_sum
#print axioms KrylovChaos.lemma_5_1_moment_lower_bound
#print axioms KrylovChaos.meixner_sech_moment_lower_bound
#print axioms KrylovChaos.meixner_euler_moment_rate_ge_two_div_pi
#print axioms KrylovChaos.theorem_1_2b_zero_laundering
#print axioms KrylovChaos.theorem_1_2b_liminf_unconditional
#print axioms KrylovChaos.exp_conj_eq_tsum_adPow
#print axioms KrylovChaos.lemma_2_1_causal_norm_sum
#print axioms KrylovChaos.lemma_2_1_single_site_exp_bound
#print axioms KrylovChaos.lemma_2_1_r_local_exp_bound
#print axioms KrylovChaos.prop_9_1_bimodal_operator_exact_size
#print axioms KrylovChaos.eq_5_1_wightman_fourier_identity
#print axioms KrylovChaos.eq_5_2_strip_laplace_identity
#print axioms KrylovChaos.eq_5_2_strip_cosh_identity
#print axioms KrylovChaos.theorem_1_2b_end_to_end
#print axioms KrylovChaos.jacobiUnitary_norm_preserve
#print axioms KrylovChaos.jacobiWavefn_ode
#print axioms KrylovChaos.theorem_1_1a_infinite_fatou_proved
#print axioms KrylovChaos.qubitLocalInteractionDecomp
#print axioms KrylovChaos.theorem_1_1b_end_to_end
#print axioms KrylovChaos.jacobiWavefn_coord_cauchy
#print axioms KrylovChaos.infiniteKrylovWavefn_tendsto
#print axioms KrylovChaos.theorem_1_1a_infinite_unconditional
#print axioms KrylovChaos.finiteKMS_entire
#print axioms KrylovChaos.finiteKMS_boundary_identity
#print axioms KrylovChaos.finiteKMS_normalized
#print axioms KrylovChaos.thermo_limit_state_exists
#print axioms KrylovChaos.thermo_limit_kms_boundary_transfer

-- Concrete Operator-Level Remediation Theorems (Flaws #1–#13)
#print axioms KrylovChaos.localHamiltonianGibbs_comm
#print axioms KrylovChaos.lanczos_three_term
#print axioms KrylovChaos.prop_4_3_concrete_product_state_bound
#print axioms KrylovChaos.prop_4_3_lambdaMSS_product_state
#print axioms KrylovChaos.prop_4_3_lambdaMSS_general_product_state
#print axioms KrylovChaos.prop_8_3_concrete_convex_mixture_reverse_poincare
#print axioms KrylovChaos.lemma_A_1_concrete_exp_bound
#print axioms KrylovChaos.lemma_A_1_polymer_to_bintree_bridge
#print axioms KrylovChaos.lemma_A_2_concrete_causal_seq_sum
#print axioms KrylovChaos.lemma_A_2_root_reversal_exp_bound
#print axioms KrylovChaos.lemma_A_3_concrete_unordered_tree_sum
#print axioms KrylovChaos.prop_9_1_part1_spectral_density
#print axioms KrylovChaos.prop_9_1_part1_subgaussian_moments
#print axioms KrylovChaos.lemma_B_1_barrier_neumann_tunneling
#print axioms KrylovChaos.theorem_1_2a_concrete_strip_cosh
#print axioms KrylovChaos.theorem_1_2a_concrete_exp_moment
#print axioms KrylovChaos.theorem_1_2a_concrete_eq52_trace_bound
#print axioms KrylovChaos.theorem_1_2a_concrete_eq53_opNorm_bound
#print axioms KrylovChaos.theorem_1_2a_concrete_eq54_r_local_bound
#print axioms KrylovChaos.lemma_6_1_concrete_wightman_commutator
#print axioms KrylovChaos.prop_6_2_concrete_high_temp_glauber
#print axioms KrylovChaos.lemma_7_3_operator_conditioning
#print axioms KrylovChaos.lemma_7_3_operator_best_approx
#print axioms KrylovChaos.lemma_7_3_operator_filtration_identity
#print axioms KrylovChaos.theorem_1_3a_concrete_operator
#print axioms KrylovChaos.theorem_1_3b_concrete_CW
#print axioms KrylovChaos.quantumRelEntropy_nonneg
#print axioms KrylovChaos.gibbs_variational_bound
#print axioms KrylovChaos.lemma_6_1_concrete_operator
#print axioms KrylovChaos.lanczosTrunc_mem_filtration
#print axioms KrylovChaos.theorem_1_1a_infinite_exact_constant
#print axioms KrylovChaos.prop_4_1_concrete_operator
#print axioms KrylovChaos.prop_4_1_part2_concrete_operator
#print axioms KrylovChaos.lemma_4_2_concrete_operator
#print axioms KrylovChaos.lemma_4_2_mss_thermal_size_concrete
#print axioms KrylovChaos.prop_2_2_part3_lanczos_state_invariance
#print axioms KrylovChaos.prop_2_2_part3_complexity_invariance

-- Concrete End-to-End Qubit Thm. 1.1(a)–(b), Analytic Foundations, Bridges & Sec. 9 (Items #8, #11–#23)
#print axioms KrylovChaos.theorem_1_1a_concrete_qubit_tail
#print axioms KrylovChaos.theorem_1_1a_concrete_qubit_complexity
#print axioms KrylovChaos.theorem_1_1b_concrete_qubit_thermal_size
#print axioms KrylovChaos.theorem_1_1a_limsup_rate_bound_unconditional
#print axioms KrylovChaos.infinite_krylov_ode_l2_unique
#print axioms KrylovChaos.wightmanAutocorr_eq_integral_spectralMeasure
#print axioms KrylovChaos.lintegral_cosh_le_of_weak_limit
#print axioms KrylovChaos.wightmanAutocorr_measure_differentiableOn_strip
#print axioms KrylovChaos.concreteOTOC_norm_le_wightmanNormSq
#print axioms KrylovChaos.otoc_strip_holomorphic_of_locally_uniform_limit
#print axioms KrylovChaos.prop_8_1_concrete_1d_glauber
#print axioms KrylovChaos.mssThermalSize_eq_I_add_II_add_III
#print axioms KrylovChaos.latticeBall_card_le
#print axioms KrylovChaos.cor_6_5_causal_ball_sum_bound
#print axioms KrylovChaos.theorem_1_3b_concrete_eq122
#print axioms KrylovChaos.isingHamiltonian_isHermitian
#print axioms KrylovChaos.diagOp_wightmanNormSq_eq_classical_L2
#print axioms KrylovChaos.prop_9_1_part1_entire_autocorr
#print axioms KrylovChaos.prop_9_1_part1_liminf_eq_zero
#print axioms KrylovChaos.prop_9_1_part2_bimodal_theta_N
#print axioms KrylovChaos.twoLevel_tunneling_complexity
#print axioms KrylovChaos.prop_9_1_part3_tunneling_time_lower_bound

-- Concrete Gap-Closure Theorems (Sub-Gaps #1–#4, 100% Unconditional on Mathlib)
#print axioms KrylovChaos.depol_global_reconstruct
#print axioms KrylovChaos.depolDualWeight_mul_of_disjoint
#print axioms KrylovChaos.norm_depolDualWeight_le
#print axioms KrylovChaos.opNorm_polyOp_le
#print axioms KrylovChaos.norm_polyWeight_le
#print axioms KrylovChaos.depolDualWeight_exp_eq_polymerZ
#print axioms KrylovChaos.lemma_7_2_concrete_positive_frame
#print axioms KrylovChaos.lemma_7_2_concrete_rho_half_normalized
#print axioms KrylovChaos.theorem_1_3a_unconditional
#print axioms KrylovChaos.theorem_1_3b_CW_unconditional
#print axioms KrylovChaos.prodDepolNormSq_matComm_supportedOn_le
#print axioms KrylovChaos.hasSum_heisenbergEvol_adPow
#print axioms KrylovChaos.fwdCausalSum_le
#print axioms KrylovChaos.fwdCausalSum_general_le
#print axioms KrylovChaos.revCausalSum_le
#print axioms KrylovChaos.theorem_1_3b_otocI_unconditional
#print axioms KrylovChaos.theorem_1_3c_concrete_end_to_end
#print axioms KrylovChaos.power_series_schwarz_bound
#print axioms KrylovChaos.normalizedTrace_mul_of_disjoint
#print axioms KrylovChaos.lemma_6_3_trace_polymer_kp
#print axioms KrylovChaos.gibbsRelEntropy_unitary_invariant
#print axioms KrylovChaos.gibbsRelEntropy_heisenberg_invariant
#print axioms KrylovChaos.gibbsRelEntropy_le_log_of_renyi2
#print axioms KrylovChaos.prop_6_4_2_concrete_entropic_decoupling
#print axioms KrylovChaos.lieb_robinson_concrete_opNorm
#print axioms KrylovChaos.opNorm_boundaryOp_le
#print axioms KrylovChaos.heisenbergEvol_concrete_norm_bound
