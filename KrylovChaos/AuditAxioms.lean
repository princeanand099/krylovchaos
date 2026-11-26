/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos

/-!
# Comprehensive Kernel Axiom Audit for `KrylovChaos` (All 28 Modules)

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

-- Concrete Operator-Algebraic & End-to-End Theorems (Milestones 6–10)
#print axioms KrylovChaos.eq_2_8_hs_commutator_size_identity
#print axioms KrylovChaos.prop_2_3_full_qubit_thermal_size
#print axioms KrylovChaos.prop_2_3_full_majorana_thermal_size
#print axioms KrylovChaos.gsBasis_wightman_orthonormal
#print axioms KrylovChaos.gsBasis_derives_singleSiteM
#print axioms KrylovChaos.totalSizeOp_bounds
#print axioms KrylovChaos.lemma_4_2_operator_thermal_size_truncation
#print axioms KrylovChaos.prop_4_1_loewner_dominance
#print axioms KrylovChaos.jacobiMat_moment_eq_dyck_sum
#print axioms KrylovChaos.lemma_5_1_moment_lower_bound
#print axioms KrylovChaos.meixner_sech_moment_lower_bound
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
