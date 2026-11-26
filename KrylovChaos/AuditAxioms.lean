/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos

/-!
# Axiom Audit for KrylovChaos

Prints the exact axiom dependencies of every headline theorem in `KrylovChaos`.
Every theorem must depend strictly on a subset of `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms KrylovChaos.prop_2_2_wightman_isometry_inner
#print axioms KrylovChaos.prop_2_2_liouvillian_self_adjoint
#print axioms KrylovChaos.prop_2_3_commutator_size_identity
#print axioms KrylovChaos.lemma_2_1_causal_commutator_induction
#print axioms KrylovChaos.theorem_1_1a_finite_tail
#print axioms KrylovChaos.theorem_1_1a_finite_complexity
#print axioms KrylovChaos.theorem_1_1a_infinite_tail_and_complexity
#print axioms KrylovChaos.prop_4_1_krylov_filtration
#print axioms KrylovChaos.prop_4_1_q_complexity_bound
#print axioms KrylovChaos.theorem_1_1b_static_reduction
#print axioms KrylovChaos.prop_4_3_product_state_static_bound
#print axioms KrylovChaos.theorem_1_2a_laplace_identity
#print axioms KrylovChaos.theorem_1_2a_even_exp_moment
#print axioms KrylovChaos.theorem_1_2a_binomial_series_summable
#print axioms KrylovChaos.lemma_5_1_path_weight_lower
#print axioms KrylovChaos.theorem_1_2b_lanczos_rate_bound
#print axioms KrylovChaos.theorem_1_2b_rate_chain
#print axioms KrylovChaos.theorem_1_2c_otoc_dominance
#print axioms KrylovChaos.prop_6_4_decoupling_combine
#print axioms KrylovChaos.lemma_7_1_dual_reconstruction
#print axioms KrylovChaos.theorem_1_3a_reverse_poincare
#print axioms KrylovChaos.theorem_1_3b_constants
#print axioms KrylovChaos.theorem_1_3c_mss_lyapunov_bound
#print axioms KrylovChaos.lemma_A_3_unordered_tree_induction
#print axioms KrylovChaos.lemma_8_2_hubbard_stratonovich_identity
#print axioms KrylovChaos.prop_8_3_product_bernoulli_reverse_poincare
#print axioms KrylovChaos.prop_9_1_no_linear_lower_bound
#print axioms KrylovChaos.prop_9_1_bimodal_exact_size
#print axioms KrylovChaos.lemma_B_1_neumann_tail_sum
