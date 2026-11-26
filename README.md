# KrylovChaos — Lean 4 Formalization

Lean 4 (`v4.35.0`) formalization of **Prince Anand**, *Finite-Temperature Bounds on Operator Growth and Quantum Chaos* (November 2026).

- Manuscript PDF: [`FiniteTempKrylovChaos.pdf`](FiniteTempKrylovChaos.pdf)
- Manuscript TeX: [`finite_temp_krylov_chaos.tex`](finite_temp_krylov_chaos.tex)
- Toolchain: `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`, `leanprover/comparator` `v4.35.0`
- Axioms: **Zero custom `axiom`s**, **zero `sorry`s** across `KrylovChaos/` and `comparator/Solution.lean` (every theorem depends strictly on a subset of `[propext, Classical.choice, Quot.sound]`).

## Theorem-to-Lean Mapping

| Manuscript Result | Lean Declaration(s) | Module | Locked in `comparator` |
|---|---|---|---|
| Parameters `κ`, `β_wc`, Catalan & factorial helpers | `invLocalityScale`, `betaWC`, `betaWC_lt_two_kappa`, `catalan_le_four_pow`, `pow_pred_div_factorial_le_exp`, `mono_nonincreasing_of_deriv_nonpos` | `KrylovChaos/Basic.lean` | — |
| Prop. 2.2 (Wightman isometry & Liouvillian) | `prop_2_2_wightman_isometry_inner`, `prop_2_2_wightman_isometry_commutes_liouvillian`, `prop_2_2_liouvillian_self_adjoint`, `prop_2_2_liouvillian_zero_diagonal` | `KrylovChaos/WightmanIsometry.lean` | — |
| Prop. 2.3 (Commutator & Majorana size identities) | `prop_2_3_commutator_size_identity`, `prop_2_3_majorana_size_identity` | `KrylovChaos/WightmanIsometry.lean` | — |
| Lemma 2.1 (Causal commutator induction & norm bounds) | `lemma_2_1_causal_commutator_induction`, `lemma_2_1_single_site_norm_bound`, `lemma_2_1_r_local_norm_bound` | `KrylovChaos/WightmanIsometry.lean` | — |
| Lemma 3.1 & Thm. 1.1(a) (Krylov tail & complexity bounds) | `finite_chain_unitarity`, `lemma_3_1_finite_chain_mgf`, `theorem_1_1a_finite_tail`, `theorem_1_1a_finite_complexity`, `theorem_1_1a_infinite_fatou_partial`, `theorem_1_1a_infinite_tail_and_complexity`, `theorem_1_1a_log_rate_bound` | `KrylovChaos/KrylovTail.lean` | Yes (3) |
| Prop. 4.1, Lemma 4.2 & Thm. 1.1(b) (Krylov filtration & static reduction `λ_L ≤ 2 α`) | `prop_4_1_krylov_filtration`, `prop_4_1_q_complexity_bound`, `lemma_4_2_thermal_size_truncation`, `theorem_1_1b_static_reduction` | `KrylovChaos/Filtration.lean` | Yes (2) |
| Prop. 4.3 (Product-state thermal-size static bound) | `singleSiteM_diag_le_one`, `prop_4_3_product_state_static_bound` | `KrylovChaos/ProductState.lean` | Yes (1) |
| Thm. 1.2(a)–(c) & Lemma 5.1 (Spectral decay, Dyck comparison, Lanczos rate `2 α ≤ 2π/(β + 2κ) < 2π/β`, OTOC dominance) | `theorem_1_2a_laplace_identity`, `theorem_1_2a_even_exp_moment`, `theorem_1_2a_binomial_series_summable`, `shiftDyckPath_isDyck`, `lemma_5_1_path_weight_lower`, `theorem_1_2b_lanczos_rate_bound`, `theorem_1_2b_rate_chain`, `trace_sq_norm_le_hsNormSq`, `theorem_1_2c_otoc_dominance` | `KrylovChaos/SpectralDyck.lean` | Yes (5) |
| Lemma 6.1, Prop. 6.2 & Prop. 6.4 (High-temperature Glauber & decoupling) | `lemma_6_1_single_site_commutator`, `prop_6_2_high_temp_glauber`, `prop_6_4_comm_splitting`, `prop_6_4_third_term_identity`, `prop_6_4_variational_opt`, `prop_6_4_decoupling_combine` | `KrylovChaos/GlauberDecoupling.lean` | Yes (1) |
| Lemma 7.1, Lemma 7.3 & Thm. 1.3(a)–(c) (Depolarized 2-design frame, reverse Poincaré, `54`/`216` constants, MSS bound) | `lemma_7_1_herm_trace_avg`, `lemma_7_1_conditioning`, `lemma_7_1_dual_reconstruction`, `lemma_7_1_dual_real_of_herm`, `lemma_7_1_dual_eigenvalues`, `lemma_7_3_subset_union_bound`, `lemma_7_3_product_filtration_identity`, `theorem_1_3a_reverse_poincare`, `theorem_1_3b_constants`, `theorem_1_3c_mss_lyapunov_bound` | `KrylovChaos/DepolarizedFrame.lean` | Yes (3) |
| Lemmas A.1–A.3, 7.2 & 6.3 (Polymer trees & Kotecký–Preiss verification) | `lemma_A_1_plane_tree_polymer_sum`, `lemma_A_2_cayley_root_reversal`, `lemma_A_3_unordered_tree_induction`, `lemma_7_2_kp_verification`, `lemma_6_3_kp_pinning_verification` | `KrylovChaos/PolymerTrees.lean` | — |
| Prop. 8.1, Lemma 8.2 & Prop. 8.3 (1D commutator bound, Hubbard–Stratonovich & product-Bernoulli reverse Poincaré) | `prop_8_1_one_dim_commutator_bound`, `cosh_two_hsPhi`, `lemma_8_2_hubbard_stratonovich_identity`, `lemma_8_2_phi_bound`, `prop_8_3_product_bernoulli_reverse_poincare` | `KrylovChaos/ClassicalIsing.lean` | Yes (2) |
| Prop. 9.1 & Lemma B.1 (Structural necessity, bimodal exact size, double-well tunneling & Neumann tail) | `prop_9_1_gaussian_kernel_bound`, `prop_9_1_no_linear_lower_bound`, `prop_9_1_bimodal_exact_size`, `lemma_B_1_neumann_tail_sum`, `prop_9_1_double_well_tunneling_limit` | `KrylovChaos/StructuralNecessity.lean` | Yes (2) |
| Non-vacuity witnesses & numerical sanity checks | `sanity_invLocalityScale_r2`, `sanity_theorem_1_1a_static_zero`, `sanity_lemma_7_1_frame`, `sanity_theorem_1_3b_r2`, `sanity_lemma_8_2_ising`, `sanity_prop_9_1_bimodal_N2`, `sanity_lemma_B_1_d1_EB4` | `KrylovChaos/SanityChecks.lean` | — |

## Scope and Honest Boundaries

- **Proved unconditionally in Lean 4 (Mathlib-only)**: All finite-volume algebraic, spectral, ODE/MGF, filtration, product-state, Dyck-path, 2-design frame, polymer-tree, Hubbard–Stratonovich, reverse-Poincaré, asymptotic rate-comparison, and structural-necessity theorems listed above, with zero custom axioms and zero `sorry`s.
- **External infinite-volume / functional-analytic results cited from the literature (not internalized as custom axioms)**: Carleman's essential self-adjointness criterion for infinite tridiagonal Jacobi operators, Montel/Vitali normal-family convergence for infinite-volume complex-time OTOCs, Araki's 1D complex-time analyticity theorem, and the abstract infinite-volume Kotecký–Preiss cluster-expansion convergence theorem. Where a manuscript theorem combines one of these external functional-analytic inputs with the manuscript's quantitative estimates, the Lean formalization proves the exact finite-volume / quantitative / asymptotic reduction theorem with explicit hypotheses rather than postulating custom axioms. See [`EXTERNAL-AXIOMS.md`](EXTERNAL-AXIOMS.md).

## Check It Yourself

```bash
lake exe cache get
lake build
lake env lean KrylovChaos/AuditAxioms.lean
lake comparator comparator.json
./scripts/verify.sh
```
