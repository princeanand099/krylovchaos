# Proof Path and Module Dependency DAG

```
KrylovChaos.Basic
├── KrylovChaos.WightmanIsometry
│   ├── KrylovChaos.SpectralDyck
│   └── KrylovChaos.GlauberDecoupling
├── KrylovChaos.KrylovTail
├── KrylovChaos.Filtration
├── KrylovChaos.ProductState
│   └── KrylovChaos.DepolarizedFrame
├── KrylovChaos.PolymerTrees
├── KrylovChaos.ClassicalIsing
└── KrylovChaos.StructuralNecessity
        │
        ▼
KrylovChaos.SanityChecks
        │
        ▼
KrylovChaos (root aggregator)
├── KrylovChaos.AuditAxioms (standalone `#print axioms` gate)
└── comparator/Solution.lean (discharges all 19 locked theorems in comparator/Challenge.lean)
```

## Proof Flow by Manuscript Section

1. **Section 2 (`Basic`, `WightmanIsometry`)**: Defines `invLocalityScale` (`κ`), `betaWC` (`β_wc`), Wightman inner product & isometry, Liouvillian self-adjointness and zero diagonal, commutator/Majorana size identities, and causal commutator induction (`lemma_2_1_*`).
2. **Section 3 (`KrylovTail`)**: Establishes finite-chain unitarity, characteristic-curve MGF bound (`lemma_3_1_finite_chain_mgf`), finite-chain exponential tail & complexity bounds (`theorem_1_1a_finite_tail`, `theorem_1_1a_finite_complexity`), Fatou infinite-chain extension (`theorem_1_1a_infinite_tail_and_complexity`), and log-rate bound (`theorem_1_1a_log_rate_bound`).
3. **Section 4 (`Filtration`, `ProductState`)**: Proves Krylov locality filtration (`prop_4_1_krylov_filtration`), `Q`-complexity bound (`prop_4_1_q_complexity_bound`), thermal-size truncation (`lemma_4_2_thermal_size_truncation`), static reduction `λ_L ≤ 2 α` (`theorem_1_1b_static_reduction`), and product-state thermal-size static bound (`prop_4_3_product_state_static_bound`).
4. **Section 5 (`SpectralDyck`)**: Proves bilateral Laplace shift (`theorem_1_2a_laplace_identity`), even-measure exponential moment dominance (`theorem_1_2a_even_exp_moment`), binomial series convergence (`theorem_1_2a_binomial_series_summable`), Dyck-path shifting & weight monotonicity (`lemma_5_1_path_weight_lower`), smoothness-free Lanczos rate bound (`theorem_1_2b_lanczos_rate_bound`, `theorem_1_2b_rate_chain`), and finite-volume OTOC dominance (`theorem_1_2c_otoc_dominance`).
5. **Section 6 (`GlauberDecoupling`, `PolymerTrees`)**: Proves single-site commutator & high-temperature Glauber bounds (`lemma_6_1_single_site_commutator`, `prop_6_2_high_temp_glauber`), commutator splitting, variational optimization, decoupling combination (`prop_6_4_*`), and Kotecký–Preiss pinning verification (`lemma_6_3_kp_pinning_verification`).
6. **Section 7 & Appendix A (`DepolarizedFrame`, `PolymerTrees`)**: Constructs the explicit 6-element depolarized 2-design frame (`depolP`, `depolF`), proves Hermiticity, trace, uniform conditioning `(1/4) I ⪯ P̃_s ⪯ (3/4) I`, exact dual reconstruction, minimal polynomial `(X - 7/2)(X + 5/2) = 0`, product-space union & filtration identities (`lemma_7_3_*`), plane/Cayley/unordered tree polymer bounds (`lemma_A_1`–`A_3`, `lemma_7_2_kp_verification`), global reverse Poincaré (`theorem_1_3a_reverse_poincare`), explicit `54`/`216` constants (`theorem_1_3b_constants`), and high-temperature MSS Lyapunov bound (`theorem_1_3c_mss_lyapunov_bound`).
7. **Section 8 (`ClassicalIsing`)**: Proves 1D commutator bound (`prop_8_1_one_dim_commutator_bound`), discrete Hubbard–Stratonovich identity & coupling bound (`lemma_8_2_*`), and product-Bernoulli reverse Poincaré (`prop_8_3_product_bernoulli_reverse_poincare`).
8. **Section 9 & Appendix B (`StructuralNecessity`)**: Proves Gaussian kernel obstruction (`prop_9_1_gaussian_kernel_bound`, `prop_9_1_no_linear_lower_bound`), bimodal exact background size (`prop_9_1_bimodal_exact_size`), Neumann tail sum (`lemma_B_1_neumann_tail_sum`), and double-well tunneling limit (`prop_9_1_double_well_tunneling_limit`).
