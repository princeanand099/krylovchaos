# External Axioms, Kernel Soundness & Scope Audit

## 1. Custom Axiom & `sorry` Audit
- **Custom axioms in `KrylovChaos/`**: **0** (`#print axioms` verified via `KrylovChaos/AuditAxioms.lean` to depend exclusively on Lean 4's three standard axioms `propext`, `Classical.choice`, and `Quot.sound`).
- **`sorry` / `admit` in `KrylovChaos/`**: **0** across all 39 modules.
- **Standalone verification**: Strictly Mathlib `v4.35.0` (`leanprover/lean4:v4.35.0`), verified by `lake build` and `lake comparator`.

## 2. Concrete Operator-Level Formalization Coverage (Against `finite_temp_krylov_chaos.tex`)

### Fully Formalized on Concrete Mathematical Objects (Zero Scalar-Wrapper Hypotheses)
- **Section 1 & Section 3 (Theorem 1.1(a), Lemma 3.1)**:
  - Finite-chain and infinite-chain Krylov exponential tail bound Eq. (1.12) and Krylov complexity bound Eq. (1.13) (`KrylovTail.lean`, `JacobiSemigroup.lean`, `InfiniteChainLimit.lean`, `ConcreteEndToEndWiring.lean` including explicit `θ₀ = 4` constant `theorem_1_1a_infinite_exact_constant`).
- **Section 2 (Lemma 2.1, Propositions 2.2–2.3, Concrete Gibbs & Lanczos Infrastructure)**:
  - Concrete spectral functional calculus `hermFunc`, concrete Gibbs state `gibbsRho`, `gibbsRhoHalf`, `gibbsRhoQuarter`, `gibbsRhoQuarterInv`, `concreteGibbsData`, `localHamiltonianGibbs`, commutation `[H, ρ_β^{1/4}] = 0`, complex-time Heisenberg evolution `heisenbergEvol` + entrywise Heisenberg ODE, concrete Wightman Lanczos recursion Eq. (2.6) (`lanczosOp`, `lanczosCoeff`, `lanczos_three_term`, `concreteKrylovComplexity`), concrete filtration & Glauber superoperators `wightmanQ`, `quantumGlauberGen`, `otocI`, `otocCW`, `lambdaMSS` (`GibbsConstruction.lean`, `WightmanIsometry.lean`, `QubitAlgebra.lean`).
- **Section 4 (Proposition 4.1, Lemma 4.2, Proposition 4.3, Theorem 1.1(b) Operator Core)**:
  - Concrete commutator support growth `matComm_mem_filtration`, concrete Lanczos filtration containment `lanczosOp_mem_filtration` and `lanczosTrunc_mem_filtration` (`OperatorGlauberAndLanczosFiltration.lean`).
  - Concrete operator-level `prop_4_1_concrete_operator` (`Re (A | 𝒬^{(β)} A)_β^W ≤ s ‖A‖_{β,W}²`), `wightmanQ_le_N_normSq`, `wightmanQ_add_bound`, and `lemma_4_2_concrete_operator` on `QubitOp N` (`ConcreteEndToEndWiring.lean`), plus asymptotic static reduction `theorem_1_1b_static_reduction` (`Filtration.lean`).
  - Concrete multi-site `N`-qubit product-state bound `prop_4_3_concrete_product_state_bound` wired directly to `mssThermalSize` (`ProductStateMultiSite.lean`).
- **Section 5 (Theorem 1.2(a)–(c), Lemma 5.1)**:
  - Concrete operator-level strip-cosh identity Eq. (5.2) `theorem_1_2a_concrete_strip_cosh` and exponential spectral moment bound `theorem_1_2a_concrete_exp_moment` directly on `QubitOp N` (`Theorem12Concrete.lean`).
  - Binomial series convergence, Dyck-path lower bound `lemma_5_1_path_weight_lower`, Lanczos rate bound `theorem_1_2b_lanczos_rate_bound`, and spectral OTOC dominance `theorem_1_2c_otoc_dominance` (`SpectralDyck.lean`, `CausalNormBounds.lean`, `CarlemanJacobi.lean`, `VitaliAnalytic.lean`).
- **Section 6 (Lemma 6.1 & Gibbs–Donsker–Varadhan Variational Inequality Eq. 6.9)**:
  - Concrete operator-level HS commutator identity `hsNormSq_siteSizeOp_eq_comm_avg` & `lemma_6_1_concrete_operator` on `QubitOp N` (`OperatorGlauberAndLanczosFiltration.lean`).
  - Concrete quantum relative entropy `quantumRelEntropy`, Klein's inequality `quantumRelEntropy_nonneg`, Gibbs relative entropy `gibbsRelEntropy_nonneg`, and exact Gibbs–Donsker–Varadhan variational inequality Eq. (6.9) `gibbs_variational_bound` on `QubitOp N` (`OperatorGlauberAndLanczosFiltration.lean`).
- **Section 7 (Lemma 7.1, Lemma 7.3, Theorem 1.3(a), Theorem 1.3(b) Equal-Time `C_W` Bound)**:
  - Depolarized frame `depolP`, `depolPHalf`, `depolPHalfInv`, concrete operator-level conditioning `lemma_7_3_operator_conditioning`, concrete best-approximation `lemma_7_3_operator_best_approx` (`HighTempConditioning.lean`).
  - Concrete 4-step Gram–Schmidt product orthonormal basis `prodDepolBasis`, concrete operator-level product filtration identity `lemma_7_3_operator_filtration_identity`, full operator-level **Theorem 1.3(a)** `theorem_1_3a_concrete_operator` (`Re (A | 𝒬̃^{(β)} A)_β^W ≤ ∑_x ‖𝒮_x(A)‖_{β,W}² ≤ 9 Re (A | 𝒬^{(β)} A)_β^W`), and full operator-level **Theorem 1.3(b)** equal-time bound `theorem_1_3b_concrete_CW` (`otocCW G A ≤ 54 Re (A | 𝒬^{(β)} A)_β^W`) (`HighTempReversePoincare.lean`).
  - Abstract Kotecký–Preiss convergence theorem `kotecky_preiss_convergence` (`KoteckyPreiss.lean`).
- **Section 8.2 (Classical Ising & Convex-Mixture Reverse Poincaré, Proposition 8.3)**:
  - Concrete `SpinConfig N`, `prodBernoulli`, `p`-biased orthonormal Fourier basis `chiBasis`, concrete `glauberDirichlet` and `degreeFiltrationQ`, and full concrete convex-mixture Reverse Poincaré `prop_8_3_concrete_convex_mixture_reverse_poincare` (Eq. 8.4) (`ClassicalIsingConcrete.lean`).
- **Section 9 & Appendix B (Proposition 9.1(1)–(3), Lemma B.1)**:
  - Concrete Gaussian time-smearing `gaussianSmear`, exact spectral weight law `prop_9_1_part1_spectral_density` (Eq. 9.2), and sub-Gaussian moment bound `prop_9_1_part1_subgaussian_moments` (`SpectralSmearingAndDoubleWell.lean`).
  - Concrete bimodal counterexample (`BimodalExact.lean`).
  - Concrete `ℤ₂` double-well parity splitting `doubleWell_even_odd_eigenpairs`, concrete Schur complement eigenvalue reduction `schur_complement_eigen_eq`, and concrete barrier hopping / Neumann-series exponential tunneling suppression `lemma_B_1_barrier_neumann_tunneling` (`SpectralSmearingAndDoubleWell.lean`).
- **Appendix A (Concrete Combinatorial Tree & Causal-Sequence Bounds)**:
  - Self-contained Catalan recurrence bound `catalanRec_le_four_pow`, concrete binary-tree sum `lemma_A_1_concrete_bin_tree_sum` & `lemma_A_1_concrete_exp_bound`, concrete causal-sequence sum `lemma_A_2_concrete_causal_seq_sum`, and concrete unordered-tree sum `lemma_A_3_concrete_unordered_tree_sum` (`ConcreteCombinatorics.lean`).

## 3. Explicitly Documented Open Sub-Gaps (Not Hidden as Hypotheses)
In strict adherence to anti-hypothesis-laundering standards, the following deep analytic sub-steps from `finite_temp_krylov_chaos.tex` are **explicitly marked as open** rather than hidden behind scalar-wrapper hypotheses:
1. **Concrete Polymer Expansion of `exp(-β H / 2)` for Lemma 7.2**: While `KoteckyPreiss.kotecky_preiss_convergence` and `ConcreteCombinatorics.lemma_A_1_concrete_exp_bound` are proved from first principles, constructing the full non-commutative Dyson/polymer operator `Q_γ` (Eq. 7.7) directly from `LocalHamiltonian N r` and proving `ρ_{β/2} = ∑_s π̃(s) P̃_s` with `π̃(s) > 0` for `β ∈ [0, β_wc]` remains open. Consequently, `theorem_1_3a_concrete_operator` and `theorem_1_3b_concrete_CW` take the concrete operator identity `G.ρHalf = ∑_s π(s) P̃_s` (`π(s) ≥ 0`) as their explicit hypothesis.
2. **Imaginary-Time Shifted Commutator Bound `I(A) ≤ 216 (A | 𝒬^{(β)} A)_β^W` (Theorem 1.3(b) Part 2)**: Equal-time `C_W(A) ≤ 54 (A | 𝒬^{(β)} A)_β^W` is proved at the operator level (`theorem_1_3b_concrete_CW`), while the imaginary-time shifted causal expansion `σ_i^α(-iβ/4)` yielding `I(A) ≤ 216 (A | 𝒬^{(β)} A)_β^W` and full end-to-end derivation of Theorem 1.3(c) from a family `{H_N}` remain open.
3. **Trace Cumulant Expansion (Lemma 6.3), Shell Expansion of `ℬ_β` (Prop. 6.4(2)), and Lattice Lieb–Robinson (Cor. 6.5)**: Concrete `gibbs_variational_bound` (Eq. 6.9) and `lemma_6_1_concrete_operator` are proved on `QubitOp N`; the full trace cluster expansion of `τ(exp(-β H) exp(ζ X))` (Lemma 6.3), the shell norm bound `g_{ℬ_β^{(k)}}` (Prop. 6.4(2)), and geometric lattice Lieb–Robinson propagation (Cor. 6.5) remain open.
4. **Full 1D Araki Transfer-Operator Analyticity (Theorem 1.2(a) 1D) & 1D Infinite-Volume KMS Limit (Section 8.1)**: Concrete 1D boundary counting (`araki_1d_boundary_count`) and abstract Vitali/Carleman/KMS machinery (`ArakiOneDim.lean`, `VitaliAnalytic.lean`, `ThermodynamicKMS.lean`) are proved, while the full non-commutative Araki expansional `E_β(t)` and concrete 1D spin-chain Lieb–Robinson convergence remain open.
5. **Legacy Scalar Helper Lemmas**: Earlier modules (`DepolarizedFrame.lean`, `GlauberDecoupling.lean`, `PolymerTrees.lean`, `OperatorBridges.lean`) retain scalar algebraic helper lemmas; they are explicitly labeled as arithmetic/algebraic helpers and are not claimed to be operator-level proofs of the corresponding manuscript theorems.
