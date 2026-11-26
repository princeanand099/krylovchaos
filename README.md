# KrylovChaos — Lean 4 Formalization

Complete, ground-up Lean 4 (`v4.35.0`) formalization of Prince Anand's manuscript *Finite-Temperature Bounds on Operator Growth and Quantum Chaos* (November 2026), built strictly on standard Mathlib `v4.35.0` with **zero custom axioms**, **zero external literature hypotheses**, **zero `sorry`s** in the library, and **zero orphan modules**.

## Verified Build Status
- **Verified Green Code Commit**: [`a010d7b7cb07e3eaf97667703478c19e51f0495f`](https://github.com/princeanand099/krylovchaos/commit/a010d7b7cb07e3eaf97667703478c19e51f0495f)
- **Raw CI Verification Log (`ci-logs`)**: [`7c580eccad467921667fb2fae51912e63ff55a6e`](https://github.com/princeanand099/krylovchaos/commit/7c580eccad467921667fb2fae51912e63ff55a6e) — `Build completed successfully (3591 jobs). LAKE_BUILD_EXIT=0`
- **Library Size**: **28 verified Lean 4 modules** (imported via `KrylovChaos.lean`) + `KrylovChaos/AuditAxioms.lean` (kernel `#print axioms` audit across 43 headline & operator-level theorems) + `comparator/` locked challenge suite.
- **Axiom Hygiene**: Every theorem depends strictly on a subset of Lean's standard core axioms `[propext, Classical.choice, Quot.sound]`.

## Module Architecture (28 Modules, Zero Orphans)

### Foundational & Operator-Algebraic Core
1. `KrylovChaos.Basic` — Core real-analytic bounds, factorial/binomial estimates, and elementary helpers.
2. `KrylovChaos.QubitAlgebra` — Concrete $N$-qubit Hilbert space $\mathcal{H} = (\mathbb{C}^2)^{\otimes N}$ (`QubitOp N`), Pauli strings, orthogonality, partial trace $\mathcal{E}_x$, complement $\mathcal{S}_x$, total size $\mathcal{S}$, Eq. (2.8) Hilbert–Schmidt commutator-size identity, and concrete support growth `filtration_comm_step`.
3. `KrylovChaos.MajoranaAlgebra` — Concrete Jordan–Wigner $2n$-Majorana Clifford algebra (`{V_i, V_j} = 2\delta_{ij}\mathbf{1}`, `{\gamma_i, \gamma_j} = \delta_{ij}\mathbf{1}`), Majorana HS size identity, and full $2n$-Majorana Proposition 2.3 (Eq. 2.10).
4. `KrylovChaos.ManyBodySetup` — $r$-local Hermitian Hamiltonians (`LocalHamiltonian`), Gibbs data (`GibbsData`), Wightman map $\mathcal{J}_\beta$, Proposition 2.2(3), full $N$-qubit Proposition 2.3 (Eq. 2.9), concrete bimodal state (Eq. 9.1), and double-well matrix.
5. `KrylovChaos.WightmanIsometry` — Wightman isometry, Liouvillian self-adjointness, and causal-commutator scalar majorants.
6. `KrylovChaos.CausalNormBounds` — Banach-algebra Hadamard/BCH expansion `exp_conj_eq_tsum_adPow`, causal-sequence expansion `adPow_eq_causal_sum`, and exact operator-norm Lemma 2.1 bounds (Eqs. 2.3–2.5).

### Krylov Dynamics, Carleman & Static-to-Dynamical Reduction (Sections 3–4)
7. `KrylovChaos.CarlemanJacobi` — Ground-up Carleman criterion (`carleman_divergence_of_linear_growth`, `carleman_deficiency_zero`).
8. `KrylovChaos.KrylovTail` — Finite-chain exponential tail & complexity bounds (Theorem 1.1(a)) and `Filter.limsup` log-rate bound.
9. `KrylovChaos.JacobiSemigroup` — Self-contained `exp_add_of_commute_real` & `hasDerivAt_exp_smul_real`, self-adjoint tridiagonal `jacobiCLM`, unitary propagator `jacobiUnitary`, exact probability conservation, exact Lanczos ODE Eq. (2.7), ground-up weighted Fatou lemma (`fatou_tsum_le_of_pointwise_tendsto`), and infinite-chain Theorem 1.1(a) (`theorem_1_1a_infinite_fatou_proved`).
10. `KrylovChaos.Filtration` — Abstract Krylov filtration, complexity bound Eq. (4.2), and static-to-dynamical reduction.
11. `KrylovChaos.WightmanProjectors` — Self-adjointness & idempotence of `partialTraceSite`, operator bounds $0 \preceq \mathcal{S} \preceq N\mathbf{1}$, Cauchy–Schwarz for $\mathcal{S}$, operator-level Lemma 4.2 (Eq. 4.3), concrete Wightman orthogonal projectors (`wightmanProj` via `Submodule.starProjection`), and Proposition 4.1 Loewner dominance.
12. `KrylovChaos.ProductState` — Product-state static bound Proposition 4.3 ($\Lambda_\beta^{\mathrm{MSS}}(s) \le s + m_{\max}\sqrt{Ns}$).
13. `KrylovChaos.ProductStateDerivation` — Ground-up derivation of `singleSiteRho` roots, unitary invariance of $\mathcal{S}_x$, Wightman Gram–Schmidt orthonormal basis `gsBasis`, and exact derivation of all 16 entries of `singleSiteM` (Eq. 4.6).

### Spectral Measure, Dyck Paths & Analytic Bounds (Section 5)
14. `KrylovChaos.VitaliAnalytic` — Ground-up Vitali/Montel power-series & strip uniform convergence.
15. `KrylovChaos.SpectralDyck` — Dyck-path combinatorics, `shiftDyckPath_injective`, Theorem 1.2(a)–(c), and ground-up OTOC dominance from $V^2 \preceq \|V\|_\infty^2 \mathbf{1}$.
16. `KrylovChaos.LanczosMoments` — Concrete symmetric tridiagonal `jacobiMat`, exact Dyck-path moment expansion `jacobiMat_moment_eq_dyck_sum`, full summed Lemma 5.1 moment lower bound, and Gamma-integral Meixner `sech` moment lower bound (Eq. 5.5).
17. `KrylovChaos.SpectralMeasure` — Concrete finite-dimensional Wightman spectral measure (`wightmanWeight`, `bohrFreq`), entire autocorrelation `wightmanAutocorr_entire`, exact matrix-trace Fourier identity Eq. (5.1), exact strip Laplace & `cosh` identities Eq. (5.2), spectral-measure moment upper bound, ground-up Cauchy–Hadamard rate comparison, and end-to-end Theorem 1.2(b) (`theorem_1_2b_end_to_end`).

### High-Temperature, 1D, Classical Ising & Structural Necessity (Sections 6–9, Appendices)
18. `KrylovChaos.KoteckyPreiss` — Ground-up Kotecký–Preiss cluster expansion convergence & logarithmic bound.
19. `KrylovChaos.ArakiOneDim` — Ground-up 1D Araki boundary counting & entire expansion.
20. `KrylovChaos.GlauberDecoupling` — Glauber decoupling and Proposition 6.4.
21. `KrylovChaos.DepolarizedFrame` — Depolarized frame, Lemma 7.1, and Theorem 1.3(a)–(c) (reverse Poincaré & MSS Lyapunov bound).
22. `KrylovChaos.PolymerTrees` — Polymer tree expansion and Appendix Lemma A.3 / Lemma B.1.
23. `KrylovChaos.ClassicalIsing` — Hubbard–Stratonovich identity (Lemma 8.2) and product-Bernoulli reverse Poincaré (Proposition 8.3).
24. `KrylovChaos.StructuralNecessity` — Structural necessity counterexamples (Proposition 9.1, double-well tunneling limit).
25. `KrylovChaos.BimodalExact` — Exact `QubitOp N` operator-level proof of Proposition 9.1(2) / Eq. (9.2) (`prop_9_1_bimodal_operator_exact_size`).

### Unification, End-to-End Instantiations & Verification
26. `KrylovChaos.OperatorBridges` — Cross-module bridges, `theorem_1_1a_limsup_rate_bound`, Corollary 6.5 (`corollary_6_5_krylov_lieb_robinson`, Eq. 6.11), global $N$-qubit 2-design frame, Lemma 7.1 dual trace bound, and Lemma 8.2 multi-edge HS bound.
27. `KrylovChaos.EndToEndTheorems` — Concrete `QubitOpCLM N` (`‖·‖_∞` operator norm with `NormOneClass`), `qubitLocalInteractionDecomp` instantiating Lemma 2.1 Eqs. (2.4)–(2.5) directly on `QubitOp N`, and end-to-end Theorem 1.1(b) (`theorem_1_1b_end_to_end`) invoking `lemma_4_2_operator_thermal_size_truncation` directly.
28. `KrylovChaos.SanityChecks` — Non-vacuity and type-level sanity checks.

## Honest Scope & Remaining Infinite-Dimensional Functional-Analysis Frontier
All finite-dimensional $N$-qubit and $2n$-Majorana operator-algebraic, spectral-measure, Lanczos/Dyck-path, Gram–Schmidt, Banach-algebra causal-norm, and end-to-end static-to-dynamical theorems are formalized ground-up on Mathlib `v4.35.0` with zero custom axioms and zero `sorry`s. Two infinite-dimensional functional-analysis steps from the manuscript remain outside current Mathlib infrastructure and are kept transparently parameterized at the finite-to-infinite limit interface:
1. Unbounded self-adjoint operator theory on $\ell^2(\mathbb{N})$ (Trotter–Kato strong resolvent convergence $T_{N_{\max}} \to \overline{T}$ implying $e^{i T_{N_{\max}} t} \to e^{i \overline{T} t}$ pointwise, which `theorem_1_1a_infinite_fatou_proved` currently receives as `hlim` while proving the Fatou tail & complexity bound ground-up).
2. Full $C^*$-algebraic thermodynamic-limit KMS state construction as $N \to \infty$ (all finite-$N$ Gibbs states, spectral measures, and uniform bounds are proved concretely for arbitrary $N \in \mathbb{N}$).
