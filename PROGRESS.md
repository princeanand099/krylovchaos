# KrylovChaos Formalization Progress Log

## Milestone Summary (All Verified Green on `ci-logs`)
- **Milestones 1–4**: Initial scaffold, 11 core modules, `SanityChecks`, `AuditAxioms`, and `comparator/` locked challenge suite.
- **Milestone 5**: Ground-up Mathlib-only formalization of all 4 external literature pillars (`CarlemanJacobi`, `KoteckyPreiss`, `VitaliAnalytic`, `ArakiOneDim`) — zero external axioms, zero literature hypotheses.
- **Milestone 6** (`3f8b1748`, `ci-logs` `4d0a5a9e`, `3573 jobs`, `LAKE_BUILD_EXIT=0`): Added `QubitAlgebra`, `ManyBodySetup`, `OperatorBridges` (de-orphaned all modules, Corollary 6.5 Eq. 6.11, global 2-design frame, `limsup` rate bound, non-laundered `theorem_1_2c_otoc_dominance`).
- **Milestone 7** (`b819eece`, `ci-logs` `980c8fe9`, `3577 jobs`, `LAKE_BUILD_EXIT=0`): Added `MajoranaAlgebra` (Eq. 2.10), `ProductStateDerivation` (Wightman Gram–Schmidt & Eq. 4.6 derivation), `WightmanProjectors` (operator bounds $0 \preceq \mathcal{S} \preceq N\mathbf{1}$, operator Lemma 4.2 Eq. 4.3, `wightmanProj` Loewner dominance), `LanczosMoments` (exact Dyck-path moment expansion, summed Lemma 5.1, Gamma-integral Meixner `sech` bound Eq. 5.5).
- **Milestone 8** (`bce66907`, `ci-logs` `091b1bce`, `3579 jobs`, `LAKE_BUILD_EXIT=0`): Added `CausalNormBounds` (Banach-algebra Hadamard/BCH `exp_conj_eq_tsum_adPow`, causal-sequence expansion, Lemma 2.1 Eqs. 2.3–2.5) and `BimodalExact` (exact `QubitOp N` Proposition 9.1(2) Eq. 9.2).
- **Milestone 9** (`be553804`, `ci-logs` `0fa15650`, `3590 jobs`, `LAKE_BUILD_EXIT=0`): Added `SpectralMeasure` (finite-dimensional Wightman spectral measure, Eq. 5.1, Eq. 5.2, Cauchy–Hadamard rate comparison, end-to-end Theorem 1.2(b)) and `JacobiSemigroup` (`jacobiCLM`, unitary propagator `jacobiUnitary`, exact Lanczos ODE Eq. 2.7, ground-up weighted Fatou lemma, `theorem_1_1a_infinite_fatou_proved`).
- **Milestone 10** (`a010d7b7`, `ci-logs` `7c580ecc`, `3591 jobs`, `LAKE_BUILD_EXIT=0`): Added `EndToEndTheorems` (`QubitOpCLM N` with `NormOneClass`, concrete `qubitLocalInteractionDecomp` instantiating Lemma 2.1 Eqs. 2.4–2.5 in exact operator norm `‖·‖_∞` on `QubitOp N`, and `theorem_1_1b_end_to_end`).
- **Milestone 11** (`617b0c650662939ced1d1221a98d1c2c484d9fd1`, `ci-logs` `4b93efa94f5ae31f3d2742a9d04a97424d596c3b`, `3593 jobs`, `LAKE_BUILD_EXIT=0`): Resolved BOTH remaining infinite-dimensional frontiers completely on standard Mathlib `v4.35.0`:
  - **`InfiniteChainLimit.lean`**: Proved `complex_finite_chain_mgf_bound`, `jacobiWavefn_trunc_diff_bound`, exponential Cauchy convergence `jacobiWavefn_coord_cauchy`, pointwise convergence `infiniteKrylovWavefn_tendsto`, probability conservation $\sum_{m=0}^\infty |\varphi_m(t)|^2 = 1$, and unconditional infinite-chain Theorem 1.1(a) (`theorem_1_1a_infinite_unconditional`) with **zero `hlim` and zero `hfatou` hypotheses**.
  - **`ThermodynamicKMS.lean`**: Proved entire finite-volume KMS correlations `finiteKMS_entire`, exact KMS boundary identity `finiteKMS_boundary_identity` ($F_{A,B}(t + i\beta) = F_{B,A}(-t)$), Tychonoff / sequential weak-* compactness on the countable quasi-local Pauli basis `PauliWord := List (Fin 4)` (`thermo_limit_state_exists`), and thermodynamic-limit KMS boundary transfer (`thermo_limit_kms_boundary_transfer`).
  - Expanded `AuditAxioms.lean` to audit all **53 headline, operator-algebraic, infinite-chain & thermodynamic-limit theorems** across all **30 library modules**.

## Current Metrics
- **Total Library Modules**: 30 (0 orphans)
- **Custom Axioms**: 0
- **External Literature / `hlim` / `hfatou` Hypotheses**: 0
- **Library `sorry`s**: 0
- **Build Status**: `Build completed successfully (3593 jobs). LAKE_BUILD_EXIT=0`
