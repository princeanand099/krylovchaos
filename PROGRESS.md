# KrylovChaos Formalization Progress Log

## Milestone Summary (All Verified Green on `ci-logs`)
- **Milestones 1–4**: Initial scaffold, 11 core modules, `SanityChecks`, `AuditAxioms`, and `comparator/` locked challenge suite.
- **Milestone 5**: Ground-up Mathlib-only formalization of all 4 external literature pillars (`CarlemanJacobi`, `KoteckyPreiss`, `VitaliAnalytic`, `ArakiOneDim`) — zero external axioms, zero literature hypotheses.
- **Milestone 6** (`3f8b1748`, `ci-logs` `4d0a5a9e`, `3573 jobs`, `LAKE_BUILD_EXIT=0`): Added `QubitAlgebra`, `ManyBodySetup`, `OperatorBridges` (de-orphaned all modules, Corollary 6.5 Eq. 6.11, global 2-design frame, `limsup` rate bound, non-laundered `theorem_1_2c_otoc_dominance`).
- **Milestone 7** (`b819eece`, `ci-logs` `980c8fe9`, `3577 jobs`, `LAKE_BUILD_EXIT=0`): Added `MajoranaAlgebra` (Eq. 2.10), `ProductStateDerivation` (Wightman Gram–Schmidt & Eq. 4.6 derivation), `WightmanProjectors` (operator bounds $0 \preceq \mathcal{S} \preceq N\mathbf{1}$, operator Lemma 4.2 Eq. 4.3, `wightmanProj` Loewner dominance), `LanczosMoments` (exact Dyck-path moment expansion, summed Lemma 5.1, Gamma-integral Meixner `sech` bound Eq. 5.5).
- **Milestone 8** (`bce66907`, `ci-logs` `091b1bce`, `3579 jobs`, `LAKE_BUILD_EXIT=0`): Added `CausalNormBounds` (Banach-algebra Hadamard/BCH `exp_conj_eq_tsum_adPow`, causal-sequence expansion, Lemma 2.1 Eqs. 2.3–2.5) and `BimodalExact` (exact `QubitOp N` Proposition 9.1(2) Eq. 9.2).
- **Milestone 9** (`be553804`, `ci-logs` `0fa15650`, `3590 jobs`, `LAKE_BUILD_EXIT=0`): Added `SpectralMeasure` (finite-dimensional Wightman spectral measure, Eq. 5.1, Eq. 5.2, Cauchy–Hadamard rate comparison, end-to-end Theorem 1.2(b)) and `JacobiSemigroup` (`jacobiCLM`, unitary propagator `jacobiUnitary`, exact Lanczos ODE Eq. 2.7, ground-up weighted Fatou lemma, `theorem_1_1a_infinite_fatou_proved`).
- **Milestone 10** (`a010d7b7cb07e3eaf97667703478c19e51f0495f`, `ci-logs` `7c580eccad467921667fb2fae51912e63ff55a6e`, `3591 jobs`, `LAKE_BUILD_EXIT=0`): Added `EndToEndTheorems` (`QubitOpCLM N` with `NormOneClass`, concrete `qubitLocalInteractionDecomp` instantiating Lemma 2.1 Eqs. 2.4–2.5 in exact operator norm `‖·‖_∞` on `QubitOp N`, and `theorem_1_1b_end_to_end` invoking `lemma_4_2_operator_thermal_size_truncation` directly) and expanded `AuditAxioms.lean` to audit all 43 headline & operator-level theorems across all **28 library modules**.

## Current Metrics
- **Total Library Modules**: 28 (0 orphans)
- **Custom Axioms**: 0
- **Library `sorry`s**: 0
- **Build Status**: `Build completed successfully (3591 jobs). LAKE_BUILD_EXIT=0`
