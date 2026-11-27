# Formalization Progress

- **Status**: Complete — all **58** library modules under `KrylovChaos/`, `KrylovChaos/AuditAxioms.lean` (**193** audited headline theorems), and **23** locked `comparator` theorems verified with **zero `sorry`s**, **zero custom axioms**, and **zero hypothesis laundering**.
- **Toolchain**: `leanprover/lean4:v4.35.0` + Mathlib `v4.35.0` + `leanprover/comparator` `v4.35.0`.

## Verdict-A Remediation Summary (30-Item Gap & Remediation Checklist Against `finite_temp_krylov_chaos.tex`)

- **Milestone 1 — Sections 2–4 & Appendix A (Items #1–#11, #29)**:
  - `#1` Majorana `LocalInteractionDecomp` & Lemma 2.1(1)–(3) (`KrylovChaos/Milestone1Majorana.lean`).
  - `#2` Standalone `jBeta` bijectivity / `LinearEquiv` (`KrylovChaos/Milestone1CoreRemediation.lean`).
  - `#3` `isEvenParity H → isEvenParity ρQuarter` wired into Prop. 2.3(2) Eq. (2.10) (`KrylovChaos/Milestone1CoreRemediation.lean`).
  - `#4` Renamed misnamed Section 2 identity `lemma_6_1_concrete_operator` → `hsNormSq_siteSizeOp_jBeta_eq_comm_avg` (`KrylovChaos/OperatorGlauberAndLanczosFiltration.lean`).
  - `#5`–`#8` Infinite Krylov ODE satisfaction, genuine Carleman $\ell^2$-uniqueness without `hflux`, exact single-exponential Fatou Eqs. (1.12)–(1.13), and `limsup` rate bound including `b 1 = 0` (`KrylovChaos/Milestone1InfiniteChain.lean`).
  - `#9` Majorana filtration, `majoranaWightmanQ`, Prop. 4.1(1)–(2), Lemma 4.2, and concrete & family Thm. 1.1(b) (`KrylovChaos/Milestone1Majorana.lean`).
  - `#10` Family-level concrete qubit Thm. 1.1(b) (`λ_L ≤ 2 α`) (`KrylovChaos/Milestone1CoreRemediation.lean`).
  - `#11` Prop. 4.3 `lambdaMSS` bound for arbitrary non-diagonal full-rank product states (`KrylovChaos/Milestone1CoreRemediation.lean`).
  - `#29` Multi-type heterogeneous-locality Lemma A.3 (`KrylovChaos/Milestone1CoreRemediation.lean`).
- **Milestone 2 — Section 5 & Theorem 1.2(a)–(c) (Items #12–#15)**:
  - `#12` Spectral-weight-to-measure bridge, `Integrable (cosh (r * ω))`, Eq. (1.15), and `r_W ≥ β/2 + κ` (`KrylovChaos/Milestone2SpectralAndVitali.lean`).
  - `#13` Concrete Lanczos tridiagonalization moment identity + Cauchy–Hadamard from strip integrability → `2 liminf b_n / n ≤ π / r_W` (`KrylovChaos/Milestone2SpectralAndVitali.lean`).
  - `#14` Concrete `T_{τ,N}(t)`, time-translation invariance, `W ↔ V` swap symmetry, 3-way Eq. (1.17), and `otocStripHalfWidthMax` (`KrylovChaos/Milestone2SpectralAndVitali.lean`, `KrylovChaos/Milestone2AnalyticFoundations.lean`).
  - `#15` Genuine Montel + Vitali strip extension theorem (`KrylovChaos/Milestone2SpectralAndVitali.lean`).
- **Milestone 3 — Sections 6–8 & Theorem 1.3(a)–(c) (Items #16–#25)**:
  - `#16` Prop. 6.2 exact `3/2` prefactor & `X ∈ E` scoping (`KrylovChaos/Milestone3Sections678.lean`).
  - `#17` Two-type hypergraph polymer expansion + order-$k$ Schwarz Lemma 6.3 Eq. (6.3) (`KrylovChaos/Milestone3Sections678.lean`).
  - `#18` Genuine non-tautological `II(A)`, `B_β`, `III(A)` & Eq. (6.4) (`KrylovChaos/Milestone3Sections678.lean`).
  - `#19` Singular `ρ_O` & `D(ρ_O ‖ ρ_β) ≤ 2 ln ‖O(iβ/4)‖_∞` (`KrylovChaos/Milestone3Sections678.lean`).
  - `#20` `wightmanNormSq_le_opNorm_sq` + all-time lattice Cor. 6.5 (`KrylovChaos/Milestone3Sections678.lean`).
  - `#21` `betaWC_concrete` & Lemma 7.3(1) general subset `U` (`KrylovChaos/Milestone3Sections678.lean`).
  - `#22` Thm. 1.3(b) Eq. (1.22) without `hRP` with exact `54`/`216` prefactors (`KrylovChaos/Milestone3Sections678.lean`).
  - `#23` Family-level concrete Thm. 1.3(c) Eqs. (1.23)–(1.24) (`KrylovChaos/Milestone3Sections678.lean`).
  - `#24` All-temperature 1D Araki Prop. 8.1 with exact `3/2` prefactor & Eq. (8.1) (`KrylovChaos/Milestone3Sections678.lean`).
  - `#25` Strict `i < j` Classical Ising `μ_β`, `Φ_max(β)`, multi-edge discrete Hubbard–Stratonovich Prop. 8.3 Eq. (8.4) & diagonal qubit bridge (`KrylovChaos/Milestone3Sections678.lean`).
- **Milestone 4 — Section 9, Appendix B, Comparator, Audit & Docs (Items #26–#28, #30)**:
  - `#26` Gaussian time-smearing Bochner integral `W_σ`, unconditional `liminf b_n / n = 0` without `hstrip`, & OTOC preservation (`KrylovChaos/Milestone4Section9AppB.lean`).
  - `#27` Bimodal state wiring & (H2) violation for all `δ ∈ [0, 1)` (`KrylovChaos/Milestone4Section9AppB.lean`).
  - `#28` Genuine `doubleWellBlock` Lemma B.1 & 1-qubit 2D Krylov closure Prop. 9.1(3) Eq. (9.3) (`KrylovChaos/Milestone4Section9AppB.lean`).
  - `#30` Expanded `AuditAxioms.lean` (193 headline theorems), documentation sync (`README.md`, `EXTERNAL-AXIOMS.md`, `PROGRESS.md`, `PROOF-PATH.md`), and full CI verification (`lake build` + `#print axioms` + `lake comparator`).
