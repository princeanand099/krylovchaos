# Formalization Progress

- **Status**: Complete — all **82** library modules under `KrylovChaos/` (including **13** concrete non-vacuity checks in `KrylovChaos/SanityChecks.lean`), `KrylovChaos/AuditAxioms.lean` (**296** verified headline theorems), and **33** locked `comparator` theorems compile and pass with **zero `sorry`s** and **zero custom axioms**.
- **Toolchain**: `leanprover/lean4:v4.35.0` + Mathlib `v4.35.0` + `leanprover/comparator` `v4.35.0`.

## Section-by-Section Coverage Against `finite_temp_krylov_chaos.tex`

- **Sections 1–3 (Theorem 1.1(a), Lemma 2.1, Propositions 2.2–2.3, Lemma 3.1)**:
  - Concrete Gibbs states, `jBeta` bijectivity/`LinearEquiv`, Wightman Lanczos recursion Eq. (2.6) & ODE Eq. (2.7) with `(-i)^n` phase, Majorana `LocalInteractionDecomp`, Lemma 2.1(1)–(3), `isEvenParity H → isEvenParity ρQuarter` wired into Prop. 2.3(2) Eq. (2.10), unconditional infinite Krylov ODE satisfaction, Carleman $\ell^2$-uniqueness, single-exponential Fatou Eqs. (1.12)–(1.13), and `limsup` rate bound (`InfiniteChainUnconditional.lean`).
- **Section 4 (Proposition 4.1, Lemma 4.2, Proposition 4.3, Theorem 1.1(b))**:
  - Concrete qubit and Majorana Prop. 4.1(1)–(2) Eq. (4.2), Lemma 4.2 Eq. (4.3), concrete and family-level Theorem 1.1(b), and Prop. 4.3 `lambdaMSS` bound for arbitrary non-diagonal full-rank product states.
- **Section 5 (Theorem 1.2(a)–(c), Lemma 5.1)**:
  - Concrete `QubitOp N` spectral measure `concreteWightmanSpectralMeasure`, `Integrable (cosh ((β/2 + κ') * ω))`, Eq. (1.15) & `β/2 + κ ≤ holoStripHalfWidth μ` (`ConcreteSpectralStrip.lean`), differentiation under the integral sign & unconditional `EReal`/finite-`r_W` Theorem 1.2(b) Eq. (1.16) (`MainTheoremPackaging.lean`, `MeixnerMomentIdentity.lean`), concrete time-ordered correlator `T_{τ,N}(t)` dominance Eq. (1.17), and thermodynamic-limit three-way `liminf` & `S_OTOC = (1/2) max(r_W, r_V)` strip analyticity (`TimeOrderedOTOC.lean`, `ConcreteOTOCStrip.lean`, `MainTheoremPackaging.lean`).
- **Sections 6–7 & Appendix A (Lemmas 6.1–6.3, 7.1–7.3, A.1–A.3, Propositions 6.2 & 6.4, Corollary 6.5, Theorem 1.3(a)–(c))**:
  - High-temperature parameter bridge (`HighTempParams.lean`: `lemma_7_2_high_temp`, `lemma_7_2_high_temp_normalized`), sharp `3/2` Prop. 6.2 (`HighTempSharpBounds.lean`), exact two-sided Theorem 1.3(a) Eq. (1.20) (`MainTheoremPackaging.lean`), Theorem 1.3(b), shifted-commutator splitting `S_β(A) = I(A) + II(A) + III(A)` (`ShiftedThermalSize.lean`), polymer partition function & combined-exponential Lemma 6.3 (`HighTempPolymerZ.lean`, `HighTempCumulant.lean`), entropic decoupling Prop. 6.4(2) Eq. (6.7) (`EntropicDecoupling.lean`), concrete Eq. (1.24) + family-level Theorem 1.3(c) (`HighTempChaosBound.lean`, `HighTempChaosFull.lean`, `ConcreteSpectralStrip.lean`), and all-time Duhamel Lieb–Robinson & lattice Corollary 6.5 Eq. (6.10) (`AllTimeLiebRobinson.lean`, `Cor65LatticeBound.lean`).
- **Section 8 (Propositions 8.1 & 8.3)**:
  - All-temperature 1D finite-range Araki complex-time bound and independent `(r, R)` Proposition 8.1 Eq. (8.1) (`ArakiOneDimAllTemp.lean`, `MainTheoremPackaging.lean`).
  - Strict `i < j` Classical Ising Gibbs measure with active-edge vertex degree `Δ = max_i #{j : J_{ij} ≠ 0}`, sharp `cosh²(β H_max + (Δ/2) ln 2)` Eq. (8.4) bound (`MainTheoremPackaging.lean`), `N = 4, Δ = 2` non-vacuity check (`SanityChecks.lean`), and diagonal qubit $L^2$ bridge.
- **Section 9 & Appendix B (Proposition 9.1(1)–(3), Lemma B.1)**:
  - Concrete 2D Gaussian OTOC convolution & Bochner-to-spectral-measure bridge (`GaussianSmearingBridge.lean`), full-rank bimodal Eq. (9.1) witness violating (H2) (`BimodalFullRank.lean`), and `D × D` double-well Sturm simplicity, parity, Courant–Fischer bulk eigenvalue localization (`Section9EndToEnd.lean`), 2D Lanczos closure, and end-to-end Prop. 9.1(3) Eq. (9.3) (`DoubleWellKrylovLimit.lean`).
