# Formalization Progress

- **Status**: Complete — all **69** library modules under `KrylovChaos/`, `KrylovChaos/AuditAxioms.lean` (**232** verified headline theorems), and **23** locked `comparator` theorems compile and pass with **zero `sorry`s** and **zero custom axioms**.
- **Toolchain**: `leanprover/lean4:v4.35.0` + Mathlib `v4.35.0` + `leanprover/comparator` `v4.35.0`.

## Section-by-Section Coverage Against `finite_temp_krylov_chaos.tex`

- **Sections 1–3 (Theorem 1.1(a), Lemma 2.1, Propositions 2.2–2.3, Lemma 3.1)**:
  - Concrete Gibbs states, `jBeta` bijectivity/`LinearEquiv`, Wightman Lanczos recursion Eq. (2.6) & ODE Eq. (2.7) with `(-i)^n` phase, Majorana `LocalInteractionDecomp`, Lemma 2.1(1)–(3), `isEvenParity H → isEvenParity ρQuarter` wired into Prop. 2.3(2) Eq. (2.10), infinite Krylov ODE satisfaction, Carleman $\ell^2$-uniqueness, single-exponential Fatou Eqs. (1.12)–(1.13), and `limsup` rate bound including `b 1 = 0`.
- **Section 4 (Proposition 4.1, Lemma 4.2, Proposition 4.3, Theorem 1.1(b))**:
  - Concrete qubit and Majorana Prop. 4.1(1)–(2) Eq. (4.2), Lemma 4.2 Eq. (4.3), concrete and family-level Theorem 1.1(b), and Prop. 4.3 `lambdaMSS` bound for arbitrary non-diagonal full-rank product states.
- **Section 5 (Theorem 1.2(a)–(c), Lemma 5.1)**:
  - Asymmetric Eq. (5.2)–(5.4) chain, measure-theoretic `wightmanSpectralMeasure`, `Integrable (cosh (r * ω))`, Eq. (1.15) & `r_W ≥ β/2 + κ`, Lanczos moment identity + Cauchy–Hadamard from strip integrability, concrete time-ordered correlator `T_{τ,N}(t)` dominance Eq. (1.17) (`TimeOrderedOTOC.lean`), and Montel + Vitali strip extension.
- **Sections 6–7 & Appendix A (Lemmas 6.1–6.3, 7.1–7.3, A.1–A.3, Propositions 6.2 & 6.4, Corollary 6.5, Theorem 1.3(a)–(c))**:
  - High-temperature parameter bridge (`HighTempParams.lean`) discharging Lemma 7.2 and Theorem 1.3(a)–(b) directly from `β ∈ [0, betaWC]`.
  - Shifted-commutator thermal size splitting `S_β(A) = I(A) + II(A) + III(A)` with `III(A) = Re Tr((ρ_A - ρ_β) ℬ_β)` (`ShiftedThermalSize.lean`).
  - Polymer partition function nonvanishing, ratio bounds, Cauchy order-2 Schwarz lemma, and combined-exponential trace cumulant bound Lemma 6.3 Eq. (6.3) (`HighTempPolymerZ.lean`, `HighTempCumulant.lean`).
  - Entropic background decoupling Prop. 6.4(2) Eq. (6.7) (`EntropicDecoupling.lean`) and concrete Eq. (1.24) + family-level Theorem 1.3(c) without assuming Hypothesis (H2) (`HighTempChaosBound.lean`).
  - All-time Duhamel Lieb–Robinson bound and lattice Corollary 6.5 Eq. (6.10) (`AllTimeLiebRobinson.lean`, `Cor65LatticeBound.lean`).
- **Section 8 (Propositions 8.1 & 8.3)**:
  - All-temperature 1D finite-range Araki complex-time bound via concentric shell causality and Proposition 8.1 Eq. (8.1) (`ArakiOneDimAllTemp.lean`).
  - Strict `i < j` Classical Ising Gibbs measure, multi-edge discrete Hubbard–Stratonovich Prop. 8.3 Eq. (8.4), and diagonal qubit $L^2$ bridge.
- **Section 9 & Appendix B (Proposition 9.1(1)–(3), Lemma B.1)**:
  - Gaussian time-smearing Bochner integral, fixed-`σ` OTOC Lyapunov preservation, bimodal $\Theta(N)$ size & direct (H2) violation for all `δ ∈ [0, 1)`, and `D × D` symmetric tridiagonal double-well matrix Sturm simplicity, parity, Rayleigh bounds, eigenvector decay Eqs. (B.2)–(B.3), and Prop. 9.1(3) Eq. (9.3) (`DoubleWellTunneling.lean`).
