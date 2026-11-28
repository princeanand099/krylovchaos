# Formalization Progress

- **Status**: Complete — all **80** library modules under `KrylovChaos/`, `KrylovChaos/AuditAxioms.lean` (**280** verified headline theorems), `KrylovChaos/SanityChecks.lean` (**12** concrete small-system non-vacuity checks), and **23** locked `comparator` theorems compile and pass with **zero `sorry`s** and **zero custom axioms**.
- **Toolchain**: `leanprover/lean4:v4.35.0` + Mathlib `v4.35.0` + `leanprover/comparator` `v4.35.0`.

## Section-by-Section Coverage Against `finite_temp_krylov_chaos.tex`

- **Sections 1–3 (Theorem 1.1(a), Lemma 2.1, Propositions 2.2–2.3, Lemma 3.1)**:
  - Concrete Gibbs states, `jBeta` bijectivity/`LinearEquiv`, Wightman Lanczos recursion Eq. (2.6) & ODE Eq. (2.7) with `(-i)^n` phase, qubit and Majorana `LocalInteractionDecomp` & Lemma 2.1(1)–(3), `isEvenParity H → isEvenParity ρQuarter` wired into Prop. 2.3(2) Eq. (2.10), and unconditional infinite-chain Theorem 1.1(a) (`InfiniteChainUnconditional.lean`: all-time convergence, ODE satisfaction, Carleman $\ell^2$-uniqueness, exact Eqs. (1.12)–(1.13), and `limsup ≤ 2 α`).
- **Section 4 (Proposition 4.1, Lemma 4.2, Proposition 4.3, Theorem 1.1(b))**:
  - Concrete qubit and Majorana Prop. 4.1(1)–(2) Eq. (4.2), Lemma 4.2 Eq. (4.3), family-level bounded-`s` qubit and `2n`-normalized Majorana Theorem 1.1(b) (`HighTempSharpBounds.lean`), and Prop. 4.3 `lambdaMSS` bound for arbitrary non-diagonal full-rank product states.
- **Section 5 (Theorem 1.2(a)–(c), Lemma 5.1)**:
  - Concrete `QubitOp N` spectral measure `cosh` bound and holomorphic strip half-width `r_W ≥ β/2 + κ` (`ConcreteSpectralStrip.lean`), exact Meixner/sech moment identity and Lemma 5.1 Eq. (5.5) (`MeixnerMomentIdentity.lean`), concrete Lanczos moment bridge and Cauchy–Hadamard rate bound from `holoStripHalfWidth`, concrete time-ordered correlator `T_{τ,N}(t)` dominance Eq. (1.17) (`TimeOrderedOTOC.lean`), and thermodynamic-limit OTOC strip analyticity via Vitali–Montel (`ConcreteOTOCStrip.lean`).
- **Sections 6–7 & Appendix A (Lemmas 6.1–6.3, 7.1–7.3, A.1–A.3, Propositions 6.2 & 6.4, Corollary 6.5, Theorem 1.3(a)–(c))**:
  - High-temperature parameter bridge (`HighTempParams.lean`) discharging Lemma 7.2, multi-site Lemma 7.3(1) Eq. (7.11), two-sided Theorem 1.3(a), and Theorem 1.3(b) directly from `β ∈ [0, betaWC]`.
  - Sharp Proposition 6.2 prefactor `(3/2)(1 - β/(4κ))⁻²` (`HighTempSharpBounds.lean`), shifted-commutator splitting `S_β = I + II + III` (`ShiftedThermalSize.lean`), Kotecký–Preiss polymer partition function & Cauchy order-2 Schwarz Lemma 6.3 Eq. (6.3) (`HighTempPolymerZ.lean`, `HighTempCumulant.lean`), entropic background decoupling Prop. 6.4(2) Eq. (6.7) (`EntropicDecoupling.lean`, `HighTempSharpBounds.lean`), all-time Duhamel Lieb–Robinson & lattice Cor. 6.5 Eq. (6.10) (`AllTimeLiebRobinson.lean`, `Cor65LatticeBound.lean`), and concrete Eq. (1.24) + end-to-end family-level Theorem 1.3(c) (`HighTempChaosBound.lean`, `ConcreteOTOCStrip.lean`).
- **Section 8 (Propositions 8.1 & 8.3)**:
  - Complete all-temperature 1D finite-range Araki complex-time and Glauber bounds (`ArakiOneDimAllTemp.lean`, `HighTempSharpBounds.lean`).
  - Strict `i < j` Classical Ising Gibbs measure, multi-edge discrete Hubbard–Stratonovich mixture Lemma 8.2, explicit `2^Δ exp(2 β H_max)` Prop. 8.3 Eq. (8.4), and quantum diagonal-Ising `Q̃ = D` / `𝒬 = L_G` operator reverse Poincaré equivalence (`ClassicalIsingConcrete.lean`, `HighTempSharpBounds.lean`).
- **Section 9 & Appendix B (Proposition 9.1(1)–(3), Lemma B.1)**:
  - Concrete 2D Gaussian-smeared `concreteOTOC` Bochner convolution & geometric-mean `√n` bound, exact Eq. (9.1) qubit-1-conditioned bimodal state & `A = √2 |1⟩⟨1|_1` violation of (H2), `D × D` double-well Lanczos basis `{|K₀⟩, |K₁⟩}` tridiagonal closure & `K(t) = sin²(Δ t / 2)`, Courant–Fischer bulk eigenvalue localization, eigenvector decay Eqs. (B.2)–(B.3), and Prop. 9.1(3) Eq. (9.3) (`DoubleWellTunneling.lean`, `Section9EndToEnd.lean`).
