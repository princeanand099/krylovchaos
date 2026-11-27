# Formalization Progress

- **Status**: Complete — all **52** library modules under `KrylovChaos/`, `KrylovChaos/AuditAxioms.lean` (**142** audited headline theorems), and **23** locked `comparator` theorems verified with **zero `sorry`s**, **zero custom axioms**, and **zero hypothesis laundering**.
- **Toolchain**: `leanprover/lean4:v4.35.0` + Mathlib `v4.35.0` + `leanprover/comparator` `v4.35.0`.

## Remediation Summary (31-Item Checklist Against `finite_temp_krylov_chaos.tex`)

- **Part A (Items #1–#8)**:
  - `#1` Majorana fermion parity, string basis, parity-aware size operator, and Prop. 2.3(2) Eq. (2.10) (`KrylovChaos/MajoranaAlgebra.lean`).
  - `#2` Exact `(-i)^n` phase in `concreteKrylovWavefn`, real-valuedness, normalization, initial condition, and ODE Eq. (2.7) (`KrylovChaos/GibbsConstruction.lean`, `KrylovChaos/ConcreteEndToEndWiring.lean`).
  - `#3` Concrete Prop. 4.1(2) Eq. (4.2) on `QubitOp N` (`KrylovChaos/ConcreteEndToEndWiring.lean`).
  - `#4` Concrete Lemma 4.2 Eq. (4.3) on `mssThermalSize`/`lambdaMSS` (`KrylovChaos/ConcreteEndToEndWiring.lean`).
  - `#5` Operator-level Lemma 6.1 & Prop. 6.2 on `QubitOp N` (`KrylovChaos/Theorem12Concrete.lean`).
  - `#6` Exact asymmetric shift Eqs. (5.2)–(5.4) (`KrylovChaos/Theorem12Concrete.lean`).
  - `#7` Euler-secant Meixner $\eta = 1$ `sech` pole obstruction & zero-laundering `Filter.liminf` Thm. 1.2(b) (`KrylovChaos/SpectralMeasure.lean`).
  - `#8` Concrete 1D finite-range Prop. 8.1 wired into Lemma 6.1 (`KrylovChaos/Milestone3Bridges.lean`).
- **Part B (Items #9–#23)**:
  - `#9` Prop. 2.2(3) Lanczos invariance under `jBeta` (`KrylovChaos/ConcreteEndToEndWiring.lean`).
  - `#10` Prop. 2.3(1) qubit Eq. (2.9) (`KrylovChaos/ManyBodySetup.lean`).
  - `#11` Unconditional `limsup` rate bound & infinite Krylov ODE $\ell^2$-uniqueness (`KrylovChaos/Milestone2AnalyticFoundations.lean`).
  - `#12` Concrete end-to-end qubit Thm. 1.1(a)–(b) (`KrylovChaos/Theorem11bConcrete.lean`).
  - `#13` Full Prop. 4.3 `lambdaMSS` bound & `N`-qubit local unitary invariance (`KrylovChaos/ProductStateLambdaMSS.lean`).
  - `#14` Measure-theoretic `wightmanSpectralMeasure : Measure ℝ`, weak-limit Fatou & strip holomorphy (`KrylovChaos/Milestone2AnalyticFoundations.lean`).
  - `#15` Concrete `concreteOTOC`, Eq. (1.17)–(1.18) dominance & locally-uniform-limit holomorphy (`KrylovChaos/Milestone2AnalyticFoundations.lean`).
  - `#16` Lemma 6.3 / A.3 trace polymer KP (`KrylovChaos/ClusterCumulantAndDecoupling.lean`, `KrylovChaos/ConcreteCombinatorics.lean`).
  - `#17` Prop. 6.4(1)–(2) `S_β = I + II + III` & entropic decoupling (`KrylovChaos/Milestone3Bridges.lean`, `KrylovChaos/ClusterCumulantAndDecoupling.lean`).
  - `#18` Cor. 6.5 $\mathbb{Z}^d$ causal ball volume & Lieb–Robinson (`KrylovChaos/Milestone3Bridges.lean`, `KrylovChaos/ClusterCumulantAndDecoupling.lean`).
  - `#19` Thm. 1.3(b) Eq. (1.22) & Thm. 1.3(c) (`KrylovChaos/Milestone3Bridges.lean`, `KrylovChaos/ShiftedCommutatorAndThm13c.lean`).
  - `#20` Sec. 8.2 Classical Ising Hamiltonian & diagonal-to-$L^2$ equivalence (`KrylovChaos/Milestone3Bridges.lean`, `KrylovChaos/ClassicalIsingConcrete.lean`).
  - `#21`–`#23` Prop. 9.1(1)–(3) & Lemma B.1 (`KrylovChaos/Milestone4StructuralNecessity.lean`, `KrylovChaos/SpectralSmearingAndDoubleWell.lean`, `KrylovChaos/BimodalExact.lean`).
- **Part C (Items #24–#31)**:
  - `#24`–`#28` Sharp `4^(m-1)` Catalan bound, Knuth `forestSum`, polymer-to-bintree bridge, causal expansion, normalized Lemma 7.2, `NormedSpace.exp` bridge, `supportedSubmodule` (`KrylovChaos/ConcreteCombinatorics.lean`, `KrylovChaos/CausalExpansion.lean`, `KrylovChaos/Lemma72Concrete.lean`, `KrylovChaos/EndToEndTheorems.lean`, `KrylovChaos/ManyBodySetup.lean`).
  - `#29`–`#31` `comparator` sync, 142-theorem `AuditAxioms.lean`, and documentation sync.
