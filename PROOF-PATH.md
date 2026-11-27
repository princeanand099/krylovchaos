# Proof Path & Module Architecture (`KrylovChaos`)

This repository formalizes *Finite-Temperature Bounds on Operator Growth and Quantum Chaos* (`finite_temp_krylov_chaos.tex`, Prince Anand, 2026) across **58** Lean 4 (`v4.35.0`) modules strictly on top of Mathlib `v4.35.0`.

## Dependency Layers

1. **Core Algebra & Parameters**: `Basic`, `QubitAlgebra`, `MajoranaAlgebra`, `WightmanIsometry`, `ManyBodySetup`, `GibbsConstruction`, `WightmanProjectors`, `EndToEndTheorems` (`NormedSpace.exp` bridge & `LocalInteractionDecomp`), `Milestone1CoreRemediation`, `Milestone1Majorana`.
2. **Section 3 & 4 — Krylov Tail, Filtration, Product States & Thm. 1.1(a)–(b)**: `KrylovTail`, `JacobiSemigroup`, `InfiniteChainLimit`, `CarlemanJacobi`, `Milestone1InfiniteChain`, `Filtration`, `OperatorGlauberAndLanczosFiltration`, `ConcreteEndToEndWiring`, `Theorem11bConcrete`, `ProductState`, `ProductStateDerivation`, `ProductStateMultiSite`, `ProductStateLambdaMSS`, `Milestone1CoreRemediation`, `Milestone1Majorana`.
3. **Section 5 — Spectral Decay, Dyck Paths, Meixner/Sech & OTOC Strip Analyticity (Thm. 1.2(a)–(c))**: `SpectralDyck`, `SpectralMeasure`, `CausalNormBounds`, `VitaliAnalytic`, `Theorem12Concrete`, `Milestone2AnalyticFoundations`, `Milestone2SpectralAndVitali`.
4. **Section 6, 7 & Appendix A — High-Temperature Cluster Expansions, Dual Frame & Reverse Poincaré (Thm. 1.3(a)–(c))**: `KoteckyPreiss`, `ConcreteCombinatorics`, `PolymerTrees`, `SupportAndDualFrame`, `PolymerExpansionConcrete`, `Lemma72Concrete`, `DepolarizedFrame`, `HighTempConditioning`, `HighTempReversePoincare`, `MultiSiteCommutator`, `CausalExpansion`, `GlauberDecoupling`, `ClusterCumulantAndDecoupling`, `ShiftedCommutatorAndThm13c`, `OperatorBridges`, `Milestone3Bridges`, `Milestone3Sections678`.
5. **Section 8 — 1D Araki Expansional & Classical Ising**: `ArakiOneDim`, `Araki1DConcrete`, `ThermodynamicKMS`, `ClassicalIsing`, `ClassicalIsingConcrete`, `Milestone3Bridges`, `Milestone3Sections678`.
6. **Section 9 & Appendix B — Structural Necessity, Bimodal Counterexample & Double Well**: `StructuralNecessity`, `BimodalExact`, `SpectralSmearingAndDoubleWell`, `Milestone4StructuralNecessity`, `Milestone4Section9AppB`.
7. **Verification Gates**: `SanityChecks` (concrete non-vacuity instantiations), `AuditAxioms` (`#print axioms` on 193 headline theorems), and `comparator/{ChallengeDefs,Challenge,Solution}.lean` (23 locked headline theorems verified by `lake comparator`).
