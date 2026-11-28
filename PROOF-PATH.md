# Proof Architecture & Dependency Graph

All **82** library modules under `KrylovChaos/` build strictly on standard Mathlib `v4.35.0` with **0 `sorry`s** and **0 custom axioms**, verified across **296** headline theorems in `KrylovChaos/AuditAxioms.lean` and **33** locked headline theorems in `comparator/`.

## Dependency Layers

1. **Layer 0 — Foundations & Operator Algebras**:
   - `Basic.lean`, `WightmanIsometry.lean`, `QubitAlgebra.lean`, `MajoranaAlgebra.lean`, `ManyBodySetup.lean`, `GibbsConstruction.lean`, `SupportAndDualFrame.lean`, `WightmanProjectors.lean`.
2. **Layer 1 — Krylov Dynamics & Static Reduction (Sections 1–4)**:
   - `KrylovTail.lean`, `CarlemanJacobi.lean`, `JacobiSemigroup.lean`, `InfiniteChainLimit.lean`, `InfiniteChainUnconditional.lean`, `Filtration.lean`, `ProductState.lean`, `ProductStateDerivation.lean`, `ProductStateMultiSite.lean`, `ProductStateLambdaMSS.lean`, `Theorem11bConcrete.lean`.
3. **Layer 2 — Spectral Analyticity, Meixner Moments & OTOC Strips (Section 5)**:
   - `CausalExpansion.lean`, `CausalNormBounds.lean`, `SpectralDyck.lean`, `LanczosMoments.lean`, `MeixnerMomentIdentity.lean`, `SpectralMeasure.lean`, `VitaliAnalytic.lean`, `ThermodynamicKMS.lean`, `Theorem12Concrete.lean`, `TimeOrderedOTOC.lean`, `ConcreteSpectralStrip.lean`, `ConcreteOTOCStrip.lean`.
4. **Layer 3 — High-Temperature Cluster Expansion, Reverse Poincaré & Chaos Bound (Sections 6–7 & Appendix A)**:
   - `PolymerTrees.lean`, `KoteckyPreiss.lean`, `ConcreteCombinatorics.lean`, `GlauberDecoupling.lean`, `DepolarizedFrame.lean`, `HighTempConditioning.lean`, `HighTempReversePoincare.lean`, `PolymerExpansionConcrete.lean`, `Lemma72Concrete.lean`, `HighTempParams.lean`, `HighTempSharpBounds.lean`, `ShiftedThermalSize.lean`, `HighTempPolymerZ.lean`, `ProductExpCumulant.lean`, `HighTempCumulant.lean`, `EntropicDecoupling.lean`, `HighTempChaosBound.lean`, `HighTempChaosFull.lean`, `AllTimeLiebRobinson.lean`, `Cor65LatticeBound.lean`.
5. **Layer 4 — 1D All-Temperature Araki & Classical Ising (Section 8)**:
   - `ArakiOneDim.lean`, `Araki1DConcrete.lean`, `ArakiOneDimAllTemp.lean`, `ClassicalIsing.lean`, `ClassicalIsingConcrete.lean`.
6. **Layer 5 — Structural Necessity, Double-Well Tunneling & Packaging (Section 9, Appendix B & Verification)**:
   - `StructuralNecessity.lean`, `SpectralSmearingAndDoubleWell.lean`, `GaussianSmearingBridge.lean`, `BimodalExact.lean`, `BimodalFullRank.lean`, `DoubleWellTunneling.lean`, `DoubleWellKrylovLimit.lean`, `Section9EndToEnd.lean`, `MainTheoremPackaging.lean`, `SanityChecks.lean`, `AuditAxioms.lean`.
