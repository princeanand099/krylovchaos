# Proof Dependency Path (`KrylovChaos`)

## Module DAG (19 Library Modules, Zero Orphans)

```
KrylovChaos.Basic
├── KrylovChaos.QubitAlgebra         (Concrete N-qubit QubitOp N, Pauli strings, Eq. 2.8, filtration_comm_step)
│   └── KrylovChaos.ManyBodySetup    (LocalHamiltonian, GibbsData, Prop 2.2(3), Prop 2.3 Eq. 2.9, bimodalState, doubleWellMatrix)
├── KrylovChaos.WightmanIsometry     (Sec. 2: Prop 2.2, Prop 2.3, Lemma 2.1)
├── KrylovChaos.CarlemanJacobi       (Ground-up Carleman criterion & zero deficiency indices)
├── KrylovChaos.KrylovTail           (Sec. 3: Thm 1.1(a) method of characteristics & tail bounds)
├── KrylovChaos.Filtration           (Sec. 4.1–4.2: Prop 4.1, Lemma 4.2, Thm 1.1(b))
├── KrylovChaos.ProductState         (Sec. 4.3: Prop 4.3 product-state static bound)
├── KrylovChaos.VitaliAnalytic       (Ground-up Vitali/Montel power-series convergence)
├── KrylovChaos.SpectralDyck         (Sec. 5: Thm 1.2(a)–(c), Lemma 5.1, shiftDyckPath_injective) [imports VitaliAnalytic]
├── KrylovChaos.KoteckyPreiss        (Ground-up Kotecký–Preiss polymer cluster expansion)
├── KrylovChaos.PolymerTrees         (App. A: Lemma A.1, A.2, Prop A.3)
├── KrylovChaos.GlauberDecoupling    (Sec. 6: Lemma 6.1, Prop 6.2, Prop 6.4)
├── KrylovChaos.DepolarizedFrame     (Sec. 7: Lemma 7.1, 7.3, Thm 1.3)
├── KrylovChaos.ArakiOneDim          (Ground-up Araki 1D boundary-commutator expansional)
├── KrylovChaos.ClassicalIsing       (Sec. 8: Prop 8.1, Lemma 8.2, Prop 8.3)
├── KrylovChaos.StructuralNecessity  (Sec. 9 & App. B: Prop 9.1(1)–(3))
└── KrylovChaos.OperatorBridges      (Unified bridge DAG: limsup rate, Carleman ESA, concrete N-qubit filtration, Corollary 6.5 Eq. 6.11, global N-qubit 2-design frame, Lemma 7.1(3b), multi-edge HS)
    └── KrylovChaos.SanityChecks
```

All 23 locked theorems in `comparator/Challenge.lean` are verified by `lake comparator` with zero `sorry`s and zero custom axioms (`⊆ [propext, Classical.choice, Quot.sound]`).
