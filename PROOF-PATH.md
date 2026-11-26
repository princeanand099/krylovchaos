# Proof Path and Module Dependency DAG

```
KrylovChaos.Basic
├── KrylovChaos.WightmanIsometry
│   ├── KrylovChaos.QubitAlgebra (concrete N-qubit algebra, Pauli strings, Eq. 2.8, concrete filtration)
│   ├── KrylovChaos.SpectralDyck (imports VitaliAnalytic)
│   └── KrylovChaos.GlauberDecoupling
├── KrylovChaos.KrylovTail
├── KrylovChaos.CarlemanJacobi
├── KrylovChaos.Filtration
├── KrylovChaos.ProductState
│   ├── KrylovChaos.QubitAlgebra
│   └── KrylovChaos.DepolarizedFrame
├── KrylovChaos.PolymerTrees
├── KrylovChaos.KoteckyPreiss
├── KrylovChaos.VitaliAnalytic
├── KrylovChaos.ArakiOneDim
├── KrylovChaos.ClassicalIsing
└── KrylovChaos.StructuralNecessity
        │
        ▼
KrylovChaos.SanityChecks
        │
        ▼
KrylovChaos (root aggregator, 17 library modules)
├── KrylovChaos.AuditAxioms (standalone `#print axioms` gate)
└── comparator/Solution.lean (discharges all 23 locked theorems in comparator/Challenge.lean)
```
