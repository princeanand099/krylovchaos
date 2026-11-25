# Proof Path & Manuscript-to-Lean Correspondence

This file tracks the dependency-ordered correspondence between *Finite-Temperature Bounds on Operator Growth and Quantum Chaos* (`finite_temp_krylov_chaos.tex`) and the Lean 4 modules in `KrylovChaos/`.

| Manuscript Result | Section | Lean Module | Status |
|---|---|---|---|
| Scales $\kappa, \beta_{\mathrm{wc}}$, Eq. (1.19), elementary inequalities | §1.2–1.3 | `KrylovChaos/Basic.lean` | Implemented |
| Lemma 2.1 (Nested-Commutator Cluster Bound) | §2.1 | `KrylovChaos/WightmanIsometry.lean` | Implemented |
| Proposition 2.2 (Wightman–Hilbert–Schmidt Isometry) | §2.2 | `KrylovChaos/WightmanIsometry.lean` | Implemented |
| Proposition 2.3 (MSS-OTOC & Thermal-Size Identity) | §2.3 | `KrylovChaos/WightmanIsometry.lean` | Implemented |
| Lemma 3.1 & Theorem 1.1(a) (Krylov Tail & Complexity) | §3 | `KrylovChaos/KrylovTail.lean` | Pending |
| Proposition 4.1, Lemma 4.2, Theorem 1.1(b) | §4.1–4.2 | `KrylovChaos/Filtration.lean` | Pending |
| Proposition 4.3 (Product State Static Bound) | §4.3 | `KrylovChaos/ProductState.lean` | Pending |
| Theorem 1.2(a)–(c), Lemma 5.1 (Spectral Decay & Dyck Paths) | §5 | `KrylovChaos/SpectralDyck.lean` | Pending |
| Lemma 6.1, Proposition 6.2, Proposition 6.4, Corollary 6.5 | §6 | `KrylovChaos/GlauberDecoupling.lean` | Pending |
| Lemma 7.1, Lemma 7.3, Theorem 1.3(a)–(c) | §7 | `KrylovChaos/DepolarizedFrame.lean` | Pending |
| Lemmas A.1–A.3, Lemma 6.3, Lemma 7.2 (Trees & Cluster Bounds) | App. A, §6–7 | `KrylovChaos/PolymerTrees.lean` | Pending |
| Proposition 8.1, Lemma 8.2, Proposition 8.3 (1D & Classical Ising) | §8 | `KrylovChaos/ClassicalIsing.lean` | Pending |
| Proposition 9.1(1)–(3), Lemma B.1 (Structural Necessity & Double Well) | §9, App. B | `KrylovChaos/StructuralNecessity.lean` | Pending |
