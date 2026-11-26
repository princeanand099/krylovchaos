# External Axioms Audit

## Custom Axioms in Lean: None (`0`)

`KrylovChaos` and `comparator/Solution.lean` contain **zero** `axiom` declarations, **zero** `sorry`s, **zero** `admit`s, **zero** `native_decide` calls, and **zero** unsafe or kernel-bypassing constructs. Every exported theorem depends strictly on a subset of Lean 4's three standard logical axioms:

- `propext`
- `Classical.choice`
- `Quot.sound`

Verify directly via:

```bash
lake env lean KrylovChaos/AuditAxioms.lean
```

## External Infinite-Volume / Literature Theorems Outside Mathlib `v4.35.0`

The manuscript *Finite-Temperature Bounds on Operator Growth and Quantum Chaos* invokes four classical infinite-volume / functional-analytic results from the mathematical physics literature that are not yet formalized in Mathlib `v4.35.0`:

1. **Carleman's essential self-adjointness criterion** (Section 3, infinite tridiagonal Jacobi operators with `∑ 1/b_n = ∞`).
2. **Montel / Vitali normal-family convergence** (Section 5, thermodynamic limit of analytic complex-time OTOCs).
3. **Araki's 1D complex-time analyticity theorem** (Section 8, imaginary-time evolution in 1D quantum spin chains).
4. **Abstract infinite-volume Kotecký–Preiss cluster-expansion convergence theorem** (Sections 6–7 & Appendix A).

Rather than declaring any of these as custom Lean `axiom`s, `KrylovChaos` proves every finite-volume, combinatorial, algebraic, ODE/MGF, spectral, Dyck-path, 2-design frame, Kotecký–Preiss criterion verification, Hubbard–Stratonovich, reverse-Poincaré, and asymptotic rate-comparison theorem unconditionally in Mathlib, with explicit hypotheses where infinite-volume limits enter.
