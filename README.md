# KrylovChaos

Lean 4 (`v4.35.0`) formalization of *Finite-Temperature Bounds on Operator Growth and Quantum Chaos* by Prince Anand (`finite_temp_krylov_chaos.tex`, `FiniteTempKrylovChaos.pdf`).

## Build & Verification

```bash
lake exe cache get
lake build KrylovChaos
```

For full verification (static hygiene check, `#print axioms`, and `lake comparator`):

```bash
./scripts/verify.sh
```

## Documentation

- `PROOF-PATH.md`: Manuscript-to-Lean theorem correspondence table.
- `PROGRESS.md`: Current formalization and CI status.
- `EXTERNAL-AXIOMS.md`: External axiom register (`0` custom axioms).
- `ATTRIBUTION.md` & `CITATION.cff`: Authorship and citation metadata.
