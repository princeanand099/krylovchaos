# Formalization Progress — `princeanand099/krylovchaos`

## Current Verified Status
- **Library Modules**: 23/23 compiling cleanly (`LAKE_BUILD_EXIT=0`, 3577 jobs on `b819eece6b71754b381facd47b12edc3bbbcb21f`, `ci-logs` `980c8fe9ca12900680ee5ac7de41190b97e79cb6`)
- **Sorries**: 0 in `KrylovChaos/`
- **Custom Axioms**: 0 (`propext`, `Classical.choice`, `Quot.sound` only)
- **Orphan Modules**: 0

## Completed Milestones
1. **Milestones 1–4**: Full initial Lean 4 formalization of Sections 1–9, `comparator/` challenge/solution lock, and `AuditAxioms.lean`.
2. **Milestone 5**: Ground-up Mathlib-only formalization of all 4 literature foundations (`CarlemanJacobi`, `KoteckyPreiss`, `VitaliAnalytic`, `ArakiOneDim`) with zero external hypotheses.
3. **Milestone 6 (Audit Remediation Batch 1)**:
   - Added concrete $N$-qubit operator algebra (`QubitAlgebra.lean`), concrete `LocalHamiltonian` / `GibbsData` / Prop 2.2(3) / full $N$-qubit Prop 2.3 Eq. (2.9) / `bimodalState` / `doubleWellMatrix` (`ManyBodySetup.lean`), and `OperatorBridges.lean` (de-orphaned all 4 literature modules, added `Filter.limsup` Theorem 1.1(a), Corollary 6.5 Eq. 6.11, global $N$-qubit 2-design frame, Lemma 7.1 dual trace bound, Lemma 8.2 multi-edge HS identity).
   - Upgraded `SpectralDyck.lean` with `shiftDyckPath_injective` and ground-up Theorem 1.2(c) (`trace_mul_quad_bound`).
4. **Milestone 7 (Audit Remediation Batch 2 — Ground-Up Concrete Proofs)**:
   - **`KrylovChaos/MajoranaAlgebra.lean`**: Concrete Jordan–Wigner $2n$-mode Majorana Clifford algebra (`{V_i, V_j} = 2δ_{ij} 1`, `{γ_i, γ_j} = δ_{ij} 1`) and full $2n$-Majorana Proposition 2.3 / Eq. (2.10).
   - **`KrylovChaos/ProductStateDerivation.lean`**: Ground-up Wightman Gram–Schmidt basis `{E_0, E_1, E_2, E_3}` for `ρ_x = (I + m Z)/2`, unitary invariance of `S_x`, exact orthonormality, and exact derivation of all 16 entries of `singleSiteM m` (Eq. 4.6).
   - **`KrylovChaos/WightmanProjectors.lean`**: Self-adjointness & idempotence of `partialTraceSite`, exact `0 ⪯ 𝒮 ⪯ N 1` (`totalSizeOp_bounds`), Cauchy–Schwarz (`totalSizeOp_cauchy_schwarz`), operator-level Lemma 4.2 (`lemma_4_2_operator_thermal_size_truncation`, Eq. 4.3), concrete Wightman orthogonal projectors `wightmanProj` (`Submodule.starProjection`), and Proposition 4.1 Loewner dominance (`prop_4_1_loewner_dominance`).
   - **`KrylovChaos/LanczosMoments.lean`**: Concrete symmetric tridiagonal `jacobiMat D b`, exact Dyck-path moment expansion (`jacobiMat_moment_eq_dyck_sum`), full summed Lemma 5.1 moment lower bound (`lemma_5_1_moment_lower_bound`), and ground-up Gamma-integral Meixner `sech` moment lower bound (`meixner_sech_moment_lower_bound`, Eq. 5.5).
