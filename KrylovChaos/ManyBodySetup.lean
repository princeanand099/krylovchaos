/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.WightmanIsometry
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Concrete Many-Body Quantum Setup (Sections 1.2, 2.1, 2.2, 9)

Provides concrete finite-dimensional `N`-qubit definitions and proofs on `QubitOp N`:
1. `LocalTerm` and `LocalHamiltonian N r` (`H = ∑_{X ∈ E} h_X`, Hermitian, `H ∈ filtrationSubmodule N r`).
2. `GibbsData N` (Hermitian `ρ_β, ρ_β^{1/2}, ρ_β^{1/4}, ρ_β^{-1/4}` with `Tr(ρ_β) = 1`) and concrete
   Wightman inner product, MSS-OTOCs (`otocCW`, `mssThermalSize`, `otocI`).
3. **Proposition 2.2(3)**: Unitary equivalence via `jBeta` preserves inner products and intertwines
   the Liouvillian `[H, ·]`, preserving all Lanczos recursion norms.
4. **Proposition 2.3 (Full N-Qubit Eq. 2.9)**: Full `N`-qubit thermal-subtracted operator-size
   identity derived directly from `eq_2_8_hs_commutator_size_identity`.
5. **Section 9 Concrete Counterexamples**: Explicit `N`-qubit bimodal density matrix `bimodalState N`
   (Eq. 9.1) and explicit `D × D` symmetric 1-banded tridiagonal double-well matrix `doubleWellMatrix`.
-/

namespace KrylovChaos

open Matrix

section LocalHamiltonians

/-- A single Hermitian `r`-local interaction term `h_X` on `N` qubits. -/
structure LocalTerm (N r : ℕ) where
  support : Finset (Fin N)
  card_le : support.card ≤ r
  op : QubitOp N
  herm : opᴴ = op
  in_filtration : op ∈ filtrationSubmodule N r

/-- An `r`-local Hermitian Hamiltonian `H = ∑_{X ∈ E} h_X` on `N` qubits. -/
structure LocalHamiltonian (N r : ℕ) where
  terms : List (LocalTerm N r)

/-- Total Hamiltonian matrix `H = ∑_{X ∈ E} h_X`. -/
def LocalHamiltonian.totalOp {N r : ℕ} (ham : LocalHamiltonian N r) : QubitOp N :=
  (ham.terms.map (·.op)).sum

/-- The total Hamiltonian `H` is Hermitian. -/
theorem LocalHamiltonian.totalOp_herm {N r : ℕ} (ham : LocalHamiltonian N r) :
    ham.totalOpᴴ = ham.totalOp := by
  unfold LocalHamiltonian.totalOp
  induction ham.terms with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons, Matrix.conjTranspose_add, t.herm, ih]

/-- Every `r`-local Hamiltonian lies in the `r`-th locality filtration subspace `V_r`. -/
theorem LocalHamiltonian.totalOp_in_filtration {N r : ℕ} (ham : LocalHamiltonian N r) :
    ham.totalOp ∈ filtrationSubmodule N r := by
  unfold LocalHamiltonian.totalOp
  induction ham.terms with
  | nil => exact Submodule.zero_mem _
  | cons t ts ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Submodule.add_mem _ t.in_filtration ih

end LocalHamiltonians

section GibbsAndOTOCs

/-- Concrete finite-dimensional thermal state package `(ρ_β, ρ_β^{1/2}, ρ_β^{1/4}, ρ_β^{-1/4})`
on `QubitOp N`. -/
structure GibbsData (N : ℕ) where
  ρβ : QubitOp N
  ρHalf : QubitOp N
  ρQuarter : QubitOp N
  ρQuarterInv : QubitOp N
  ρβ_herm : ρβᴴ = ρβ
  ρHalf_herm : ρHalfᴴ = ρHalf
  ρQuarter_herm : ρQuarterᴴ = ρQuarter
  ρQuarterInv_herm : ρQuarterInvᴴ = ρQuarterInv
  sq_quarter : ρQuarter * ρQuarter = ρHalf
  sq_half : ρHalf * ρHalf = ρβ
  inv_left : ρQuarterInv * ρQuarter = 1
  inv_right : ρQuarter * ρQuarterInv = 1
  trace_one : ρβ.trace = 1

/-- Concrete Wightman inner product `(A | B)_β^W = Tr(ρ_β^{1/2} A† ρ_β^{1/2} B)` (Eq. 1.2). -/
def wightmanInner {N : ℕ} (G : GibbsData N) (A B : QubitOp N) : ℂ :=
  Matrix.trace (G.ρHalf * Aᴴ * G.ρHalf * B)

/-- Concrete Wightman norm squared `‖A‖_{β,W}² = Re (A | A)_β^W`. -/
def wightmanNormSq {N : ℕ} (G : GibbsData N) (A : QubitOp N) : ℝ :=
  (wightmanInner G A A).re

/-- Concrete summed Wightman squared commutator `C_W(A) = (1/8) ∑_{x,α} ‖[A, σ_x^α]‖_{β,W}²` (Eq. 1.8). -/
noncomputable def otocCW {N : ℕ} (G : GibbsData N) (A : QubitOp N) : ℝ :=
  (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
    wightmanNormSq G (matComm A (pauliSite x α.succ))

/-- Concrete thermal-subtracted Hilbert–Schmidt operator size (Eq. 1.9):
`S_β(A) = Re ⟨𝒥_β(A), S 𝒥_β(A)⟩_HS - Re ⟨ρ_β^{1/2}, S ρ_β^{1/2}⟩_HS`. -/
noncomputable def mssThermalSize {N : ℕ} (G : GibbsData N) (A : QubitOp N) : ℝ :=
  (hsInner (jBeta G.ρQuarter A) (totalSizeOp (jBeta G.ρQuarter A))).re -
  (hsInner G.ρHalf (totalSizeOp G.ρHalf)).re

/-- **Proposition 2.2(3) (Wightman–Hilbert–Schmidt Unitary Equivalence & Lanczos Invariance)**:
`jBeta G.ρQuarter` is an exact isometry `(A | B)_β^W = ⟨𝒥_β(A), 𝒥_β(B)⟩_HS` and intertwines
the Liouvillian `[H, ·]` whenever `[H, ρ_β^{1/4}] = 0`, so every Krylov inner product and
Lanczos coefficient `b_n` computed in `(H_op, (·|·)_β^W)` equals the corresponding Hilbert–Schmidt
quantity for the image sequence `𝒥_β(O_n)`. -/
theorem prop_2_2_lanczos_invariance {N : ℕ} (G : GibbsData N) (H : QubitOp N)
    (hcomm : H * G.ρQuarter = G.ρQuarter * H) :
    (∀ A B : QubitOp N, wightmanInner G A B = hsInner (jBeta G.ρQuarter A) (jBeta G.ρQuarter B)) ∧
    (∀ A : QubitOp N, jBeta G.ρQuarter (matComm H A) = matComm H (jBeta G.ρQuarter A)) := by
  refine ⟨fun A B ↦ ?_, fun A ↦ ?_⟩
  · unfold wightmanInner
    have h := prop_2_2_isometry G.ρQuarter G.ρHalf G.ρQuarter_herm G.sq_quarter A B
    exact h.symm
  · exact prop_2_2_intertwining G.ρQuarter H hcomm A

/-- **Proposition 2.3 (Full N-Qubit Thermal-Subtracted Size Identity, Eq. 2.9)**:
For any `N`-qubit thermal state `G : GibbsData N` and operator `A : QubitOp N`,
`S_β(A) = (1/8) ∑_{x=1}^N ∑_{α=1}^3 (‖[𝒥_β(A), σ_x^α]‖_HS² - ‖[ρ_β^{1/2}, σ_x^α]‖_HS²)`. -/
theorem prop_2_3_full_qubit_thermal_size {N : ℕ} (G : GibbsData N) (A : QubitOp N) :
    mssThermalSize G A =
      (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
        (hsNormSq (matComm (jBeta G.ρQuarter A) (pauliSite x α.succ)) -
         hsNormSq (matComm G.ρHalf (pauliSite x α.succ))) := by
  unfold mssThermalSize
  rw [eq_2_8_hs_commutator_size_identity (jBeta G.ρQuarter A),
      eq_2_8_hs_commutator_size_identity G.ρHalf]
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro x _
  rw [← Finset.sum_sub_distrib]

end GibbsAndOTOCs

section ConcreteCounterexamples

/-- Single-qubit projector `|0⟩⟨0|`. -/
def proj0 : Mat2 := !![1, 0; 0, 0]

/-- Single-qubit projector `|1⟩⟨1|`. -/
def proj1 : Mat2 := !![0, 0; 0, 1]

/-- **Section 9 Concrete Bimodal Density Matrix (Eq. 9.1)**:
For `N ≥ 1`, `ρ = (1/2) |0⟩⟨0|_1 ⊗ (I/2)^{⊗(N-1)} + (1/2) |1⟩⟨1|_1 ⊗ |0…0⟩⟨0…0|_{2…N}`
on `QubitOp N`. -/
noncomputable def bimodalState (N : ℕ) (hN : 0 < N) : QubitOp N :=
  (1 / 2 : ℂ) • kronOp (fun x : Fin N ↦
      if x.1 = 0 then proj0 else (1 / 2 : ℂ) • (1 : Mat2)) +
  (1 / 2 : ℂ) • kronOp (fun x : Fin N ↦
      if x.1 = 0 then proj1 else proj0)

/-- The concrete bimodal density matrix `bimodalState N` is Hermitian. -/
theorem bimodalState_herm (N : ℕ) (hN : 0 < N) :
    (bimodalState N hN)ᴴ = bimodalState N hN := by
  unfold bimodalState
  have hp0 : proj0ᴴ = proj0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [proj0]
  have hp1 : proj1ᴴ = proj1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [proj1]
  have hhalf : ((1 / 2 : ℂ) • (1 : Mat2))ᴴ = (1 / 2 : ℂ) • (1 : Mat2) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, kronOp_conjTranspose]
  have hs : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by simp
  rw [hs]
  congr 1 <;> congr 1 <;> congr 1 <;> funext x <;> split_ifs <;> assumption

/-- The concrete bimodal density matrix `bimodalState N` has unit trace `Tr(ρ) = 1`. -/
theorem bimodalState_trace (N : ℕ) (hN : 0 < N) :
    (bimodalState N hN).trace = 1 := by
  unfold bimodalState
  simp only [Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, kronOp_trace]
  have ht0 : proj0.trace = 1 := by simp [proj0, Matrix.trace, Matrix.diag]
  have ht1 : proj1.trace = 1 := by simp [proj1, Matrix.trace, Matrix.diag]
  have hth : ((1 / 2 : ℂ) • (1 : Mat2)).trace = 1 := by
    simp [Matrix.trace, Matrix.diag]; norm_num
  have hprod1 : (∏ x : Fin N,
      (if x.1 = 0 then proj0 else (1 / 2 : ℂ) • (1 : Mat2)).trace) = 1 := by
    apply Finset.prod_eq_one; intro x _
    split_ifs <;> [exact ht0; exact hth]
  have hprod2 : (∏ x : Fin N, (if x.1 = 0 then proj1 else proj0).trace) = 1 := by
    apply Finset.prod_eq_one; intro x _
    split_ifs <;> [exact ht1; exact ht0]
  rw [hprod1, hprod2]
  norm_num

/-- **Section 9 / Appendix B Concrete Double-Well Matrix**:
Explicit `D × D` real symmetric 1-banded (tridiagonal) matrix `L` with off-diagonal
hopping `1` and barrier potential `E_B` on interior sites `1 ≤ i ≤ D - 2`. -/
def doubleWellMatrix (D : ℕ) (EB : ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun i j ↦
    if i = j then
      if i.1 = 0 ∨ i.1 + 1 = D then 0 else EB
    else if i.1 + 1 = j.1 ∨ j.1 + 1 = i.1 then 1
    else 0

/-- The concrete double-well matrix `doubleWellMatrix D EB` is symmetric (`Lᵀ = L`). -/
theorem doubleWellMatrix_symm (D : ℕ) (EB : ℝ) :
    (doubleWellMatrix D EB)ᵀ = doubleWellMatrix D EB := by
  ext i j
  simp only [Matrix.transpose_apply, doubleWellMatrix, Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : j ≠ i := Ne.symm h
    simp only [h, h', ↓reduceIte, or_comm]

/-- The concrete double-well matrix `doubleWellMatrix D EB` is 1-banded (tridiagonal):
entries vanish whenever `|i - j| > 1`. -/
theorem doubleWellMatrix_tridiag (D : ℕ) (EB : ℝ) (i j : Fin D)
    (hfar : i.1 + 1 < j.1 ∨ j.1 + 1 < i.1) :
    doubleWellMatrix D EB i j = 0 := by
  simp only [doubleWellMatrix, Matrix.of_apply]
  have hne : i ≠ j := by intro heq; subst heq; omega
  have hnotadj : ¬(i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by omega
  simp [hne, hnotadj]

end ConcreteCounterexamples

end KrylovChaos
