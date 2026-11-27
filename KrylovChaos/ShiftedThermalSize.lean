/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.WightmanIsometry
import KrylovChaos.OperatorGlauberAndLanczosFiltration
import KrylovChaos.Milestone3Sections678
import Mathlib.Tactic

/-!
# Exact Shifted-Commutator Splitting of Thermal Operator Size (Proposition 6.4(1), Eqs. 6.4–6.6)

Defines the exact shifted-commutator decomposition of `[σ_x^α, 𝒥_β(A)]`:
- `X_{x,α}(A) = 𝒥_β([σ_x^α(-iβ/4), A])`
- `D_{x,α} = [σ_x^α, ρ_β^{1/2}]`
- `Y_{x,α}(A) = A(iβ/4) D_{x,α}`
- `ρ_A = (𝒥_β(A))ᴴ (𝒥_β(A))` (which equals `(𝒥_β(A))²` for Hermitian `A`)
- `ℬ_β = (1/8) ∑_{x,α} (σ_x^α(-iβ/2) - σ_x^α)(σ_x^α(-iβ/2) - σ_x^α)ᴴ`
- `II(A) = (1/4) ∑_{x,α} Re ⟨X_{x,α}(A), Y_{x,α}(A)⟩_HS`
- `III(A) = Re Tr((ρ_A - ρ_β) ℬ_β)`

Proves the exact identities (Eqs. 6.4–6.6):
1. `[σ_x^α, 𝒥_β(A)] = X_{x,α}(A) + Y_{x,α}(A)`
2. `S_β(A) = I(A) + II(A) + III(A)`
3. `|II(A)| ≤ 2 √(I(A)) √(Re Tr(ρ_β ℬ_β) + III(A))`
4. `Re Tr(ρ_β ℬ_β) = B_β = Re ⟨ρ_β^{1/2}, 𝒮(ρ_β^{1/2})⟩_HS`.
-/

namespace KrylovChaos

open Matrix

/-- Shifted commutator piece `X_{x,α}(A) = 𝒥_β([σ_x^α(-iβ/4), A])`. -/
noncomputable def shiftedCommX {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ)
    (A : QubitOp N) (x : Fin N) (α : Fin 3) : QubitOp N :=
  jBeta (concreteGibbsData hH β).ρQuarter
    (matComm (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)) A)

/-- Thermal dressing commutator `D_{x,α} = [σ_x^α, ρ_β^{1/2}]`. -/
noncomputable def thermalDiffD {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ)
    (x : Fin N) (α : Fin 3) : QubitOp N :=
  matComm (pauliSite x α.succ) (concreteGibbsData hH β).ρHalf

/-- Thermal-dressing piece `Y_{x,α}(A) = A(iβ/4) D_{x,α}`. -/
noncomputable def thermalDressY {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ)
    (A : QubitOp N) (x : Fin N) (α : Fin 3) : QubitOp N :=
  heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) A * thermalDiffD hH β x α

/-- Thermal background operator
`ℬ_β = (1/8) ∑_{x,α} (σ_x^α(-iβ/2) - σ_x^α) (σ_x^α(-iβ/2) - σ_x^α)ᴴ`. -/
noncomputable def thermalBackgroundOp {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) : QubitOp N :=
  ((1 / 8 : ℝ) : ℂ) • ∑ x : Fin N, ∑ α : Fin 3,
    let Δ := heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) (pauliSite x α.succ) -
      pauliSite x α.succ
    Δ * Δᴴ

/-- Exact cross-term `II(A) = (1/4) ∑_{x,α} Re ⟨X_{x,α}(A), Y_{x,α}(A)⟩_HS` (Eq. 6.5). -/
noncomputable def shiftedThermalSizeII {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (A : QubitOp N) : ℝ :=
  (1 / 4 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
    (hsInner (shiftedCommX hH β A x α) (thermalDressY hH β A x α)).re

/-- Exact background-fluctuation term `III(A) = Re Tr((ρ_A - ρ_β) ℬ_β)` (Eq. 6.6). -/
noncomputable def shiftedThermalSizeIII {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (A : QubitOp N) : ℝ :=
  (((rhoO_op hH β A - (concreteGibbsData hH β).ρβ) * thermalBackgroundOp hH β).trace).re

/-- Helper: `ρ_β^{1/4} * M * ρ_β^{-1/4} = M(iβ/4)` and `ρ_β^{-1/4} * M * ρ_β^{1/4} = M(-iβ/4)`. -/
lemma gibbsRhoQuarter_conj_eq_heisenbergEvol_both {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (M : QubitOp N) :
    let G := concreteGibbsData hH β
    G.ρQuarter * M * G.ρQuarterInv = heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) M ∧
    G.ρQuarterInv * M * G.ρQuarter = heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) M := by
  have h := gibbsRhoQuarter_conj_eq_heisenbergEvol hH β M
  refine ⟨h.1, ?_⟩
  rw [h.2]; congr 1; ring

/-- Helper: `ρ_β^{-1/2} * M * ρ_β^{1/2} = M(-iβ/2)` written as `M * ρ_β^{1/2} = ρ_β^{1/2} * M(-iβ/2)`. -/
lemma mul_gibbsRhoHalf_eq_gibbsRhoHalf_mul_evol {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (M : QubitOp N) :
    let G := concreteGibbsData hH β
    M * G.ρHalf = G.ρHalf * heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) M := by
  intro G
  have h1 := (gibbsRhoQuarter_conj_eq_heisenbergEvol_both hH β M).2
  have h2 := (gibbsRhoQuarter_conj_eq_heisenbergEvol_both hH β
    (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) M)).2
  have hadd : heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ))
      (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) M) =
      heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) M := by
    unfold heisenbergEvol complexPropagator
    simp only [← Matrix.mul_assoc, hermFunc_mul]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hermFunc_mul]
    have hL : (fun x : ℝ ↦
        Complex.exp (Complex.I * (-Complex.I * ((β / 4 : ℝ) : ℂ)) * (x : ℂ)) *
        Complex.exp (Complex.I * (-Complex.I * ((β / 4 : ℝ) : ℂ)) * (x : ℂ))) =
        fun x : ℝ ↦ Complex.exp (Complex.I * (-Complex.I * ((β / 2 : ℝ) : ℂ)) * (x : ℂ)) := by
      funext x; rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hR : (fun x : ℝ ↦
        Complex.exp (Complex.I * -(-Complex.I * ((β / 4 : ℝ) : ℂ)) * (x : ℂ)) *
        Complex.exp (Complex.I * -(-Complex.I * ((β / 4 : ℝ) : ℂ)) * (x : ℂ))) =
        fun x : ℝ ↦ Complex.exp (Complex.I * -(-Complex.I * ((β / 2 : ℝ) : ℂ)) * (x : ℂ)) := by
      funext x; rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hL, hR]; simp only [Matrix.mul_assoc]
  rw [← hadd, ← h2, ← h1]
  calc M * G.ρHalf
      = (G.ρQuarter * G.ρQuarterInv) * M * (G.ρQuarter * G.ρQuarter) := by
          rw [G.inv_right, Matrix.one_mul, G.sq_quarter]
    _ = (G.ρQuarter * G.ρQuarter) * (G.ρQuarterInv * (G.ρQuarterInv * M * G.ρQuarter) * G.ρQuarter) := by
          calc (G.ρQuarter * G.ρQuarterInv) * M * (G.ρQuarter * G.ρQuarter)
              = G.ρQuarter * (G.ρQuarter * G.ρQuarterInv) * G.ρQuarterInv * M * (G.ρQuarter * G.ρQuarter) := by
                  rw [G.inv_right, Matrix.mul_one]
            _ = (G.ρQuarter * G.ρQuarter) * (G.ρQuarterInv * (G.ρQuarterInv * M * G.ρQuarter) * G.ρQuarter) := by
                  simp only [Matrix.mul_assoc]
    _ = G.ρHalf * (G.ρQuarterInv * (G.ρQuarterInv * M * G.ρQuarter) * G.ρQuarter) := by
          rw [G.sq_quarter]

/-- Exact operator splitting `[σ_x^α, 𝒥_β(A)] = X_{x,α}(A) + Y_{x,α}(A)`. -/
theorem matComm_jBeta_eq_shiftedCommX_add_thermalDressY {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) (A : QubitOp N) (x : Fin N) (α : Fin 3) :
    matComm (pauliSite x α.succ) (jBeta (concreteGibbsData hH β).ρQuarter A) =
      shiftedCommX hH β A x α + thermalDressY hH β A x α := by
  set G := concreteGibbsData hH β
  set P := pauliSite x α.succ
  have hP := (gibbsRhoQuarter_conj_eq_heisenbergEvol_both hH β P).2
  have hA := (gibbsRhoQuarter_conj_eq_heisenbergEvol_both hH β A).1
  unfold shiftedCommX thermalDressY thermalDiffD
  change jBeta G.ρQuarter (matComm (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) P) A) +
    heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) A * matComm P G.ρHalf = _
  rw [← hP, ← hA]
  unfold jBeta matComm
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have h1 : G.ρQuarter * (G.ρQuarterInv * (P * (G.ρQuarter * (A * G.ρQuarter)))) =
      P * (G.ρQuarter * (A * G.ρQuarter)) := by
    rw [← Matrix.mul_assoc G.ρQuarter G.ρQuarterInv, G.inv_right, Matrix.one_mul]
  have h2 : G.ρQuarter * (A * (G.ρQuarterInv * (P * (G.ρQuarter * G.ρQuarter)))) =
      G.ρQuarter * (A * (G.ρQuarterInv * (P * G.ρHalf))) := by
    rw [G.sq_quarter]
  have h3 : G.ρQuarter * (A * (G.ρQuarterInv * (G.ρHalf * P))) =
      G.ρQuarter * (A * (G.ρQuarter * P)) := by
    have hq : G.ρQuarterInv * G.ρHalf = G.ρQuarter := by
      rw [← G.sq_quarter, ← Matrix.mul_assoc, G.inv_left, Matrix.one_mul]
    rw [← Matrix.mul_assoc G.ρQuarterInv G.ρHalf, hq]
  rw [h1, h2, h3]
  abel

/-- Factorization of the thermal-dressing piece:
`Y_{x,α}(A) = 𝒥_β(A) * (σ_x^α(-iβ/2) - σ_x^α)`. -/
lemma thermalDressY_eq_jBeta_mul_diff {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (A : QubitOp N) (x : Fin N) (α : Fin 3) :
    thermalDressY hH β A x α =
      jBeta (concreteGibbsData hH β).ρQuarter A *
        (heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) (pauliSite x α.succ) -
          pauliSite x α.succ) := by
  set G := concreteGibbsData hH β
  set P := pauliSite x α.succ
  unfold thermalDressY thermalDiffD matComm
  have hD : P * G.ρHalf - G.ρHalf * P =
      G.ρHalf * (heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) P - P) := by
    rw [Matrix.mul_sub, mul_gibbsRhoHalf_eq_gibbsRhoHalf_mul_evol hH β P]
  have hA : heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) A * G.ρHalf =
      jBeta G.ρQuarter A := by
    rw [← (gibbsRhoQuarter_conj_eq_heisenbergEvol_both hH β A).1]
    unfold jBeta
    calc G.ρQuarter * A * G.ρQuarterInv * G.ρHalf
        = G.ρQuarter * A * (G.ρQuarterInv * G.ρQuarter) * G.ρQuarter := by
            rw [← G.sq_quarter]; simp only [Matrix.mul_assoc]
      _ = G.ρQuarter * A * G.ρQuarter := by rw [G.inv_left, Matrix.mul_one]
  change heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) A * (P * G.ρHalf - G.ρHalf * P) = _
  rw [hD, ← Matrix.mul_assoc, hA]

/-- Exact identification of the Hilbert–Schmidt norm of `Y_{x,α}(A)` with `Re Tr(ρ_A ℬ_β)`:
`(1/8) ∑_{x,α} ‖Y_{x,α}(A)‖_HS² = Re Tr(ρ_A ℬ_β)`. -/
lemma sum_hsNormSq_thermalDressY_eq_trace_rhoO_B {N : ℕ} {H : QubitOp N}
    (hH : H.IsHermitian) (β : ℝ) (A : QubitOp N) :
    (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3, hsNormSq (thermalDressY hH β A x α) =
      ((rhoO_op hH β A * thermalBackgroundOp hH β).trace).re := by
  unfold thermalBackgroundOp rhoO_op
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
    Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl; intro x _
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro α _
  rw [thermalDressY_eq_jBeta_mul_diff]
  unfold hsNormSq hsInner
  congr 1
  set J := jBeta (concreteGibbsData hH β).ρQuarter A
  set Δ := heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) (pauliSite x α.succ) -
    pauliSite x α.succ
  calc ((J * Δ)ᴴ * (J * Δ)).trace
      = (Δᴴ * (Jᴴ * J * Δ)).trace := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = ((Jᴴ * J * Δ) * Δᴴ).trace := Matrix.trace_mul_comm _ _
    _ = (Jᴴ * J * (Δ * Δᴴ)).trace := by simp only [Matrix.mul_assoc]

/-- Symmetry of Hilbert–Schmidt norm under commutator reversal. -/
lemma hsNormSq_matComm_comm {N : ℕ} (U V : QubitOp N) :
    hsNormSq (matComm U V) = hsNormSq (matComm V U) := by
  have hneg : matComm U V = -matComm V U := by unfold matComm; abel
  rw [hneg]
  unfold hsNormSq hsInner
  simp only [Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg]

/-- Exact identification of the thermal background size:
`backgroundSizeB (concreteGibbsData hH β) = Re Tr(ρ_β ℬ_β)`. -/
lemma backgroundSizeB_eq_trace_gibbs_B {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (β : ℝ) :
    backgroundSizeB (concreteGibbsData hH β) =
      (((concreteGibbsData hH β).ρβ * thermalBackgroundOp hH β).trace).re := by
  set G := concreteGibbsData hH β
  have h1 : rhoO_op hH β (1 : QubitOp N) = G.ρβ := by
    unfold rhoO_op jBeta
    change (G.ρQuarter * 1 * G.ρQuarter)ᴴ * (G.ρQuarter * 1 * G.ρQuarter) = G.ρβ
    rw [Matrix.mul_one, G.sq_quarter, G.ρHalf_herm, G.sq_half]
  have hY1 : ∀ (x : Fin N) (α : Fin 3),
      thermalDressY hH β (1 : QubitOp N) x α = matComm (pauliSite x α.succ) G.ρHalf := by
    intro x α
    unfold thermalDressY thermalDiffD
    have h1ev : heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) (1 : QubitOp N) = 1 := by
      unfold heisenbergEvol complexPropagator
      rw [Matrix.mul_one, hermFunc_mul]
      have h0 : (fun E : ℝ ↦
          Complex.exp (Complex.I * (Complex.I * ((β / 4 : ℝ) : ℂ)) * (E : ℂ)) *
          Complex.exp (Complex.I * -(Complex.I * ((β / 4 : ℝ) : ℂ)) * (E : ℂ))) = fun _ ↦ 1 := by
        funext E; rw [← Complex.exp_add]
        have : Complex.I * (Complex.I * ((β / 4 : ℝ) : ℂ)) * (E : ℂ) +
            Complex.I * -(Complex.I * ((β / 4 : ℝ) : ℂ)) * (E : ℂ) = 0 := by ring
        rw [this, Complex.exp_zero]
      rw [h0, hermFunc_one]
    rw [h1ev, Matrix.one_mul]
  rw [← h1, ← sum_hsNormSq_thermalDressY_eq_trace_rhoO_B hH β (1 : QubitOp N)]
  simp_rw [hY1]
  unfold backgroundSizeB totalSizeOp hsInner
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro x _
  have hsite := hsNormSq_siteSizeOp_eq_comm_avg x G.ρHalf
  have hidem := siteSizeOp_idem x G.ρHalf
  have hsa := siteSizeOp_self_adj x G.ρHalf (siteSizeOp x G.ρHalf)
  unfold hsNormSq hsInner at hsite hsa
  have heq : ((siteSizeOp x G.ρHalf)ᴴ * siteSizeOp x G.ρHalf).trace =
      (G.ρHalfᴴ * siteSizeOp x G.ρHalf).trace := by
    rw [hsa, hidem]
  rw [← heq, hsite]
  congr 1
  exact Finset.sum_congr rfl fun α _ ↦ hsNormSq_matComm_comm _ _

/-- For Hermitian `A`, `ρ_A = (𝒥_β(A))²`. -/
lemma rhoO_op_eq_sq_of_herm {N : ℕ} {H A : QubitOp N} (hH : H.IsHermitian) (hA : A.IsHermitian)
    (β : ℝ) :
    rhoO_op hH β A = jBeta (concreteGibbsData hH β).ρQuarter A *
      jBeta (concreteGibbsData hH β).ρQuarter A := by
  unfold rhoO_op jBeta
  set G := concreteGibbsData hH β
  have hjh : (G.ρQuarter * A * G.ρQuarter)ᴴ = G.ρQuarter * A * G.ρQuarter := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, G.ρQuarter_herm, hA.eq, Matrix.mul_assoc]
  rw [hjh]

set_option maxHeartbeats 800000 in
/-- **Proposition 6.4(1) (Exact Shifted-Commutator Thermal-Size Decomposition, Eqs. 6.4–6.6)**:
For ANY Hermitian `H : QubitOp N`, `β : ℝ`, and `A : QubitOp N`:
1. `mssThermalSize G A = otocI hH β A + shiftedThermalSizeII hH β A + shiftedThermalSizeIII hH β A`
2. `|shiftedThermalSizeII hH β A| ≤ 2 * √(otocI hH β A) * √(Re Tr(ρ_β ℬ_β) + shiftedThermalSizeIII hH β A)`. -/
theorem prop_6_4_part1_shifted_eq_6_4 {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (A : QubitOp N) :
    let G := concreteGibbsData hH β
    mssThermalSize G A =
      otocI hH β A + shiftedThermalSizeII hH β A + shiftedThermalSizeIII hH β A ∧
    |shiftedThermalSizeII hH β A| ≤
      2 * Real.sqrt (otocI hH β A) *
        Real.sqrt (((G.ρβ * thermalBackgroundOp hH β).trace).re + shiftedThermalSizeIII hH β A) := by
  intro G
  have htot : (hsInner (jBeta G.ρQuarter A) (totalSizeOp (jBeta G.ρQuarter A))).re =
      (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3,
        hsNormSq (matComm (pauliSite x α.succ) (jBeta G.ρQuarter A)) := by
    unfold totalSizeOp hsInner
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    have hsite := hsNormSq_siteSizeOp_eq_comm_avg x (jBeta G.ρQuarter A)
    have hidem := siteSizeOp_idem x (jBeta G.ρQuarter A)
    have hsa := siteSizeOp_self_adj x (jBeta G.ρQuarter A) (siteSizeOp x (jBeta G.ρQuarter A))
    unfold hsNormSq hsInner at hsite hsa
    have heq : ((siteSizeOp x (jBeta G.ρQuarter A))ᴴ * siteSizeOp x (jBeta G.ρQuarter A)).trace =
        ((jBeta G.ρQuarter A)ᴴ * siteSizeOp x (jBeta G.ρQuarter A)).trace := by
      rw [hsa, hidem]
    rw [← heq, hsite]
    congr 1
    exact Finset.sum_congr rfl fun α _ ↦ hsNormSq_matComm_comm _ _
  have hx_eq : (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3, hsNormSq (shiftedCommX hH β A x α) =
      otocI hH β A := by
    have hpt : ∀ (x : Fin N) (α : Fin 3),
        hsNormSq (shiftedCommX hH β A x α) =
          gibbsWightmanNormSq G (matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ))) := by
      intro x α
      unfold shiftedCommX
      have hiso : hsNormSq (jBeta G.ρQuarter (matComm (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)) A)) =
          gibbsWightmanNormSq G (matComm (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)) A) :=
        congrArg Complex.re
          (prop_2_2_wightman_isometry_inner G.ρQuarter G.ρHalf _ _ G.ρQuarter_herm G.sq_quarter)
      rw [hiso]
      have hneg : matComm (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)) A =
          -matComm A (heisenbergEvol hH (-Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)) := by
        unfold matComm; abel
      rw [hneg]
      unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
      simp only [Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    unfold otocI
    apply congrArg ((1 / 8 : ℝ) * ·)
    exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun α _ ↦ hpt x α
  have hy_eq : (1 / 8 : ℝ) * ∑ x : Fin N, ∑ α : Fin 3, hsNormSq (thermalDressY hH β A x α) =
      ((G.ρβ * thermalBackgroundOp hH β).trace).re + shiftedThermalSizeIII hH β A := by
    rw [sum_hsNormSq_thermalDressY_eq_trace_rhoO_B]
    unfold shiftedThermalSizeIII
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    ring
  have hexp : ∀ (U V : QubitOp N),
      hsNormSq (U + V) = hsNormSq U + 2 * (hsInner U V).re + hsNormSq V := by
    intro U V
    unfold hsNormSq hsInner
    simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    have hsym : (Vᴴ * U).trace.re = (Uᴴ * V).trace.re := by
      have hc : (Vᴴ * U).trace = starRingEnd ℂ (Uᴴ * V).trace := by
        rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hc, Complex.conj_re]
    linarith
  have hdecomp : mssThermalSize G A =
      otocI hH β A + shiftedThermalSizeII hH β A + shiftedThermalSizeIII hH β A := by
    have hpt : ∀ (x : Fin N) (α : Fin 3),
        hsNormSq (matComm (pauliSite x α.succ) (jBeta G.ρQuarter A)) =
        hsNormSq (shiftedCommX hH β A x α) +
        2 * (hsInner (shiftedCommX hH β A x α) (thermalDressY hH β A x α)).re +
        hsNormSq (thermalDressY hH β A x α) := fun x α ↦ by
      rw [matComm_jBeta_eq_shiftedCommX_add_thermalDressY, hexp]
    have hsum_eq : (∑ x : Fin N, ∑ α : Fin 3, hsNormSq (matComm (pauliSite x α.succ) (jBeta G.ρQuarter A))) =
        (∑ x : Fin N, ∑ α : Fin 3, hsNormSq (shiftedCommX hH β A x α)) +
        2 * (∑ x : Fin N, ∑ α : Fin 3, (hsInner (shiftedCommX hH β A x α) (thermalDressY hH β A x α)).re) +
        (∑ x : Fin N, ∑ α : Fin 3, hsNormSq (thermalDressY hH β A x α)) := by
      simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hbg := backgroundSizeB_eq_trace_gibbs_B hH β
    unfold mssThermalSize shiftedThermalSizeII
    have hbg' : (hsInner G.ρHalf (totalSizeOp G.ρHalf)).re =
        ((G.ρβ * thermalBackgroundOp hH β).trace).re := hbg
    rw [htot, hsum_eq, hbg']
    linarith [hx_eq, hy_eq]
  refine ⟨hdecomp, ?_⟩
  rw [← hy_eq, ← hx_eq]
  unfold shiftedThermalSizeII
  set SX := ∑ x : Fin N, ∑ α : Fin 3, hsNormSq (shiftedCommX hH β A x α)
  set SY := ∑ x : Fin N, ∑ α : Fin 3, hsNormSq (thermalDressY hH β A x α)
  set SXY := ∑ x : Fin N, ∑ α : Fin 3, (hsInner (shiftedCommX hH β A x α) (thermalDressY hH β A x α)).re
  have hSX_nn : 0 ≤ SX := Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun α _ ↦ hsNormSq_nonneg _
  have hSY_nn : 0 ≤ SY := Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun α _ ↦ hsNormSq_nonneg _
  have hexp_smul : ∀ (U V : QubitOp N) (t : ℝ),
      hsNormSq (U + (t : ℂ) • V) = hsNormSq U + 2 * t * (hsInner U V).re + t ^ 2 * hsNormSq V := by
    intro U V t
    have h1 : (hsInner U ((t : ℂ) • V)).re = t * (hsInner U V).re := by
      unfold hsInner
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    have h2 : hsNormSq ((t : ℂ) • V) = t ^ 2 * hsNormSq V := by
      unfold hsNormSq hsInner
      simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
        smul_smul, smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Complex.re_ofReal_mul, sq]
    rw [hexp U ((t : ℂ) • V), h1, h2]; ring
  have hquad : ∀ t : ℝ, 0 ≤ SX + 2 * t * SXY + t ^ 2 * SY := by
    intro t
    have hsum_nn : 0 ≤ ∑ x : Fin N, ∑ α : Fin 3,
        hsNormSq (shiftedCommX hH β A x α + (t : ℂ) • thermalDressY hH β A x α) :=
      Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun α _ ↦ hsNormSq_nonneg _
    have hsum_eq : (∑ x : Fin N, ∑ α : Fin 3,
        hsNormSq (shiftedCommX hH β A x α + (t : ℂ) • thermalDressY hH β A x α)) =
        SX + 2 * t * SXY + t ^ 2 * SY := by
      dsimp only [SX, SXY, SY]
      have h1 : ∀ x : Fin N, (∑ α : Fin 3,
          hsNormSq (shiftedCommX hH β A x α + (t : ℂ) • thermalDressY hH β A x α)) =
          (∑ α : Fin 3, hsNormSq (shiftedCommX hH β A x α)) +
          (2 * t) * (∑ α : Fin 3, (hsInner (shiftedCommX hH β A x α) (thermalDressY hH β A x α)).re) +
          (t ^ 2) * (∑ α : Fin 3, hsNormSq (thermalDressY hH β A x α)) := by
        intro x
        trans (∑ α : Fin 3, (hsNormSq (shiftedCommX hH β A x α) +
            2 * t * (hsInner (shiftedCommX hH β A x α) (thermalDressY hH β A x α)).re +
            t ^ 2 * hsNormSq (thermalDressY hH β A x α)))
        · exact Finset.sum_congr rfl fun α _ ↦ hexp_smul _ _ t
        · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      trans (∑ x : Fin N, ((∑ α : Fin 3, hsNormSq (shiftedCommX hH β A x α)) +
          (2 * t) * (∑ α : Fin 3, (hsInner (shiftedCommX hH β A x α) (thermalDressY hH β A x α)).re) +
          (t ^ 2) * (∑ α : Fin 3, hsNormSq (thermalDressY hH β A x α))))
      · exact Finset.sum_congr rfl fun x _ ↦ h1 x
      · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    linarith
  have hcs_sq : SXY ^ 2 ≤ SX * SY := by
    by_cases hSY0 : SY = 0
    · have h0 : SXY = 0 := by
        by_contra hne
        have hq := hquad (-SX / (2 * SXY) - 1 / SXY)
        rw [hSY0, mul_zero, add_zero] at hq
        have : 2 * (-SX / (2 * SXY) - 1 / SXY) * SXY = -SX - 2 := by field_simp [hne]
        linarith
      rw [h0, hSY0]; norm_num
    · have hSYpos : 0 < SY := lt_of_le_of_ne hSY_nn (Ne.symm hSY0)
      have hq := hquad (-SXY / SY)
      have hmul := mul_nonneg hq hSYpos.le
      have hident : (SX + 2 * (-SXY / SY) * SXY + (-SXY / SY) ^ 2 * SY) * SY = SX * SY - SXY ^ 2 := by
        field_simp [hSYpos.ne']; ring
      linarith
  have hrhs_eq : 2 * Real.sqrt ((1 / 8 : ℝ) * SX) * Real.sqrt ((1 / 8 : ℝ) * SY) =
      (1 / 4 : ℝ) * Real.sqrt (SX * SY) := by
    rw [mul_assoc, ← Real.sqrt_mul (by positivity)]
    have h1 : (1 / 8 : ℝ) * SX * ((1 / 8 : ℝ) * SY) = (1 / 8 : ℝ) ^ 2 * (SX * SY) := by ring
    rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]; ring
  rw [hrhs_eq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc |SXY| = Real.sqrt (SXY ^ 2) := (Real.sqrt_sq_eq_abs SXY).symm
    _ ≤ Real.sqrt (SX * SY) := Real.sqrt_le_sqrt hcs_sq

end KrylovChaos
