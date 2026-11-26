/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.ProductState
import KrylovChaos.QubitAlgebra
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Ground-Up Derivation of the Single-Site Product-State Matrix (Section 4.3, Eq. 4.6)

Derives `singleSiteM m` (Eq. 4.6 of `finite_temp_krylov_chaos.tex`) directly from the
single-qubit thermal state `ρ_x = (I + m Z)/2` via:
1. Explicit matrix roots `ρ_x^{1/2}` and `ρ_x^{1/4}` (`singleSiteRho_roots`).
2. Unitary invariance of the single-site size superoperator `S_x(M) = M - (1/2) Tr(M) I`
   (`singleSiteSizeOp_unitary_invariant`).
3. Explicit Wightman Gram–Schmidt orthonormal basis `{E_0, E_1, E_2, E_3}` (`gsBasis m`),
   with ground-up proof of Hermiticity (`gsBasis_herm`) and exact Wightman orthonormality
   `(E_a | E_b)_{ρ_x}^W = δ_{ab}` (`gsBasis_wightman_orthonormal`).
4. Exact matrix-element derivation of all 16 entries of `singleSiteM m` from the
   thermal-subtracted Hilbert–Schmidt size quadratic form (`gsBasis_derives_singleSiteM`).
-/

namespace KrylovChaos

open scoped Matrix

section SingleSiteProductDerivation

/-- Single-qubit thermal density matrix `ρ_x = (I + m Z)/2 = diag((1+m)/2, (1-m)/2)`. -/
noncomputable def singleSiteRho (m : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(((1 + m) / 2 : ℝ) : ℂ), 0; 0, (((1 - m) / 2 : ℝ) : ℂ)]

/-- Positive square root `ρ_x^{1/2}`. -/
noncomputable def singleSiteRhoHalf (m : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt ((1 + m) / 2) : ℂ), 0; 0, (Real.sqrt ((1 - m) / 2) : ℂ)]

/-- Positive fourth root `ρ_x^{1/4}`. -/
noncomputable def singleSiteRhoQuarter (m : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt (Real.sqrt ((1 + m) / 2)) : ℂ), 0;
     0, (Real.sqrt (Real.sqrt ((1 - m) / 2)) : ℂ)]

/-- Single-site size superoperator `S_x(M) = M - (1/2) Tr(M) I`. -/
noncomputable def singleSiteSizeOp (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  M - ((1 / 2 : ℂ) * M.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Unitary invariance of `S_x`: `S_x(U M Uᴴ) = U S_x(M) Uᴴ` for unitary `U`. -/
theorem singleSiteSizeOp_unitary_invariant (U M : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    singleSiteSizeOp (U * M * Uᴴ) = U * singleSiteSizeOp M * Uᴴ := by
  unfold singleSiteSizeOp
  have htr : (U * M * Uᴴ).trace = M.trace := by
    rw [Matrix.trace_mul_comm (U * M) Uᴴ, ← Matrix.mul_assoc, hU', Matrix.one_mul]
  rw [htr, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU]

/-- Single-site Wightman inner product `(A | B)_{ρ_x}^W = Tr(ρ_x^{1/2} Aᴴ ρ_x^{1/2} B)`. -/
noncomputable def singleSiteWightmanInner (m : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (singleSiteRhoHalf m * Aᴴ * singleSiteRhoHalf m * B).trace

/-- Single-site Wightman isometry `J_x(A) = ρ_x^{1/4} A ρ_x^{1/4}`. -/
noncomputable def singleSiteJ (m : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  singleSiteRhoQuarter m * A * singleSiteRhoQuarter m

/-- Single-site Hilbert–Schmidt size quadratic form `⟨J_x(A), S_x J_x(B)⟩_HS`. -/
noncomputable def singleSiteSizeForm (m : ℝ) (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ((singleSiteJ m A)ᴴ * singleSiteSizeOp (singleSiteJ m B)).trace

/-- Verification of matrix root identities `ρ_x^{1/2} ρ_x^{1/2} = ρ_x` and
`ρ_x^{1/4} ρ_x^{1/4} = ρ_x^{1/2}` for `|m| < 1`. -/
theorem singleSiteRho_roots {m : ℝ} (hm : |m| < 1) :
    singleSiteRhoHalf m * singleSiteRhoHalf m = singleSiteRho m ∧
    singleSiteRhoQuarter m * singleSiteRhoQuarter m = singleSiteRhoHalf m := by
  have hlt := abs_lt.mp hm
  have hp : 0 ≤ (1 + m) / 2 := by linarith
  have hr : 0 ≤ (1 - m) / 2 := by linarith
  set p := Real.sqrt ((1 + m) / 2)
  set r := Real.sqrt ((1 - m) / 2)
  have hpp : (p : ℂ) * (p : ℂ) = (((1 + m) / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp]
  have hrr : (r : ℂ) * (r : ℂ) = (((1 - m) / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  have hqp : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
  have hqr : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [singleSiteRhoHalf, singleSiteRho, Matrix.mul_apply, Fin.sum_univ_two, hpp, hrr]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [singleSiteRhoQuarter, singleSiteRhoHalf, Matrix.mul_apply, Fin.sum_univ_two, hqp, hqr]

/-- Wightman Gram–Schmidt orthonormal basis `{E_0, E_1, E_2, E_3}` for `ρ_x = (I + m Z)/2`. -/
noncomputable def gsBasis (m : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => pauliMat 0
  | 1 => ((Real.sqrt (prodSigma m))⁻¹ : ℂ) • pauliMat 1
  | 2 => ((Real.sqrt (prodSigma m))⁻¹ : ℂ) • pauliMat 2
  | 3 => ((prodSigma m)⁻¹ : ℂ) • (pauliMat 3 - (m : ℂ) • pauliMat 0)

/-- Every Gram–Schmidt basis element is Hermitian: `(E_a)ᴴ = E_a`. -/
theorem gsBasis_herm (m : ℝ) (a : Fin 4) : (gsBasis m a)ᴴ = gsBasis m a := by
  fin_cases a <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gsBasis, pauliMat, Matrix.conjTranspose_apply]

private lemma prod_param_identities {m : ℝ} (hm : |m| < 1) :
    let p := Real.sqrt ((1 + m) / 2)
    let r := Real.sqrt ((1 - m) / 2)
    0 < p ∧ 0 < r ∧ 0 < prodSigma m ∧
    p ^ 2 = (1 + m) / 2 ∧ r ^ 2 = (1 - m) / 2 ∧
    2 * p * r = prodSigma m ∧
    (prodQ m) ^ 2 = 1 - prodSigma m := by
  have hlt := abs_lt.mp hm
  have hp_pos : 0 < (1 + m) / 2 := by linarith
  have hr_pos : 0 < (1 - m) / 2 := by linarith
  have h1m2 : 0 < 1 - m ^ 2 := by nlinarith
  have hp : 0 < Real.sqrt ((1 + m) / 2) := Real.sqrt_pos.mpr hp_pos
  have hr : 0 < Real.sqrt ((1 - m) / 2) := Real.sqrt_pos.mpr hr_pos
  have hσ : 0 < prodSigma m := Real.sqrt_pos.mpr h1m2
  have hp2 : (Real.sqrt ((1 + m) / 2)) ^ 2 = (1 + m) / 2 := Real.sq_sqrt hp_pos.le
  have hr2 : (Real.sqrt ((1 - m) / 2)) ^ 2 = (1 - m) / 2 := Real.sq_sqrt hr_pos.le
  have h2pr : 2 * Real.sqrt ((1 + m) / 2) * Real.sqrt ((1 - m) / 2) = prodSigma m := by
    have hsq : (2 * Real.sqrt ((1 + m) / 2) * Real.sqrt ((1 - m) / 2)) ^ 2 = 1 - m ^ 2 := by
      calc (2 * Real.sqrt ((1 + m) / 2) * Real.sqrt ((1 - m) / 2)) ^ 2
          = 4 * (Real.sqrt ((1 + m) / 2)) ^ 2 * (Real.sqrt ((1 - m) / 2)) ^ 2 := by ring
        _ = 4 * ((1 + m) / 2) * ((1 - m) / 2) := by rw [hp2, hr2]
        _ = 1 - m ^ 2 := by ring
    unfold prodSigma
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.sqrt ((1 + m) / 2) * Real.sqrt ((1 - m) / 2)), hsq]
  have hq2 : (prodQ m) ^ 2 = 1 - prodSigma m := by
    unfold prodQ
    calc (Real.sqrt ((1 + m) / 2) - Real.sqrt ((1 - m) / 2)) ^ 2
        = (Real.sqrt ((1 + m) / 2)) ^ 2 + (Real.sqrt ((1 - m) / 2)) ^ 2 -
            2 * Real.sqrt ((1 + m) / 2) * Real.sqrt ((1 - m) / 2) := by ring
      _ = (1 + m) / 2 + (1 - m) / 2 - prodSigma m := by rw [hp2, hr2, h2pr]
      _ = 1 - prodSigma m := by ring
  exact ⟨hp, hr, hσ, hp2, hr2, h2pr, hq2⟩

/-- **Gram–Schmidt Wightman Orthonormality**:
`(E_a | E_b)_{ρ_x}^W = δ_{ab}` for all `a, b : Fin 4` and `|m| < 1`. -/
theorem gsBasis_wightman_orthonormal {m : ℝ} (hm : |m| < 1) (a b : Fin 4) :
    singleSiteWightmanInner m (gsBasis m a) (gsBasis m b) = if a = b then 1 else 0 := by
  obtain ⟨hp, hr, hσ, hp2, hr2, h2pr, _⟩ := prod_param_identities hm
  set p := Real.sqrt ((1 + m) / 2)
  set r := Real.sqrt ((1 - m) / 2)
  have hσ_ne : (prodSigma m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  have hsqσ_ne : (Real.sqrt (prodSigma m) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hσ).ne'
  have hsqσ2 : (Real.sqrt (prodSigma m) : ℂ) * (Real.sqrt (prodSigma m) : ℂ) = (prodSigma m : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hσ.le]
  have hσ2 : (prodSigma m : ℂ) ^ 2 = (1 - m ^ 2 : ℂ) := by
    have : (prodSigma m) ^ 2 = 1 - m ^ 2 := Real.sq_sqrt (by nlinarith [abs_lt.mp hm])
    exact_mod_cast this
  have h2prC : (2 : ℂ) * (p : ℂ) * (r : ℂ) = (prodSigma m : ℂ) := by exact_mod_cast h2pr
  have hp2C : (p : ℂ) * (p : ℂ) = ((1 + m) / 2 : ℂ) := by
    have : p * p = (1 + m) / 2 := by nlinarith [hp2]
    exact_mod_cast this
  have hr2C : (r : ℂ) * (r : ℂ) = ((1 - m) / 2 : ℂ) := by
    have : r * r = (1 - m) / 2 := by nlinarith [hr2]
    exact_mod_cast this
  fin_cases a <;> fin_cases b <;>
    simp [singleSiteWightmanInner, singleSiteRhoHalf, gsBasis, pauliMat,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply]
  · linear_combination hp2C + hr2C
  · have : ((p : ℂ) * (p : ℂ) * (1 - (m : ℂ)) + (r : ℂ) * (r : ℂ) * (-1 - (m : ℂ))) = 0 := by
      rw [hp2C, hr2C]; ring
    field_simp [hσ_ne]; linear_combination this
  · field_simp [hsqσ_ne]; rw [hsqσ2]; linear_combination -h2prC
  · field_simp [hsqσ_ne]; rw [hsqσ2]; linear_combination -h2prC
  · have : ((p : ℂ) * (p : ℂ) * (1 - (m : ℂ)) + (r : ℂ) * (r : ℂ) * (-1 - (m : ℂ))) = 0 := by
      rw [hp2C, hr2C]; ring
    field_simp [hσ_ne]; linear_combination this
  · field_simp [hσ_ne]
    have : (p : ℂ) * (p : ℂ) * (1 - (m : ℂ)) ^ 2 + (r : ℂ) * (r : ℂ) * (-1 - (m : ℂ)) ^ 2 =
        1 - (m : ℂ) ^ 2 := by
      rw [hp2C, hr2C]; ring
    rw [hσ2]; linear_combination this

/-- **Ground-Up Derivation of Eq. (4.6) (`singleSiteM`)**:
For every `|m| < 1` and every `a, b : Fin 4`, the thermal-subtracted single-site
size matrix element in the Wightman Gram–Schmidt basis `{E_0, E_1, E_2, E_3}` equals
`singleSiteM m a b` identically. -/
theorem gsBasis_derives_singleSiteM {m : ℝ} (hm : |m| < 1) (a b : Fin 4) :
    singleSiteSizeForm m (gsBasis m a) (gsBasis m b) -
      (if a = b then singleSiteSizeForm m (gsBasis m 0) (gsBasis m 0) else 0) =
    (singleSiteM m a b : ℂ) := by
  obtain ⟨hp, hr, hσ, hp2, hr2, h2pr, hq2⟩ := prod_param_identities hm
  set p := Real.sqrt ((1 + m) / 2)
  set r := Real.sqrt ((1 - m) / 2)
  have hσ_ne : (prodSigma m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  have hsqσ_ne : (Real.sqrt (prodSigma m) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hσ).ne'
  have hsqσ2 : (Real.sqrt (prodSigma m) : ℂ) * (Real.sqrt (prodSigma m) : ℂ) = (prodSigma m : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hσ.le]
  have hσ2 : (prodSigma m : ℂ) ^ 2 = (1 - m ^ 2 : ℂ) := by
    have : (prodSigma m) ^ 2 = 1 - m ^ 2 := Real.sq_sqrt (by nlinarith [abs_lt.mp hm])
    exact_mod_cast this
  have h2prC : (2 : ℂ) * (p : ℂ) * (r : ℂ) = (prodSigma m : ℂ) := by exact_mod_cast h2pr
  have hp2C : (p : ℂ) * (p : ℂ) = ((1 + m) / 2 : ℂ) := by
    have : p * p = (1 + m) / 2 := by nlinarith [hp2]
    exact_mod_cast this
  have hr2C : (r : ℂ) * (r : ℂ) = ((1 - m) / 2 : ℂ) := by
    have : r * r = (1 - m) / 2 := by nlinarith [hr2]
    exact_mod_cast this
  have hqp : (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp.le]
  have hqr : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr.le]
  have hq2C : ((prodQ m) ^ 2 : ℂ) = 1 - (prodSigma m : ℂ) := by exact_mod_cast hq2
  have h00 : singleSiteSizeForm m (gsBasis m 0) (gsBasis m 0) = ((prodQ m) ^ 2 / 2 : ℂ) := by
    simp only [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      smul_eq_mul, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add,
      mul_one, one_mul, star_zero, star_one, Complex.star_def, Complex.conj_ofReal,
      ↓reduceIte, Fin.zero_eta, Fin.mk_one, zero_ne_one, one_ne_zero]
    calc (Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) *
            ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) -
              1 / 2 * ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) +
                (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ))) +
          (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) *
            ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) -
              1 / 2 * ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ) +
                (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)))
        = (p : ℂ) * ((p : ℂ) - 1 / 2 * ((p : ℂ) + (r : ℂ))) +
          (r : ℂ) * ((r : ℂ) - 1 / 2 * ((p : ℂ) + (r : ℂ))) := by rw [hqp, hqr]
      _ = ((p : ℂ) * (p : ℂ) + (r : ℂ) * (r : ℂ) - 2 * (p : ℂ) * (r : ℂ)) / 2 := by ring
      _ = (1 - (prodSigma m : ℂ)) / 2 := by rw [hp2C, hr2C, h2prC]; ring
      _ = ((prodQ m) ^ 2 / 2 : ℂ) := by rw [← hq2C]; ring
  have h11 : singleSiteSizeForm m (gsBasis m 1) (gsBasis m 1) = 1 := by
    simp only [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      smul_eq_mul, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add,
      mul_one, one_mul, star_zero, star_one, Complex.star_def, Complex.conj_ofReal,
      ↓reduceIte, Fin.zero_eta, Fin.mk_one, zero_ne_one, one_ne_zero, sub_zero]
    have hstep :
        (Real.sqrt p : ℂ) * (Real.sqrt (prodSigma m) : ℂ)⁻¹ * (Real.sqrt r : ℂ) *
          ((Real.sqrt r : ℂ) * (Real.sqrt (prodSigma m) : ℂ)⁻¹ * (Real.sqrt p : ℂ)) +
        (Real.sqrt r : ℂ) * (Real.sqrt (prodSigma m) : ℂ)⁻¹ * (Real.sqrt p : ℂ) *
          ((Real.sqrt p : ℂ) * (Real.sqrt (prodSigma m) : ℂ)⁻¹ * (Real.sqrt r : ℂ)) =
        (2 * ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ)) * ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ))) *
          ((Real.sqrt (prodSigma m) : ℂ) * (Real.sqrt (prodSigma m) : ℂ))⁻¹ := by ring
    rw [hstep, hqp, hqr, hsqσ2, h2prC]
    exact mul_inv_cancel₀ hσ_ne
  have h22 : singleSiteSizeForm m (gsBasis m 2) (gsBasis m 2) = 1 := by
    simp only [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      smul_eq_mul, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add,
      mul_one, one_mul, star_zero, star_one, Complex.star_def, Complex.conj_ofReal,
      ↓reduceIte, Fin.zero_eta, Fin.mk_one, zero_ne_one, one_ne_zero, sub_zero,
      map_mul, map_neg, Complex.conj_I, neg_neg]
    have hstep :
        (Real.sqrt p : ℂ) * ((Real.sqrt (prodSigma m) : ℂ)⁻¹ * Complex.I) * (Real.sqrt r : ℂ) *
          ((Real.sqrt r : ℂ) * ((Real.sqrt (prodSigma m) : ℂ)⁻¹ * -Complex.I) * (Real.sqrt p : ℂ)) +
        (Real.sqrt r : ℂ) * ((Real.sqrt (prodSigma m) : ℂ)⁻¹ * -Complex.I) * (Real.sqrt p : ℂ) *
          ((Real.sqrt p : ℂ) * ((Real.sqrt (prodSigma m) : ℂ)⁻¹ * Complex.I) * (Real.sqrt r : ℂ)) =
        (2 * ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ)) * ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ))) *
          ((Real.sqrt (prodSigma m) : ℂ) * (Real.sqrt (prodSigma m) : ℂ))⁻¹ *
          (-(Complex.I * Complex.I)) := by ring
    have hII : -(Complex.I * Complex.I) = 1 := by simp [Complex.I_mul_I]
    rw [hstep, hqp, hqr, hsqσ2, h2prC, hII, mul_one]
    exact mul_inv_cancel₀ hσ_ne
  have h33 : singleSiteSizeForm m (gsBasis m 3) (gsBasis m 3) = 1 - ((prodQ m) ^ 2 / 2 : ℂ) := by
    simp only [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      smul_eq_mul, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add,
      mul_one, one_mul, star_zero, star_one, Complex.star_def, Complex.conj_ofReal,
      ↓reduceIte, Fin.zero_eta, Fin.mk_one, zero_ne_one, one_ne_zero, sub_self, neg_zero,
      map_mul, map_sub, map_inv₀, map_neg, map_one]
    have hpa : (Real.sqrt p : ℂ) * ((prodSigma m : ℂ)⁻¹ * (1 - (m : ℂ))) * (Real.sqrt p : ℂ) =
        (p : ℂ) * (prodSigma m : ℂ)⁻¹ * (1 - (m : ℂ)) := by
      calc _ = ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ)) * (prodSigma m : ℂ)⁻¹ * (1 - (m : ℂ)) := by ring
        _ = _ := by rw [hqp]
    have hra : (Real.sqrt r : ℂ) * ((prodSigma m : ℂ)⁻¹ * (-1 - (m : ℂ))) * (Real.sqrt r : ℂ) =
        (r : ℂ) * (prodSigma m : ℂ)⁻¹ * (-1 - (m : ℂ)) := by
      calc _ = ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) * (prodSigma m : ℂ)⁻¹ * (-1 - (m : ℂ)) := by ring
        _ = _ := by rw [hqr]
    rw [hpa, hra, hq2C]
    field_simp [hσ_ne]
    calc (p : ℂ) * (1 - (m : ℂ)) *
          ((p : ℂ) * (1 - (m : ℂ)) * 2 - ((p : ℂ) * (1 - (m : ℂ)) + (r : ℂ) * (-1 - (m : ℂ)))) +
        (r : ℂ) * (-1 - (m : ℂ)) *
          ((r : ℂ) * (-1 - (m : ℂ)) * 2 - ((p : ℂ) * (1 - (m : ℂ)) + (r : ℂ) * (-1 - (m : ℂ))))
        = (p : ℂ) * (p : ℂ) * (1 - (m : ℂ)) ^ 2 + (r : ℂ) * (r : ℂ) * (1 + (m : ℂ)) ^ 2 +
          2 * (p : ℂ) * (r : ℂ) * (1 - (m : ℂ) ^ 2) := by ring
      _ = ((1 + (m : ℂ)) / 2) * (1 - (m : ℂ)) ^ 2 + ((1 - (m : ℂ)) / 2) * (1 + (m : ℂ)) ^ 2 +
          (prodSigma m : ℂ) * (1 - (m : ℂ) ^ 2) := by rw [hp2C, hr2C, h2prC]
      _ = (1 - (m : ℂ) ^ 2) * (1 + (prodSigma m : ℂ)) := by ring
      _ = (prodSigma m : ℂ) ^ 2 * (1 + (prodSigma m : ℂ)) := by rw [hσ2]
      _ = (2 - (1 - (prodSigma m : ℂ))) * (prodSigma m : ℂ) ^ 2 := by ring
  have h03 : singleSiteSizeForm m (gsBasis m 0) (gsBasis m 3) = (m : ℂ) / 2 := by
    simp only [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      smul_eq_mul, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add,
      mul_one, one_mul, star_zero, star_one, Complex.star_def, Complex.conj_ofReal,
      ↓reduceIte, Fin.zero_eta, Fin.mk_one, zero_ne_one, one_ne_zero, sub_self, neg_zero]
    have hpa : (Real.sqrt p : ℂ) * ((prodSigma m : ℂ)⁻¹ * (1 - (m : ℂ))) * (Real.sqrt p : ℂ) =
        (p : ℂ) * (prodSigma m : ℂ)⁻¹ * (1 - (m : ℂ)) := by
      calc _ = ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ)) * (prodSigma m : ℂ)⁻¹ * (1 - (m : ℂ)) := by ring
        _ = _ := by rw [hqp]
    have hra : (Real.sqrt r : ℂ) * ((prodSigma m : ℂ)⁻¹ * (-1 - (m : ℂ))) * (Real.sqrt r : ℂ) =
        (r : ℂ) * (prodSigma m : ℂ)⁻¹ * (-1 - (m : ℂ)) := by
      calc _ = ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) * (prodSigma m : ℂ)⁻¹ * (-1 - (m : ℂ)) := by ring
        _ = _ := by rw [hqr]
    rw [hqp, hqr, hpa, hra]
    field_simp [hσ_ne]
    calc (p : ℂ) * ((p : ℂ) * (1 - (m : ℂ)) * 2 - ((p : ℂ) * (1 - (m : ℂ)) + (r : ℂ) * (-1 - (m : ℂ)))) +
        (r : ℂ) * ((r : ℂ) * (-1 - (m : ℂ)) * 2 - ((p : ℂ) * (1 - (m : ℂ)) + (r : ℂ) * (-1 - (m : ℂ))))
        = (p : ℂ) * (p : ℂ) * (1 - (m : ℂ)) - (r : ℂ) * (r : ℂ) * (1 + (m : ℂ)) +
          2 * (p : ℂ) * (r : ℂ) * (m : ℂ) := by ring
      _ = ((1 + (m : ℂ)) / 2) * (1 - (m : ℂ)) - ((1 - (m : ℂ)) / 2) * (1 + (m : ℂ)) +
          (prodSigma m : ℂ) * (m : ℂ) := by rw [hp2C, hr2C, h2prC]
      _ = (prodSigma m : ℂ) * (m : ℂ) := by ring
  have h30 : singleSiteSizeForm m (gsBasis m 3) (gsBasis m 0) = (m : ℂ) / 2 := by
    simp only [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      smul_eq_mul, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add,
      mul_one, one_mul, star_zero, star_one, Complex.star_def, Complex.conj_ofReal,
      ↓reduceIte, Fin.zero_eta, Fin.mk_one, zero_ne_one, one_ne_zero, sub_self, neg_zero,
      map_mul, map_sub, map_inv₀, map_neg, map_one]
    have hpa : (Real.sqrt p : ℂ) * ((prodSigma m : ℂ)⁻¹ * (1 - (m : ℂ))) * (Real.sqrt p : ℂ) =
        (p : ℂ) * (prodSigma m : ℂ)⁻¹ * (1 - (m : ℂ)) := by
      calc _ = ((Real.sqrt p : ℂ) * (Real.sqrt p : ℂ)) * (prodSigma m : ℂ)⁻¹ * (1 - (m : ℂ)) := by ring
        _ = _ := by rw [hqp]
    have hra : (Real.sqrt r : ℂ) * ((prodSigma m : ℂ)⁻¹ * (-1 - (m : ℂ))) * (Real.sqrt r : ℂ) =
        (r : ℂ) * (prodSigma m : ℂ)⁻¹ * (-1 - (m : ℂ)) := by
      calc _ = ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) * (prodSigma m : ℂ)⁻¹ * (-1 - (m : ℂ)) := by ring
        _ = _ := by rw [hqr]
    rw [hpa, hra, hqp, hqr]
    field_simp [hσ_ne]
    calc (p : ℂ) * (1 - (m : ℂ)) * ((p : ℂ) * 2 - ((p : ℂ) + (r : ℂ))) +
        (r : ℂ) * (-1 - (m : ℂ)) * ((r : ℂ) * 2 - ((p : ℂ) + (r : ℂ)))
        = (p : ℂ) * (p : ℂ) * (1 - (m : ℂ)) - (r : ℂ) * (r : ℂ) * (1 + (m : ℂ)) +
          2 * (p : ℂ) * (r : ℂ) * (m : ℂ) := by ring
      _ = ((1 + (m : ℂ)) / 2) * (1 - (m : ℂ)) - ((1 - (m : ℂ)) / 2) * (1 + (m : ℂ)) +
          (prodSigma m : ℂ) * (m : ℂ) := by rw [hp2C, hr2C, h2prC]
      _ = (prodSigma m : ℂ) * (m : ℂ) := by ring
  fin_cases a <;> fin_cases b
  · simp [singleSiteM]
  · simp [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, singleSiteM, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · simp [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, singleSiteM, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · change singleSiteSizeForm m (gsBasis m 0) (gsBasis m 3) - 0 = ((m / 2 : ℝ) : ℂ)
    rw [sub_zero, h03]; push_cast; rfl
  · simp [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, singleSiteM, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · change singleSiteSizeForm m (gsBasis m 1) (gsBasis m 1) -
      singleSiteSizeForm m (gsBasis m 0) (gsBasis m 0) = ((1 - (prodQ m) ^ 2 / 2 : ℝ) : ℂ)
    rw [h11, h00]; push_cast; ring
  · simp [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, singleSiteM, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]; ring
  · simp [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, singleSiteM, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · simp [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, singleSiteM, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · simp [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, singleSiteM, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]; ring
  · change singleSiteSizeForm m (gsBasis m 2) (gsBasis m 2) -
      singleSiteSizeForm m (gsBasis m 0) (gsBasis m 0) = ((1 - (prodQ m) ^ 2 / 2 : ℝ) : ℂ)
    rw [h22, h00]; push_cast; ring
  · simp [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, singleSiteM, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · change singleSiteSizeForm m (gsBasis m 3) (gsBasis m 0) - 0 = ((m / 2 : ℝ) : ℂ)
    rw [sub_zero, h30]; push_cast; rfl
  · simp [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, singleSiteM, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · simp [singleSiteSizeForm, singleSiteSizeOp, singleSiteJ, singleSiteRhoQuarter,
      gsBasis, pauliMat, singleSiteM, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · change singleSiteSizeForm m (gsBasis m 3) (gsBasis m 3) -
      singleSiteSizeForm m (gsBasis m 0) (gsBasis m 0) = (prodSigma m : ℂ)
    rw [h33, h00, hq2C]; ring

end SingleSiteProductDerivation

end KrylovChaos
