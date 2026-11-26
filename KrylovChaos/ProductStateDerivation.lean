/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.WightmanIsometry
import KrylovChaos.ProductState
import KrylovChaos.DepolarizedFrame
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Concrete Product-State Gram–Schmidt Derivation (Section 4.3, Proposition 4.3)

Removes any hardcoding of `singleSiteM` by constructing from first principles for any
single-qubit magnetization `m ∈ (-1, 1)`:
1. The thermal density matrix `ρ_x(m) = (1/2)(I + m Z)` and its exact positive roots
   `ρ_x^{1/2}`, `ρ_x^{1/4}`.
2. The Gram–Schmidt Wightman orthonormal basis `{E_0, E_1, E_2, E_3}` of `M_2(ℂ)`.
3. Proof of exact Wightman orthonormality `(E_a | E_b)_{ρ_x}^W = δ_{ab}`.
4. Proof that the thermal-subtracted Hilbert–Schmidt size matrix elements
   `Re ⟨𝒥(E_a), S_x 𝒥(E_b)⟩_HS - δ_{ab} Re ⟨ρ_x^{1/2}, S_x ρ_x^{1/2}⟩_HS`
   equal `singleSiteM m a b` for all `a, b : Fin 4` (deriving Eq. 4.6).
5. Unitary invariance of `singleSiteSizeOp` under all `U ∈ U(2)`.
-/

namespace KrylovChaos

open Matrix

section SingleSiteGramSchmidt

/-- Single-qubit thermal density matrix `ρ_x(m) = (1/2)(I + m Z) = diag((1+m)/2, (1-m)/2)`. -/
noncomputable def singleSiteRho (m : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(((1 + m) / 2 : ℝ) : ℂ), 0; 0, (((1 - m) / 2 : ℝ) : ℂ)]

/-- Positive square root `ρ_x(m)^{1/2} = diag(√((1+m)/2), √((1-m)/2))`. -/
noncomputable def singleSiteRhoHalf (m : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt ((1 + m) / 2) : ℂ), 0; 0, (Real.sqrt ((1 - m) / 2) : ℂ)]

/-- Positive fourth root `ρ_x(m)^{1/4} = diag(((1+m)/2)^{1/4}, ((1-m)/2)^{1/4})`. -/
noncomputable def singleSiteRhoQuarter (m : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt (Real.sqrt ((1 + m) / 2)) : ℂ), 0; 0, (Real.sqrt (Real.sqrt ((1 - m) / 2)) : ℂ)]

/-- Single-qubit Hilbert–Schmidt size projector `S_x(B) = B - (1/2) Tr(B) I`. -/
noncomputable def singleSiteSizeOp (B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  B - ((1 / 2 : ℂ) * B.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

/-- Unitary invariance of the single-qubit Hilbert–Schmidt size quadratic form:
for any unitary `U` (`Uᴴ * U = 1`, `U * Uᴴ = 1`),
`⟨U M Uᴴ, S_x(U M Uᴴ)⟩_HS = ⟨M, S_x(M)⟩_HS`. -/
theorem singleSiteSizeOp_unitary_invariant (U M : Matrix (Fin 2) (Fin 2) ℂ)
    (hUL : Uᴴ * U = 1) (hUR : U * Uᴴ = 1) :
    hsInner (U * M * Uᴴ) (singleSiteSizeOp (U * M * Uᴴ)) =
      hsInner M (singleSiteSizeOp M) := by
  unfold hsInner singleSiteSizeOp
  have htr : Matrix.trace (U * M * Uᴴ) = Matrix.trace M := by
    calc Matrix.trace (U * M * Uᴴ)
        = Matrix.trace (Uᴴ * (U * M)) := Matrix.trace_mul_comm _ Uᴴ
      _ = Matrix.trace ((Uᴴ * U) * M) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace M := by rw [hUL, Matrix.one_mul]
  have hconj : (U * M * Uᴴ)ᴴ = U * Mᴴ * Uᴴ := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [htr, hconj]
  simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul]
  have ht1 : Matrix.trace (U * Mᴴ * Uᴴ * (U * M * Uᴴ)) = Matrix.trace (Mᴴ * M) := by
    calc Matrix.trace (U * Mᴴ * Uᴴ * (U * M * Uᴴ))
        = Matrix.trace (U * Mᴴ * (Uᴴ * U) * M * Uᴴ) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (U * (Mᴴ * M) * Uᴴ) := by rw [hUL, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Uᴴ * (U * (Mᴴ * M))) := Matrix.trace_mul_comm _ Uᴴ
      _ = Matrix.trace ((Uᴴ * U) * (Mᴴ * M)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Mᴴ * M) := by rw [hUL, Matrix.one_mul]
  have ht2 : Matrix.trace (U * Mᴴ * Uᴴ) = Matrix.trace Mᴴ := by
    calc Matrix.trace (U * Mᴴ * Uᴴ)
        = Matrix.trace (Uᴴ * (U * Mᴴ)) := Matrix.trace_mul_comm _ Uᴴ
      _ = Matrix.trace ((Uᴴ * U) * Mᴴ) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace Mᴴ := by rw [hUL, Matrix.one_mul]
  rw [ht1, ht2]

/-- Exact root identities `ρ_x^{1/2} * ρ_x^{1/2} = ρ_x` and `ρ_x^{1/4} * ρ_x^{1/4} = ρ_x^{1/2}`
for all `|m| < 1`. -/
theorem singleSiteRho_roots {m : ℝ} (hm : |m| < 1) :
    singleSiteRhoHalf m * singleSiteRhoHalf m = singleSiteRho m ∧
    singleSiteRhoQuarter m * singleSiteRhoQuarter m = singleSiteRhoHalf m := by
  have hp : 0 ≤ (1 + m) / 2 := by linarith [abs_lt.mp hm]
  have hr : 0 ≤ (1 - m) / 2 := by linarith [abs_lt.mp hm]
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [singleSiteRhoHalf, singleSiteRho, Matrix.mul_apply, Fin.sum_univ_two]
    · exact_mod_cast Real.mul_self_sqrt hp
    · exact_mod_cast Real.mul_self_sqrt hr
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [singleSiteRhoQuarter, singleSiteRhoHalf, Matrix.mul_apply, Fin.sum_univ_two]
    · exact_mod_cast Real.mul_self_sqrt (Real.sqrt_nonneg _)
    · exact_mod_cast Real.mul_self_sqrt (Real.sqrt_nonneg _)

/-- Gram–Schmidt Wightman orthonormal basis `{E_0, E_1, E_2, E_3}` of `M_2(ℂ)` for `ρ_x(m)`:
`E_0 = I`, `E_1 = σ^{-1/2} X`, `E_2 = σ^{-1/2} Y`, `E_3 = σ^{-1} (Z - m I)`
where `σ = √(1 - m²)`. -/
noncomputable def gsBasis (m : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
  | 1 => (((Real.sqrt (prodSigma m))⁻¹ : ℝ) : ℂ) • pauliX
  | 2 => (((Real.sqrt (prodSigma m))⁻¹ : ℝ) : ℂ) • pauliY
  | 3 => !![(((prodSigma m)⁻¹ * (1 - m) : ℝ) : ℂ), 0;
            0, (((prodSigma m)⁻¹ * (-1 - m) : ℝ) : ℂ)]

/-- `gsBasis m 3` equals `σ⁻¹ (Z - m I)`. -/
theorem gsBasis_three_eq (m : ℝ) :
    gsBasis m 3 = (((prodSigma m)⁻¹ : ℝ) : ℂ) • (pauliZ - (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gsBasis, pauliZ] <;> ring

/-- Exact Wightman orthonormality `(E_a | E_b)_{ρ_x}^W = δ_{ab}` for all `|m| < 1`. -/
theorem gsBasis_wightman_orthonormal {m : ℝ} (hm : |m| < 1) (a b : Fin 4) :
    wightmanInner (singleSiteRhoHalf m) (gsBasis m a) (gsBasis m b) =
      if a = b then 1 else 0 := by
  have hm1 : -1 < m ∧ m < 1 := abs_lt.mp hm
  have hp : 0 < (1 + m) / 2 := by linarith
  have hr : 0 < (1 - m) / 2 := by linarith
  have h1m2 : 0 < 1 - m ^ 2 := by nlinarith
  have hsig : 0 < prodSigma m := Real.sqrt_pos.mpr h1m2
  have hrt_sig : 0 < Real.sqrt (prodSigma m) := Real.sqrt_pos.mpr hsig
  set p := Real.sqrt ((1 + m) / 2)
  set r := Real.sqrt ((1 - m) / 2)
  have hpr : p * r = prodSigma m / 2 := by
    rw [← Real.sqrt_mul hp.le]
    have heq : (1 + m) / 2 * ((1 - m) / 2) = (1 - m ^ 2) / 4 := by ring
    rw [heq, Real.sqrt_div h1m2.le, show Real.sqrt 4 = 2 by norm_num, prodSigma]
  have hpsq : p * p = (1 + m) / 2 := Real.mul_self_sqrt hp.le
  have hrsq : r * r = (1 - m) / 2 := Real.mul_self_sqrt hr.le
  have hsigsq : prodSigma m * prodSigma m = 1 - m ^ 2 := Real.mul_self_sqrt h1m2.le
  have hrtsigsq : Real.sqrt (prodSigma m) * Real.sqrt (prodSigma m) = prodSigma m :=
    Real.mul_self_sqrt hsig.le
  have hhalf_eq : singleSiteRhoHalf m = !![(p : ℂ), 0; 0, (r : ℂ)] := rfl
  unfold wightmanInner
  rw [hhalf_eq]
  fin_cases a <;> fin_cases b <;>
    simp [gsBasis, pauliX, pauliY, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  · exact_mod_cast (by linarith [hpsq, hrsq] : p * p + r * r = 1)
  · exact_mod_cast (by
      have h : p * (p * ((prodSigma m)⁻¹ * (1 - m))) + r * (r * ((prodSigma m)⁻¹ * (-1 - m))) =
          (p * p * (1 - m) + r * r * (-1 - m)) * (prodSigma m)⁻¹ := by ring
      rw [h, hpsq, hrsq]; ring :
      p * (p * ((prodSigma m)⁻¹ * (1 - m))) + r * (r * ((prodSigma m)⁻¹ * (-1 - m))) = 0)
  · have hcalc : p * (Real.sqrt (prodSigma m))⁻¹ * r * (Real.sqrt (prodSigma m))⁻¹ +
        r * (Real.sqrt (prodSigma m))⁻¹ * p * (Real.sqrt (prodSigma m))⁻¹ = 1 := by
      have h1 : p * (Real.sqrt (prodSigma m))⁻¹ * r * (Real.sqrt (prodSigma m))⁻¹ +
          r * (Real.sqrt (prodSigma m))⁻¹ * p * (Real.sqrt (prodSigma m))⁻¹ =
          (2 * (p * r)) * ((Real.sqrt (prodSigma m))⁻¹ * (Real.sqrt (prodSigma m))⁻¹) := by ring
      rw [h1, hpr]
      field_simp [hrt_sig.ne', hsig.ne']
      linarith [hrtsigsq]
    exact_mod_cast hcalc
  · ring
  · ring
  · have hcalc : p * (Real.sqrt (prodSigma m))⁻¹ * r * (Real.sqrt (prodSigma m))⁻¹ +
        r * (Real.sqrt (prodSigma m))⁻¹ * p * (Real.sqrt (prodSigma m))⁻¹ = 1 := by
      have h1 : p * (Real.sqrt (prodSigma m))⁻¹ * r * (Real.sqrt (prodSigma m))⁻¹ +
          r * (Real.sqrt (prodSigma m))⁻¹ * p * (Real.sqrt (prodSigma m))⁻¹ =
          (2 * (p * r)) * ((Real.sqrt (prodSigma m))⁻¹ * (Real.sqrt (prodSigma m))⁻¹) := by ring
      rw [h1, hpr]
      field_simp [hrt_sig.ne', hsig.ne']
      linarith [hrtsigsq]
    have hC : ((p : ℂ) * (((Real.sqrt (prodSigma m))⁻¹ : ℝ) : ℂ) *
        (r : ℂ) * (((Real.sqrt (prodSigma m))⁻¹ : ℝ) : ℂ) +
        (r : ℂ) * (((Real.sqrt (prodSigma m))⁻¹ : ℝ) : ℂ) *
        (p : ℂ) * (((Real.sqrt (prodSigma m))⁻¹ : ℝ) : ℂ)) = 1 := by
      exact_mod_cast hcalc
    calc _ = (p : ℂ) * (((Real.sqrt (prodSigma m))⁻¹ : ℝ) : ℂ) *
              (r : ℂ) * (((Real.sqrt (prodSigma m))⁻¹ : ℝ) : ℂ) +
              (r : ℂ) * (((Real.sqrt (prodSigma m))⁻¹ : ℝ) : ℂ) *
              (p : ℂ) * (((Real.sqrt (prodSigma m))⁻¹ : ℝ) : ℂ) := by ring_nf; simp [Complex.I_sq]; ring
      _ = 1 := hC
  · exact_mod_cast (by
      have h : p * ((prodSigma m)⁻¹ * (1 - m)) * p + r * ((prodSigma m)⁻¹ * (-1 - m)) * r =
          (p * p * (1 - m) + r * r * (-1 - m)) * (prodSigma m)⁻¹ := by ring
      rw [h, hpsq, hrsq]; ring :
      p * ((prodSigma m)⁻¹ * (1 - m)) * p + r * ((prodSigma m)⁻¹ * (-1 - m)) * r = 0)
  · have hcalc : p * ((prodSigma m)⁻¹ * (1 - m)) * (p * ((prodSigma m)⁻¹ * (1 - m))) +
        r * ((prodSigma m)⁻¹ * (-1 - m)) * (r * ((prodSigma m)⁻¹ * (-1 - m))) = 1 := by
      have h1 : p * ((prodSigma m)⁻¹ * (1 - m)) * (p * ((prodSigma m)⁻¹ * (1 - m))) +
          r * ((prodSigma m)⁻¹ * (-1 - m)) * (r * ((prodSigma m)⁻¹ * (-1 - m))) =
          (p * p * (1 - m) ^ 2 + r * r * (-1 - m) ^ 2) * ((prodSigma m)⁻¹ * (prodSigma m)⁻¹) := by ring
      rw [h1, hpsq, hrsq]
      field_simp [hsig.ne']
      linarith [hsigsq]
    exact_mod_cast hcalc

/-- **Proposition 4.3 (Ground-Up Derivation of `singleSiteM`, Eq. 4.6)**:
The thermal-subtracted Hilbert–Schmidt size matrix in the Gram–Schmidt Wightman basis
`{E_0, E_1, E_2, E_3}` equals `singleSiteM m a b` for every `a, b : Fin 4` and `|m| < 1`. -/
theorem gsBasis_derives_singleSiteM {m : ℝ} (hm : |m| < 1) (a b : Fin 4) :
    (hsInner (jBeta (singleSiteRhoQuarter m) (gsBasis m a))
      (singleSiteSizeOp (jBeta (singleSiteRhoQuarter m) (gsBasis m b)))).re -
    (if a = b then (hsInner (singleSiteRhoHalf m) (singleSiteSizeOp (singleSiteRhoHalf m))).re else 0) =
    singleSiteM m a b := by
  have hm1 : -1 < m ∧ m < 1 := abs_lt.mp hm
  have hp : 0 < (1 + m) / 2 := by linarith
  have hr : 0 < (1 - m) / 2 := by linarith
  have h1m2 : 0 < 1 - m ^ 2 := by nlinarith
  have hsig : 0 < prodSigma m := Real.sqrt_pos.mpr h1m2
  set p := Real.sqrt ((1 + m) / 2)
  set r := Real.sqrt ((1 - m) / 2)
  have hp_sq : p * p = (1 + m) / 2 := Real.mul_self_sqrt hp.le
  have hr_sq : r * r = (1 - m) / 2 := Real.mul_self_sqrt hr.le
  have hpr : p * r = prodSigma m / 2 := by
    rw [← Real.sqrt_mul hp.le]
    have heq : (1 + m) / 2 * ((1 - m) / 2) = (1 - m ^ 2) / 4 := by ring
    rw [heq, Real.sqrt_div h1m2.le, show Real.sqrt 4 = 2 by norm_num, prodSigma]
  have hpq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hrq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hbg : (hsInner (singleSiteRhoHalf m) (singleSiteSizeOp (singleSiteRhoHalf m))).re =
      (prodQ m) ^ 2 / 2 := by
    unfold hsInner singleSiteSizeOp singleSiteRhoHalf prodQ
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, smul_eq_mul]
    norm_num [Complex.star_def, Complex.conj_ofReal]
    ring
  have hj0 : jBeta (singleSiteRhoQuarter m) (gsBasis m 0) = singleSiteRhoHalf m := by
    unfold jBeta gsBasis
    rw [Matrix.mul_one]
    exact (singleSiteRho_roots hm).2
  have hj3 : jBeta (singleSiteRhoQuarter m) (gsBasis m 3) = !![(r : ℂ), 0; 0, -(p : ℂ)] := by
    have hq_eq : singleSiteRhoQuarter m = !![(Real.sqrt p : ℂ), 0; 0, (Real.sqrt r : ℂ)] := rfl
    unfold jBeta
    rw [hq_eq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [gsBasis, Matrix.mul_apply, Fin.sum_univ_two]
    · have h1 : Real.sqrt p * ((prodSigma m)⁻¹ * (1 - m)) * Real.sqrt p = r := by
        have hmul : Real.sqrt p * ((prodSigma m)⁻¹ * (1 - m)) * Real.sqrt p =
            (Real.sqrt p * Real.sqrt p) * (1 - m) * (prodSigma m)⁻¹ := by ring
        rw [hmul, hpq, mul_inv_eq_iff_eq_mul₀ hsig.ne']
        have h2 : r * prodSigma m = 2 * r * (p * r) := by rw [hpr]; ring
        have h3 : 2 * r * (p * r) = 2 * (r * r) * p := by ring
        rw [h2, h3, hr_sq]; ring
      exact_mod_cast h1
    · have h1 : Real.sqrt r * ((prodSigma m)⁻¹ * (-1 - m)) * Real.sqrt r = -p := by
        have hmul : Real.sqrt r * ((prodSigma m)⁻¹ * (-1 - m)) * Real.sqrt r =
            (Real.sqrt r * Real.sqrt r) * (-1 - m) * (prodSigma m)⁻¹ := by ring
        rw [hmul, hrq, mul_inv_eq_iff_eq_mul₀ hsig.ne']
        have h2 : -p * prodSigma m = -2 * p * (p * r) := by rw [hpr]; ring
        have h3 : -2 * p * (p * r) = -2 * (p * p) * r := by ring
        rw [h2, h3, hp_sq]; ring
      exact_mod_cast h1
  have hinner_S : ∀ A B : Matrix (Fin 2) (Fin 2) ℂ,
      (hsInner A (singleSiteSizeOp B)).re =
        (Matrix.trace (Aᴴ * B)).re - (1 / 2 : ℝ) * (Matrix.trace Aᴴ * Matrix.trace B).re := by
    intro A B
    unfold hsInner singleSiteSizeOp
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul, Complex.sub_re]
    congr 1
    rw [mul_assoc, Complex.mul_re]
    norm_num
    ring
  have hw := fun a b ↦ gsBasis_wightman_orthonormal hm a b
  have hiso : ∀ a b : Fin 4,
      Matrix.trace ((jBeta (singleSiteRhoQuarter m) (gsBasis m a))ᴴ *
        jBeta (singleSiteRhoQuarter m) (gsBasis m b)) = if a = b then 1 else 0 := by
    intro a b
    have hq_herm : (singleSiteRhoQuarter m)ᴴ = singleSiteRhoQuarter m := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [singleSiteRhoQuarter]
    change ((wightmanIsometry (singleSiteRhoQuarter m) (gsBasis m a))ᴴ *
      wightmanIsometry (singleSiteRhoQuarter m) (gsBasis m b)).trace = if a = b then 1 else 0
    rw [prop_2_2_wightman_isometry_inner (singleSiteRhoQuarter m) (singleSiteRhoHalf m)
      (gsBasis m a) (gsBasis m b) hq_herm (singleSiteRho_roots hm).2]
    exact hw a b
  have htr0 : Matrix.trace (jBeta (singleSiteRhoQuarter m) (gsBasis m 0)) = (p + r : ℝ) := by
    rw [hj0]; simp [singleSiteRhoHalf, Matrix.trace, Matrix.diag, p, r]
  have htr3 : Matrix.trace (jBeta (singleSiteRhoQuarter m) (gsBasis m 3)) = (r - p : ℝ) := by
    rw [hj3]; simp [Matrix.trace, Matrix.diag, sub_eq_add_neg]
  have htr0h : Matrix.trace (jBeta (singleSiteRhoQuarter m) (gsBasis m 0))ᴴ = (p + r : ℝ) := by
    rw [Matrix.trace_conjTranspose, htr0]; simp [Complex.star_def, Complex.conj_ofReal]
  have htr3h : Matrix.trace (jBeta (singleSiteRhoQuarter m) (gsBasis m 3))ᴴ = (r - p : ℝ) := by
    rw [Matrix.trace_conjTranspose, htr3]; simp [Complex.star_def, Complex.conj_ofReal]
  have htr1 : Matrix.trace (jBeta (singleSiteRhoQuarter m) (gsBasis m 1)) = 0 := by
    simp [jBeta, gsBasis, singleSiteRhoQuarter, pauliX, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_two]
  have htr2 : Matrix.trace (jBeta (singleSiteRhoQuarter m) (gsBasis m 2)) = 0 := by
    simp [jBeta, gsBasis, singleSiteRhoQuarter, pauliY, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_two]
  have htr1h : Matrix.trace (jBeta (singleSiteRhoQuarter m) (gsBasis m 1))ᴴ = 0 := by
    simp [Matrix.trace_conjTranspose, htr1]
  have htr2h : Matrix.trace (jBeta (singleSiteRhoQuarter m) (gsBasis m 2))ᴴ = 0 := by
    simp [Matrix.trace_conjTranspose, htr2]
  have hq_def : prodQ m = p - r := rfl
  rw [hinner_S, hiso, hbg]
  fin_cases a <;> fin_cases b <;> dsimp only
  · rw [htr0h, htr0, hq_def]; simp [singleSiteM]; nlinarith [hp_sq, hr_sq]
  · simp [singleSiteM, htr1]
  · simp [singleSiteM, htr2]
  · rw [htr0h, htr3]; simp [singleSiteM]; nlinarith [hp_sq, hr_sq]
  · simp [singleSiteM, htr1h]
  · simp [singleSiteM, htr1]
  · simp [singleSiteM, htr2]
  · simp [singleSiteM, htr1h]
  · simp [singleSiteM, htr2h]
  · simp [singleSiteM, htr1]
  · simp [singleSiteM, htr2]
  · simp [singleSiteM, htr2h]
  · rw [htr3h, htr0]; simp [singleSiteM]; nlinarith [hp_sq, hr_sq]
  · simp [singleSiteM, htr1]
  · simp [singleSiteM, htr2]
  · rw [htr3h, htr3, hq_def]; simp [singleSiteM]; nlinarith [hp_sq, hr_sq, hpr]

end SingleSiteGramSchmidt

end KrylovChaos
