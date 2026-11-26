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

private lemma diag_mul_diag (a b c d : ℂ) :
    (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) ℂ) * !![c, 0; 0, d] = !![a * c, 0; 0, b * d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Verification of matrix root identities `ρ_x^{1/2} ρ_x^{1/2} = ρ_x` and
`ρ_x^{1/4} ρ_x^{1/4} = ρ_x^{1/2}` for `|m| < 1`. -/
theorem singleSiteRho_roots {m : ℝ} (hm : |m| < 1) :
    singleSiteRhoHalf m * singleSiteRhoHalf m = singleSiteRho m ∧
    singleSiteRhoQuarter m * singleSiteRhoQuarter m = singleSiteRhoHalf m := by
  have hlt := abs_lt.mp hm
  have hp : 0 ≤ (1 + m) / 2 := by linarith
  have hr : 0 ≤ (1 - m) / 2 := by linarith
  have hpp : (Real.sqrt ((1 + m) / 2) : ℂ) * (Real.sqrt ((1 + m) / 2) : ℂ) =
      (((1 + m) / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp]
  have hrr : (Real.sqrt ((1 - m) / 2) : ℂ) * (Real.sqrt ((1 - m) / 2) : ℂ) =
      (((1 - m) / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]
  have hqp : (Real.sqrt (Real.sqrt ((1 + m) / 2)) : ℂ) *
      (Real.sqrt (Real.sqrt ((1 + m) / 2)) : ℂ) = (Real.sqrt ((1 + m) / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
  have hqr : (Real.sqrt (Real.sqrt ((1 - m) / 2)) : ℂ) *
      (Real.sqrt (Real.sqrt ((1 - m) / 2)) : ℂ) = (Real.sqrt ((1 - m) / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Real.sqrt_nonneg _)]
  constructor
  · unfold singleSiteRhoHalf singleSiteRho
    rw [diag_mul_diag, hpp, hrr]
  · unfold singleSiteRhoQuarter singleSiteRhoHalf
    rw [diag_mul_diag, hqp, hqr]

/-- Wightman Gram–Schmidt orthonormal basis `{E_0, E_1, E_2, E_3}` for `ρ_x = (I + m Z)/2`. -/
noncomputable def gsBasis (m : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => !![0, ((Real.sqrt (prodSigma m))⁻¹ : ℂ); ((Real.sqrt (prodSigma m))⁻¹ : ℂ), 0]
  | 2 => !![0, (-Complex.I * ((Real.sqrt (prodSigma m))⁻¹ : ℂ));
            (Complex.I * ((Real.sqrt (prodSigma m))⁻¹ : ℂ)), 0]
  | 3 => !![((prodSigma m)⁻¹ * (1 - m) : ℂ), 0; 0, ((prodSigma m)⁻¹ * (-1 - m) : ℂ)]

/-- Verification that `gsBasis m 3 = σ(m)⁻¹ (Z - m I)`. -/
theorem gsBasis_three_eq (m : ℝ) :
    gsBasis m 3 = ((prodSigma m)⁻¹ : ℂ) • (pauliMat 3 - (m : ℂ) • pauliMat 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gsBasis, pauliMat]

/-- Every Gram–Schmidt basis element is Hermitian: `(E_a)ᴴ = E_a`. -/
theorem gsBasis_herm (m : ℝ) (a : Fin 4) : (gsBasis m a)ᴴ = gsBasis m a := by
  fin_cases a <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gsBasis, Matrix.conjTranspose_apply, Complex.star_def]

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

private lemma diag_wightman_inner (p r : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (!![p, 0; 0, r] * Aᴴ * !![p, 0; 0, r] * B).trace =
    p ^ 2 * star (A 0 0) * B 0 0 +
    p * r * (star (A 1 0) * B 1 0 + star (A 0 1) * B 0 1) +
    r ^ 2 * star (A 1 1) * B 1 1 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add]
  ring

private lemma diag_size_form (a b : ℂ) (ha : star a = a) (hb : star b = b)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    ((!![a, 0; 0, b] * A * !![a, 0; 0, b])ᴴ *
      singleSiteSizeOp (!![a, 0; 0, b] * B * !![a, 0; 0, b])).trace =
    (1 / 2 : ℂ) * (a ^ 2 * star (A 0 0) - b ^ 2 * star (A 1 1)) *
      (a ^ 2 * B 0 0 - b ^ 2 * B 1 1) +
    a ^ 2 * b ^ 2 * (star (A 1 0) * B 1 0 + star (A 0 1) * B 0 1) := by
  simp only [singleSiteSizeOp, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    smul_eq_mul, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, zero_mul, add_zero, zero_add,
    mul_one, one_mul, star_zero, star_mul', ha, hb, ↓reduceIte, Fin.zero_eta, Fin.mk_one,
    zero_ne_one, one_ne_zero]
  ring

/-- **Gram–Schmidt Wightman Orthonormality**:
`(E_a | E_b)_{ρ_x}^W = δ_{ab}` for all `a, b : Fin 4` and `|m| < 1`. -/
theorem gsBasis_wightman_orthonormal {m : ℝ} (hm : |m| < 1) (a b : Fin 4) :
    singleSiteWightmanInner m (gsBasis m a) (gsBasis m b) = if a = b then 1 else 0 := by
  obtain ⟨hp, hr, hσ, hp2, hr2, h2pr, _⟩ := prod_param_identities hm
  set p : ℂ := (Real.sqrt ((1 + m) / 2) : ℂ)
  set r : ℂ := (Real.sqrt ((1 - m) / 2) : ℂ)
  set σ : ℂ := (prodSigma m : ℂ)
  set sσ : ℂ := (Real.sqrt (prodSigma m) : ℂ)
  have hσ_ne : σ ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  have hsσ_ne : sσ ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hσ).ne'
  have hsσ2 : sσ ^ 2 = σ := by
    change ((Real.sqrt (prodSigma m) : ℝ) : ℂ) ^ 2 = ((prodSigma m : ℝ) : ℂ)
    rw [← Complex.ofReal_pow, Real.sq_sqrt hσ.le]
  have hσ2 : σ ^ 2 = 1 - (m : ℂ) ^ 2 := by
    change ((prodSigma m : ℝ) : ℂ) ^ 2 = 1 - (m : ℂ) ^ 2
    rw [← Complex.ofReal_pow, show (prodSigma m) ^ 2 = 1 - m ^ 2 from
      Real.sq_sqrt (by nlinarith [abs_lt.mp hm])]
    push_cast; rfl
  have h2prC : 2 * p * r = σ := by
    change 2 * ((Real.sqrt ((1 + m) / 2) : ℝ) : ℂ) * ((Real.sqrt ((1 - m) / 2) : ℝ) : ℂ) =
      ((prodSigma m : ℝ) : ℂ)
    rw [← h2pr]; push_cast; rfl
  have hp2C : p ^ 2 = (1 + (m : ℂ)) / 2 := by
    change ((Real.sqrt ((1 + m) / 2) : ℝ) : ℂ) ^ 2 = (1 + (m : ℂ)) / 2
    rw [← Complex.ofReal_pow, hp2]; push_cast; rfl
  have hr2C : r ^ 2 = (1 - (m : ℂ)) / 2 := by
    change ((Real.sqrt ((1 - m) / 2) : ℝ) : ℂ) ^ 2 = (1 - (m : ℂ)) / 2
    rw [← Complex.ofReal_pow, hr2]; push_cast; rfl
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hhalf : singleSiteRhoHalf m = !![p, 0; 0, r] := rfl
  unfold singleSiteWightmanInner
  rw [hhalf, diag_wightman_inner]
  match a, b with
  | 0, 0 =>
    rw [if_pos rfl]
    simp only [gsBasis, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, star_zero, star_one, mul_zero, zero_mul,
      add_zero, zero_add, mul_one, one_mul]
    linear_combination hp2C + hr2C
  | 0, 1 => rw [if_neg (by decide)]; simp [gsBasis]
  | 0, 2 => rw [if_neg (by decide)]; simp [gsBasis]
  | 0, 3 =>
    rw [if_neg (by decide)]
    simp only [gsBasis, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, star_zero, star_one, mul_zero, zero_mul,
      add_zero, zero_add, mul_one, one_mul, Complex.ofReal_inv]
    change p ^ 2 * (σ⁻¹ * (1 - (m : ℂ))) + r ^ 2 * (σ⁻¹ * (-1 - (m : ℂ))) = 0
    field_simp [hσ_ne]; linear_combination (1 - (m : ℂ)) * hp2C + (-1 - (m : ℂ)) * hr2C
  | 1, 0 => rw [if_neg (by decide)]; simp [gsBasis]
  | 1, 1 =>
    rw [if_pos rfl]
    simp only [gsBasis, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, star_zero, star_inv₀, Complex.star_def,
      Complex.conj_ofReal, mul_zero, zero_mul, add_zero, zero_add, Complex.ofReal_inv]
    change p * r * (sσ⁻¹ * sσ⁻¹ + sσ⁻¹ * sσ⁻¹) = 1
    field_simp [hsσ_ne]; rw [hsσ2]; linear_combination h2prC
  | 1, 2 =>
    rw [if_neg (by decide)]
    simp only [gsBasis, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, star_zero, star_inv₀, Complex.star_def,
      Complex.conj_ofReal, mul_zero, zero_mul, add_zero, zero_add, Complex.ofReal_inv]
    ring
  | 1, 3 => rw [if_neg (by decide)]; simp [gsBasis]
  | 2, 0 => rw [if_neg (by decide)]; simp [gsBasis]
  | 2, 1 =>
    rw [if_neg (by decide)]
    simp only [gsBasis, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, star_zero, star_mul', star_inv₀, star_neg,
      Complex.star_def, Complex.conj_I, Complex.conj_ofReal, mul_zero, zero_mul, add_zero,
      zero_add, neg_neg, Complex.ofReal_inv]
    ring
  | 2, 2 =>
    rw [if_pos rfl]
    simp only [gsBasis, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, star_zero, star_mul', star_inv₀, star_neg,
      Complex.star_def, Complex.conj_I, Complex.conj_ofReal, mul_zero, zero_mul, add_zero,
      zero_add, neg_neg, Complex.ofReal_inv]
    change p * r * (-Complex.I * sσ⁻¹ * (Complex.I * sσ⁻¹) +
      Complex.I * sσ⁻¹ * (-Complex.I * sσ⁻¹)) = 1
    field_simp [hsσ_ne]; rw [hsσ2]
    linear_combination -2 * p * r * hII + h2prC
  | 2, 3 => rw [if_neg (by decide)]; simp [gsBasis]
  | 3, 0 =>
    rw [if_neg (by decide)]
    simp only [gsBasis, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, star_zero, star_one, star_mul', star_inv₀,
      star_sub, star_neg, Complex.star_def, Complex.conj_ofReal, map_one, mul_zero, zero_mul,
      add_zero, zero_add, mul_one, one_mul, Complex.ofReal_inv]
    change p ^ 2 * (σ⁻¹ * (1 - (m : ℂ))) + r ^ 2 * (σ⁻¹ * (-1 - (m : ℂ))) = 0
    field_simp [hσ_ne]; linear_combination (1 - (m : ℂ)) * hp2C + (-1 - (m : ℂ)) * hr2C
  | 3, 1 => rw [if_neg (by decide)]; simp [gsBasis]
  | 3, 2 => rw [if_neg (by decide)]; simp [gsBasis]
  | 3, 3 =>
    rw [if_pos rfl]
    simp only [gsBasis, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, star_zero, star_mul', star_inv₀, star_sub,
      star_neg, Complex.star_def, Complex.conj_ofReal, map_one, mul_zero, zero_mul, add_zero,
      zero_add, Complex.ofReal_inv]
    change p ^ 2 * (σ⁻¹ * (1 - (m : ℂ))) * (σ⁻¹ * (1 - (m : ℂ))) +
      r ^ 2 * (σ⁻¹ * (-1 - (m : ℂ))) * (σ⁻¹ * (-1 - (m : ℂ))) = 1
    field_simp [hσ_ne]
    linear_combination (1 - (m : ℂ)) ^ 2 * hp2C + (-1 - (m : ℂ)) ^ 2 * hr2C - hσ2

/-- **Ground-Up Derivation of Eq. (4.6) (`singleSiteM`)**:
For every `|m| < 1` and every `a, b : Fin 4`, the thermal-subtracted single-site
size matrix element in the Wightman Gram–Schmidt basis `{E_0, E_1, E_2, E_3}` equals
`singleSiteM m a b` identically. -/
theorem gsBasis_derives_singleSiteM {m : ℝ} (hm : |m| < 1) (a b : Fin 4) :
    singleSiteSizeForm m (gsBasis m a) (gsBasis m b) -
      (if a = b then singleSiteSizeForm m (gsBasis m 0) (gsBasis m 0) else 0) =
    (singleSiteM m a b : ℂ) := by
  obtain ⟨hp, hr, hσ, hp2, hr2, h2pr, hq2⟩ := prod_param_identities hm
  set p : ℂ := (Real.sqrt ((1 + m) / 2) : ℂ)
  set r : ℂ := (Real.sqrt ((1 - m) / 2) : ℂ)
  set qp : ℂ := (Real.sqrt (Real.sqrt ((1 + m) / 2)) : ℂ)
  set qr : ℂ := (Real.sqrt (Real.sqrt ((1 - m) / 2)) : ℂ)
  set σ : ℂ := (prodSigma m : ℂ)
  set sσ : ℂ := (Real.sqrt (prodSigma m) : ℂ)
  have hσ_ne : σ ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
  have hsσ_ne : sσ ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hσ).ne'
  have hsσ2 : sσ ^ 2 = σ := by
    change ((Real.sqrt (prodSigma m) : ℝ) : ℂ) ^ 2 = ((prodSigma m : ℝ) : ℂ)
    rw [← Complex.ofReal_pow, Real.sq_sqrt hσ.le]
  have hσ2 : σ ^ 2 = 1 - (m : ℂ) ^ 2 := by
    change ((prodSigma m : ℝ) : ℂ) ^ 2 = 1 - (m : ℂ) ^ 2
    rw [← Complex.ofReal_pow, show (prodSigma m) ^ 2 = 1 - m ^ 2 from
      Real.sq_sqrt (by nlinarith [abs_lt.mp hm])]
    push_cast; rfl
  have h2prC : 2 * p * r = σ := by
    change 2 * ((Real.sqrt ((1 + m) / 2) : ℝ) : ℂ) * ((Real.sqrt ((1 - m) / 2) : ℝ) : ℂ) =
      ((prodSigma m : ℝ) : ℂ)
    rw [← h2pr]; push_cast; rfl
  have hp2C : p ^ 2 = (1 + (m : ℂ)) / 2 := by
    change ((Real.sqrt ((1 + m) / 2) : ℝ) : ℂ) ^ 2 = (1 + (m : ℂ)) / 2
    rw [← Complex.ofReal_pow, hp2]; push_cast; rfl
  have hr2C : r ^ 2 = (1 - (m : ℂ)) / 2 := by
    change ((Real.sqrt ((1 - m) / 2) : ℝ) : ℂ) ^ 2 = (1 - (m : ℂ)) / 2
    rw [← Complex.ofReal_pow, hr2]; push_cast; rfl
  have hqp2 : qp ^ 2 = p := by
    change ((Real.sqrt (Real.sqrt ((1 + m) / 2)) : ℝ) : ℂ) ^ 2 =
      ((Real.sqrt ((1 + m) / 2) : ℝ) : ℂ)
    rw [← Complex.ofReal_pow, Real.sq_sqrt hp.le]
  have hqr2 : qr ^ 2 = r := by
    change ((Real.sqrt (Real.sqrt ((1 - m) / 2)) : ℝ) : ℂ) ^ 2 =
      ((Real.sqrt ((1 - m) / 2) : ℝ) : ℂ)
    rw [← Complex.ofReal_pow, Real.sq_sqrt hr.le]
  have hq2C : ((prodQ m : ℂ) ^ 2) = 1 - σ := by
    change ((prodQ m : ℝ) : ℂ) ^ 2 = 1 - ((prodSigma m : ℝ) : ℂ)
    rw [← Complex.ofReal_pow, hq2]; push_cast; rfl
  have hstar_qp : star qp = qp := by simp [qp, Complex.star_def]
  have hstar_qr : star qr = qr := by simp [qr, Complex.star_def]
  have hquar : singleSiteRhoQuarter m = !![qp, 0; 0, qr] := rfl
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hsimp_eval : ∀ x y : Fin 4,
      singleSiteSizeForm m (gsBasis m x) (gsBasis m y) =
      (1 / 2 : ℂ) * (p * star ((gsBasis m x) 0 0) - r * star ((gsBasis m x) 1 1)) *
        (p * (gsBasis m y) 0 0 - r * (gsBasis m y) 1 1) +
      p * r * (star ((gsBasis m x) 1 0) * (gsBasis m y) 1 0 +
        star ((gsBasis m x) 0 1) * (gsBasis m y) 0 1) := by
    intro x y
    unfold singleSiteSizeForm singleSiteJ
    rw [hquar, diag_size_form qp qr hstar_qp hstar_qr, hqp2, hqr2]
  match a, b with
  | 0, 0 => simp [singleSiteM]
  | 0, 1 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp [gsBasis, singleSiteM]
  | 0, 2 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp [gsBasis, singleSiteM]
  | 0, 3 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp only [gsBasis, singleSiteM, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      star_zero, star_one, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul,
      Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_inv]
    change 1 / 2 * (p - r) * (p * (σ⁻¹ * (1 - (m : ℂ))) - r * (σ⁻¹ * (-1 - (m : ℂ)))) = (m : ℂ) / 2
    field_simp [hσ_ne]
    linear_combination (1 - (m : ℂ)) * hp2C - (1 + (m : ℂ)) * hr2C + (m : ℂ) * h2prC
  | 1, 0 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp [gsBasis, singleSiteM]
  | 1, 1 =>
    rw [if_pos rfl, hsimp_eval, hsimp_eval]
    simp only [gsBasis, singleSiteM, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      star_zero, star_one, star_inv₀, Complex.star_def, Complex.conj_ofReal,
      mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul, sub_zero,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_ofNat, Complex.ofReal_inv]
    change p * r * (sσ⁻¹ * sσ⁻¹ + sσ⁻¹ * sσ⁻¹) - 1 / 2 * (p - r) * (p - r) =
      1 - (prodQ m : ℂ) ^ 2 / 2
    rw [hq2C]
    field_simp [hsσ_ne]; rw [hsσ2]
    linear_combination (2 + σ) * h2prC - σ * hp2C - σ * hr2C
  | 1, 2 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp only [gsBasis, singleSiteM, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      star_zero, star_inv₀, Complex.star_def, Complex.conj_ofReal,
      mul_zero, zero_mul, add_zero, zero_add, sub_self, Complex.ofReal_zero]
    ring
  | 1, 3 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp [gsBasis, singleSiteM]
  | 2, 0 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp [gsBasis, singleSiteM]
  | 2, 1 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp only [gsBasis, singleSiteM, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      star_zero, star_mul', star_inv₀, star_neg, Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal, mul_zero, zero_mul, add_zero, zero_add, sub_self, neg_neg,
      Complex.ofReal_zero]
    ring
  | 2, 2 =>
    rw [if_pos rfl, hsimp_eval, hsimp_eval]
    simp only [gsBasis, singleSiteM, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      star_zero, star_one, star_mul', star_inv₀, star_neg, Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul,
      sub_zero, neg_neg, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_inv]
    change p * r * (-Complex.I * sσ⁻¹ * (Complex.I * sσ⁻¹) +
        Complex.I * sσ⁻¹ * (-Complex.I * sσ⁻¹)) - 1 / 2 * (p - r) * (p - r) =
      1 - (prodQ m : ℂ) ^ 2 / 2
    rw [hq2C]
    field_simp [hsσ_ne]; rw [hsσ2]
    linear_combination -4 * p * r * hII + (2 + σ) * h2prC - σ * hp2C - σ * hr2C
  | 2, 3 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp [gsBasis, singleSiteM]
  | 3, 0 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp only [gsBasis, singleSiteM, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      star_zero, star_one, star_mul', star_inv₀, star_sub, star_neg, Complex.star_def,
      Complex.conj_ofReal, map_one, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul,
      Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_inv]
    change 1 / 2 * (p * (σ⁻¹ * (1 - (m : ℂ))) - r * (σ⁻¹ * (-1 - (m : ℂ)))) * (p - r) = (m : ℂ) / 2
    field_simp [hσ_ne]
    linear_combination (1 - (m : ℂ)) * hp2C - (1 + (m : ℂ)) * hr2C + (m : ℂ) * h2prC
  | 3, 1 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp [gsBasis, singleSiteM]
  | 3, 2 =>
    rw [if_neg (by decide), sub_zero, hsimp_eval]
    simp [gsBasis, singleSiteM]
  | 3, 3 =>
    rw [if_pos rfl, hsimp_eval, hsimp_eval]
    simp only [gsBasis, singleSiteM, Fin.isValue, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      star_zero, star_one, star_mul', star_inv₀, star_sub, star_neg, Complex.star_def,
      Complex.conj_ofReal, map_one, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul,
      Complex.ofReal_inv]
    change 1 / 2 * (p * (σ⁻¹ * (1 - (m : ℂ))) - r * (σ⁻¹ * (-1 - (m : ℂ)))) *
      (p * (σ⁻¹ * (1 - (m : ℂ))) - r * (σ⁻¹ * (-1 - (m : ℂ)))) -
      1 / 2 * (p - r) * (p - r) = σ
    field_simp [hσ_ne]
    linear_combination
      ((1 - (m : ℂ)) ^ 2 - σ ^ 2) * hp2C +
      ((1 + (m : ℂ)) ^ 2 - σ ^ 2) * hr2C +
      ((1 - (m : ℂ) ^ 2) + σ ^ 2) * h2prC -
      (1 + σ) * hσ2

end SingleSiteProductDerivation

end KrylovChaos
