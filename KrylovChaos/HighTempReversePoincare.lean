/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.HighTempConditioning
import Mathlib.Tactic

/-!
# Operator-Level Lemma 7.3(3), Theorem 1.3(a) & Theorem 1.3(b) (Flaws #2, #3)

Builds on `HighTempConditioning` to prove directly on `QubitOp N`:
1. **Product Orthonormal Basis `prodDepolBasis s s'`** via 4-step Gram–Schmidt on `Mat2`.
2. **Lemma 7.3(3) (`lemma_7_3_operator_filtration_identity`)**: Exact filtration identity on `QubitOp N`.
3. **Theorem 1.3(a) (`theorem_1_3a_concrete_operator`)**:
   `Re (A | 𝒬̃^{(β)} A)_β^W ≤ ∑ x, ‖𝒮_x(A)‖_{β,W}² ≤ 9 * Re (A | 𝒬^{(β)} A)_β^W`.
4. **Theorem 1.3(b) (`theorem_1_3b_concrete_CW`)**:
   `otocCW G A ≤ 54 * Re (A | 𝒬^{(β)} A)_β^W`.
-/

namespace KrylovChaos

open Matrix

section ProductBasisAndFiltrationIdentity

/-- Single-qubit depolarized inner product `⟨X, Y⟩_{u,v} = Tr(P̃_u Xᴴ P̃_v Y)`. -/
noncomputable def singleDepolInner (u v : Fin 6) (X Y : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  Matrix.trace (depolP u * Xᴴ * depolP v * Y)

lemma singleDepolInner_eq_hs (u v : Fin 6) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    singleDepolInner u v X Y =
      hsInner (depolPHalf v * X * depolPHalf u) (depolPHalf v * Y * depolPHalf u) := by
  unfold singleDepolInner hsInner
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, depolPHalf_herm, depolPHalf_herm]
  calc (depolP u * Xᴴ * depolP v * Y).trace
      = (depolPHalf u * (depolPHalf u * Xᴴ * (depolPHalf v * depolPHalf v) * Y)).trace := by
          rw [← depolPHalf_sq u, ← depolPHalf_sq v]; simp only [Matrix.mul_assoc]
    _ = ((depolPHalf u * Xᴴ * (depolPHalf v * depolPHalf v) * Y) * depolPHalf u).trace :=
          Matrix.trace_mul_comm _ _
    _ = (depolPHalf u * (Xᴴ * depolPHalf v) * (depolPHalf v * Y * depolPHalf u)).trace := by
          simp only [Matrix.mul_assoc]

lemma singleDepolInner_conj (u v : Fin 6) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    singleDepolInner u v Y X = star (singleDepolInner u v X Y) := by
  rw [singleDepolInner_eq_hs, singleDepolInner_eq_hs]
  unfold hsInner
  rw [← Matrix.trace_conjTranspose]
  congr 1
  symm
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

lemma singleDepolInner_add_right (u v : Fin 6) (X Y Z : Matrix (Fin 2) (Fin 2) ℂ) :
    singleDepolInner u v X (Y + Z) = singleDepolInner u v X Y + singleDepolInner u v X Z := by
  unfold singleDepolInner; rw [Matrix.mul_add, Matrix.trace_add]

lemma singleDepolInner_sub_right (u v : Fin 6) (X Y Z : Matrix (Fin 2) (Fin 2) ℂ) :
    singleDepolInner u v X (Y - Z) = singleDepolInner u v X Y - singleDepolInner u v X Z := by
  unfold singleDepolInner; rw [Matrix.mul_sub, Matrix.trace_sub]

lemma singleDepolInner_smul_right (u v : Fin 6) (c : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    singleDepolInner u v X (c • Y) = c * singleDepolInner u v X Y := by
  unfold singleDepolInner; rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

lemma singleDepolInner_add_left (u v : Fin 6) (X Y Z : Matrix (Fin 2) (Fin 2) ℂ) :
    singleDepolInner u v (X + Y) Z = singleDepolInner u v X Z + singleDepolInner u v Y Z := by
  unfold singleDepolInner
  rw [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.trace_add]

lemma singleDepolInner_sub_left (u v : Fin 6) (X Y Z : Matrix (Fin 2) (Fin 2) ℂ) :
    singleDepolInner u v (X - Y) Z = singleDepolInner u v X Z - singleDepolInner u v Y Z := by
  unfold singleDepolInner
  rw [Matrix.conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.trace_sub]

lemma singleDepolInner_smul_left (u v : Fin 6) (c : ℂ) (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
    singleDepolInner u v (c • X) Y = star c * singleDepolInner u v X Y := by
  unfold singleDepolInner
  rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul]

lemma singleDepolInner_self_im (u v : Fin 6) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (singleDepolInner u v X X).im = 0 := by
  have h := singleDepolInner_conj u v X X
  have him := congrArg Complex.im h
  simp [Complex.star_def] at him
  linarith

lemma singleDepolInner_self_eq_re (u v : Fin 6) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    singleDepolInner u v X X = ((singleDepolInner u v X X).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [singleDepolInner_self_im]

lemma singleDepolInner_self_pos (u v : Fin 6) {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X ≠ 0) :
    0 < (singleDepolInner u v X X).re := by
  rw [singleDepolInner_eq_hs]
  set M := depolPHalf v * X * depolPHalf u
  have hM : M ≠ 0 := by
    intro h0
    apply hX
    have hmul : depolPHalfInv v * M * depolPHalfInv u = 0 := by simp [h0]
    have hinv : depolPHalfInv v * M * depolPHalfInv u = X := by
      simp only [M]
      calc depolPHalfInv v * (depolPHalf v * X * depolPHalf u) * depolPHalfInv u
          = (depolPHalfInv v * depolPHalf v) * X * (depolPHalf u * depolPHalfInv u) := by
            simp only [Matrix.mul_assoc]
        _ = X := by
            rw [depolPHalfInv_mul, depolPHalf_mul_inv, Matrix.one_mul, Matrix.mul_one]
    rw [hinv] at hmul; exact hmul
  have hex : ∃ i j : Fin 2, M i j ≠ 0 := by
    by_contra hall; push Not at hall; apply hM; ext i j; exact hall i j
  rcases hex with ⟨i₀, j₀, hij⟩
  have hre : (hsInner M M).re = ∑ i : Fin 2, ∑ j : Fin 2, ‖M i j‖ ^ 2 := by
    unfold hsInner
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hre]
  have hterm : 0 < ‖M i₀ j₀‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hij)
  have hle1 : ‖M i₀ j₀‖ ^ 2 ≤ ∑ j : Fin 2, ‖M i₀ j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 2 ↦ ‖M i₀ j‖ ^ 2) (fun j _ ↦ sq_nonneg _) (Finset.mem_univ j₀)
  have hle2 : ∑ j : Fin 2, ‖M i₀ j‖ ^ 2 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖M i j‖ ^ 2 :=
    Finset.single_le_sum (f := fun i : Fin 2 ↦ ∑ j : Fin 2, ‖M i j‖ ^ 2) (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _) (Finset.mem_univ i₀)
  linarith

private lemma pauliMat_trace_mul (a b : Fin 4) :
    (pauliMat a * pauliMat b).trace = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    (simp [pauliMat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)

private lemma pauliMat_lin_indep (c : Fin 4 → ℂ)
    (h : ∑ a : Fin 4, c a • pauliMat a = 0) : ∀ a : Fin 4, c a = 0 := by
  intro a
  have htr : (pauliMat a * ∑ b : Fin 4, c b • pauliMat b).trace = 0 := by
    rw [h, Matrix.mul_zero, Matrix.trace_zero]
  rw [Matrix.mul_sum, Matrix.trace_sum] at htr
  have hsim : ∑ b : Fin 4, (pauliMat a * (c b • pauliMat b)).trace = c a * 2 := by
    have : ∀ b : Fin 4, (pauliMat a * (c b • pauliMat b)).trace =
        if a = b then c b * 2 else 0 := by
      intro b
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, pauliMat_trace_mul]
      split_ifs <;> simp
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hsim] at htr
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp htr).resolve_right h2

/-- 4-step Gram–Schmidt orthonormal basis of `Matrix (Fin 2) (Fin 2) ℂ` for `singleDepolInner u v`,
with `e₀ = c₀ • 1` (a nonzero scalar multiple of `pauliMat 0 = 1`). -/
noncomputable def singleDepolGS0 (u v : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (singleDepolInner u v (pauliMat 0) (pauliMat 0)).re)⁻¹ : ℂ) • pauliMat 0

noncomputable def singleDepolW1 (u v : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliMat 1 - singleDepolInner u v (singleDepolGS0 u v) (pauliMat 1) • singleDepolGS0 u v

noncomputable def singleDepolGS1 (u v : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (singleDepolInner u v (singleDepolW1 u v) (singleDepolW1 u v)).re)⁻¹ : ℂ) •
    singleDepolW1 u v

noncomputable def singleDepolW2 (u v : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliMat 2 -
    singleDepolInner u v (singleDepolGS0 u v) (pauliMat 2) • singleDepolGS0 u v -
    singleDepolInner u v (singleDepolGS1 u v) (pauliMat 2) • singleDepolGS1 u v

noncomputable def singleDepolGS2 (u v : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (singleDepolInner u v (singleDepolW2 u v) (singleDepolW2 u v)).re)⁻¹ : ℂ) •
    singleDepolW2 u v

noncomputable def singleDepolW3 (u v : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  pauliMat 3 -
    singleDepolInner u v (singleDepolGS0 u v) (pauliMat 3) • singleDepolGS0 u v -
    singleDepolInner u v (singleDepolGS1 u v) (pauliMat 3) • singleDepolGS1 u v -
    singleDepolInner u v (singleDepolGS2 u v) (pauliMat 3) • singleDepolGS2 u v

noncomputable def singleDepolGS3 (u v : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (singleDepolInner u v (singleDepolW3 u v) (singleDepolW3 u v)).re)⁻¹ : ℂ) •
    singleDepolW3 u v

noncomputable def singleDepolBasis (u v : Fin 6) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => singleDepolGS0 u v
  | 1 => singleDepolGS1 u v
  | 2 => singleDepolGS2 u v
  | 3 => singleDepolGS3 u v

private lemma pauliMat_ne_zero (a : Fin 4) : pauliMat a ≠ 0 := by
  intro h
  have h1 := pauliMat_lin_indep (fun b ↦ if b = a then 1 else 0) (by simp [h]) a
  simp at h1

private lemma singleDepolW1_ne_zero (u v : Fin 6) : singleDepolW1 u v ≠ 0 := by
  intro h0
  let s0 : ℂ := ((Real.sqrt (singleDepolInner u v (pauliMat 0) (pauliMat 0)).re)⁻¹ : ℂ)
  let a01 : ℂ := singleDepolInner u v (singleDepolGS0 u v) (pauliMat 1)
  have hgs0 : singleDepolGS0 u v = s0 • pauliMat 0 := rfl
  have hw1_step : singleDepolW1 u v = pauliMat 1 - a01 • singleDepolGS0 u v := rfl
  have hw1 : singleDepolW1 u v = (-a01 * s0) • pauliMat 0 + (1 : ℂ) • pauliMat 1 := by
    rw [hw1_step, hgs0]
    ext i j; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  rw [hw1] at h0
  have hlin : ∑ a : Fin 4,
      (if a = 0 then (-a01 * s0) else if a = 1 then (1 : ℂ) else 0) • pauliMat a = 0 := by
    rw [Fin.sum_univ_four]
    simpa [Fin.isValue] using h0
  have h1 := pauliMat_lin_indep _ hlin 1
  simp at h1

private lemma singleDepolW2_ne_zero (u v : Fin 6) : singleDepolW2 u v ≠ 0 := by
  intro h0
  let s0 : ℂ := ((Real.sqrt (singleDepolInner u v (pauliMat 0) (pauliMat 0)).re)⁻¹ : ℂ)
  let s1 : ℂ := ((Real.sqrt (singleDepolInner u v (singleDepolW1 u v) (singleDepolW1 u v)).re)⁻¹ : ℂ)
  let a01 : ℂ := singleDepolInner u v (singleDepolGS0 u v) (pauliMat 1)
  let a02 : ℂ := singleDepolInner u v (singleDepolGS0 u v) (pauliMat 2)
  let a12 : ℂ := singleDepolInner u v (singleDepolGS1 u v) (pauliMat 2)
  have hgs0 : singleDepolGS0 u v = s0 • pauliMat 0 := rfl
  have hgs1_step : singleDepolGS1 u v = s1 • (pauliMat 1 - a01 • singleDepolGS0 u v) := rfl
  have hgs1 : singleDepolGS1 u v = (-(s1 * a01 * s0)) • pauliMat 0 + s1 • pauliMat 1 := by
    rw [hgs1_step, hgs0]
    ext i j; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  have hw2_step : singleDepolW2 u v = pauliMat 2 - a02 • singleDepolGS0 u v - a12 • singleDepolGS1 u v := rfl
  have hw2 : singleDepolW2 u v =
      (-a02 * s0 + a12 * s1 * a01 * s0) • pauliMat 0 +
      (-a12 * s1) • pauliMat 1 +
      (1 : ℂ) • pauliMat 2 := by
    rw [hw2_step, hgs0, hgs1]
    ext i j; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  rw [hw2] at h0
  have hlin : ∑ a : Fin 4,
      (if a = 0 then (-a02 * s0 + a12 * s1 * a01 * s0)
       else if a = 1 then (-a12 * s1)
       else if a = 2 then (1 : ℂ)
       else 0) • pauliMat a = 0 := by
    rw [Fin.sum_univ_four]
    simpa [Fin.isValue] using h0
  have h2 := pauliMat_lin_indep _ hlin 2
  simp at h2

private lemma singleDepolW3_ne_zero (u v : Fin 6) : singleDepolW3 u v ≠ 0 := by
  intro h0
  have hspan : ∃ c0 c1 c2 : ℂ,
      singleDepolW3 u v = c0 • pauliMat 0 + c1 • pauliMat 1 + c2 • pauliMat 2 + (1 : ℂ) • pauliMat 3 := by
    let s0 : ℂ := ((Real.sqrt (singleDepolInner u v (pauliMat 0) (pauliMat 0)).re)⁻¹ : ℂ)
    let s1 : ℂ := ((Real.sqrt (singleDepolInner u v (singleDepolW1 u v) (singleDepolW1 u v)).re)⁻¹ : ℂ)
    let s2 : ℂ := ((Real.sqrt (singleDepolInner u v (singleDepolW2 u v) (singleDepolW2 u v)).re)⁻¹ : ℂ)
    have h0' : ∃ a0 : ℂ, singleDepolGS0 u v = a0 • pauliMat 0 := ⟨s0, rfl⟩
    rcases h0' with ⟨a0, ha0⟩
    have h1' : ∃ b0 b1 : ℂ, singleDepolGS1 u v = b0 • pauliMat 0 + b1 • pauliMat 1 := by
      let w0 := singleDepolInner u v (singleDepolGS0 u v) (pauliMat 1)
      refine ⟨-(s1 * w0 * a0), s1, ?_⟩
      have hstep : singleDepolGS1 u v = s1 • (pauliMat 1 - w0 • singleDepolGS0 u v) := rfl
      rw [hstep, ha0]
      ext i j; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rcases h1' with ⟨b0, b1, hb⟩
    have h2' : ∃ d0 d1 d2 : ℂ, singleDepolGS2 u v = d0 • pauliMat 0 + d1 • pauliMat 1 + d2 • pauliMat 2 := by
      let u0 := singleDepolInner u v (singleDepolGS0 u v) (pauliMat 2)
      let u1 := singleDepolInner u v (singleDepolGS1 u v) (pauliMat 2)
      refine ⟨s2 * (-u0 * a0 - u1 * b0), s2 * (-u1 * b1), s2, ?_⟩
      have hstep : singleDepolGS2 u v = s2 • (pauliMat 2 - u0 • singleDepolGS0 u v - u1 • singleDepolGS1 u v) := rfl
      rw [hstep, ha0, hb]
      ext i j; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rcases h2' with ⟨d0, d1, d2, hd⟩
    let v0 := singleDepolInner u v (singleDepolGS0 u v) (pauliMat 3)
    let v1 := singleDepolInner u v (singleDepolGS1 u v) (pauliMat 3)
    let v2 := singleDepolInner u v (singleDepolGS2 u v) (pauliMat 3)
    refine ⟨-v0 * a0 - v1 * b0 - v2 * d0, -v1 * b1 - v2 * d1, -v2 * d2, ?_⟩
    have hstep : singleDepolW3 u v = pauliMat 3 - v0 • singleDepolGS0 u v - v1 • singleDepolGS1 u v - v2 • singleDepolGS2 u v := rfl
    rw [hstep, ha0, hb, hd]
    ext i j; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  rcases hspan with ⟨c0, c1, c2, hw3⟩
  rw [hw3] at h0
  have hlin : ∑ a : Fin 4,
      (if a = 0 then c0 else if a = 1 then c1 else if a = 2 then c2 else 1) • pauliMat a = 0 := by
    rw [Fin.sum_univ_four]
    simpa [Fin.isValue] using h0
  have h3 := pauliMat_lin_indep _ hlin 3
  simp at h3

private lemma singleDepol_norm_unit (u v : Fin 6) {W : Matrix (Fin 2) (Fin 2) ℂ} (hW : W ≠ 0) :
    singleDepolInner u v
      (((Real.sqrt (singleDepolInner u v W W).re)⁻¹ : ℂ) • W)
      (((Real.sqrt (singleDepolInner u v W W).re)⁻¹ : ℂ) • W) = 1 := by
  have hpos := singleDepolInner_self_pos u v hW
  set r : ℝ := (singleDepolInner u v W W).re
  have heq : singleDepolInner u v W W = (r : ℂ) := singleDepolInner_self_eq_re u v W
  rw [singleDepolInner_smul_left, singleDepolInner_smul_right, heq]
  simp only [Complex.star_def, Complex.conj_inv, Complex.conj_ofReal]
  rw [← mul_assoc, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hpos.ne')]

theorem singleDepolBasis_orthonormal (u v : Fin 6) (i j : Fin 4) :
    singleDepolInner u v (singleDepolBasis u v i) (singleDepolBasis u v j) =
      if i = j then 1 else 0 := by
  have h00 : singleDepolInner u v (singleDepolGS0 u v) (singleDepolGS0 u v) = 1 :=
    singleDepol_norm_unit u v (pauliMat_ne_zero 0)
  have h0w1 : singleDepolInner u v (singleDepolGS0 u v) (singleDepolW1 u v) = 0 := by
    unfold singleDepolW1
    rw [singleDepolInner_sub_right, singleDepolInner_smul_right, h00, mul_one, sub_self]
  have h01 : singleDepolInner u v (singleDepolGS0 u v) (singleDepolGS1 u v) = 0 := by
    unfold singleDepolGS1
    rw [singleDepolInner_smul_right, h0w1, mul_zero]
  have h10 : singleDepolInner u v (singleDepolGS1 u v) (singleDepolGS0 u v) = 0 := by
    rw [singleDepolInner_conj, h01, star_zero]
  have h11 : singleDepolInner u v (singleDepolGS1 u v) (singleDepolGS1 u v) = 1 :=
    singleDepol_norm_unit u v (singleDepolW1_ne_zero u v)
  have h0w2 : singleDepolInner u v (singleDepolGS0 u v) (singleDepolW2 u v) = 0 := by
    unfold singleDepolW2
    rw [singleDepolInner_sub_right, singleDepolInner_sub_right, singleDepolInner_smul_right,
      singleDepolInner_smul_right, h00, h01, mul_one, mul_zero, sub_self, sub_zero]
  have h1w2 : singleDepolInner u v (singleDepolGS1 u v) (singleDepolW2 u v) = 0 := by
    unfold singleDepolW2
    rw [singleDepolInner_sub_right, singleDepolInner_sub_right, singleDepolInner_smul_right,
      singleDepolInner_smul_right, h10, h11, mul_zero, mul_one, sub_zero, sub_self]
  have h02 : singleDepolInner u v (singleDepolGS0 u v) (singleDepolGS2 u v) = 0 := by
    unfold singleDepolGS2; rw [singleDepolInner_smul_right, h0w2, mul_zero]
  have h12 : singleDepolInner u v (singleDepolGS1 u v) (singleDepolGS2 u v) = 0 := by
    unfold singleDepolGS2; rw [singleDepolInner_smul_right, h1w2, mul_zero]
  have h20 : singleDepolInner u v (singleDepolGS2 u v) (singleDepolGS0 u v) = 0 := by
    rw [singleDepolInner_conj, h02, star_zero]
  have h21 : singleDepolInner u v (singleDepolGS2 u v) (singleDepolGS1 u v) = 0 := by
    rw [singleDepolInner_conj, h12, star_zero]
  have h22 : singleDepolInner u v (singleDepolGS2 u v) (singleDepolGS2 u v) = 1 :=
    singleDepol_norm_unit u v (singleDepolW2_ne_zero u v)
  have h0w3 : singleDepolInner u v (singleDepolGS0 u v) (singleDepolW3 u v) = 0 := by
    unfold singleDepolW3
    rw [singleDepolInner_sub_right, singleDepolInner_sub_right, singleDepolInner_sub_right,
      singleDepolInner_smul_right, singleDepolInner_smul_right, singleDepolInner_smul_right,
      h00, h01, h02, mul_one, mul_zero, mul_zero, sub_self, sub_zero, sub_zero]
  have h1w3 : singleDepolInner u v (singleDepolGS1 u v) (singleDepolW3 u v) = 0 := by
    unfold singleDepolW3
    rw [singleDepolInner_sub_right, singleDepolInner_sub_right, singleDepolInner_sub_right,
      singleDepolInner_smul_right, singleDepolInner_smul_right, singleDepolInner_smul_right,
      h10, h11, h12, mul_zero, mul_one, mul_zero, sub_zero, sub_zero, sub_self]
  have h2w3 : singleDepolInner u v (singleDepolGS2 u v) (singleDepolW3 u v) = 0 := by
    unfold singleDepolW3
    rw [singleDepolInner_sub_right, singleDepolInner_sub_right, singleDepolInner_sub_right,
      singleDepolInner_smul_right, singleDepolInner_smul_right, singleDepolInner_smul_right,
      h20, h21, h22, mul_zero, mul_zero, mul_one, sub_zero, sub_zero, sub_self]
  have h03 : singleDepolInner u v (singleDepolGS0 u v) (singleDepolGS3 u v) = 0 := by
    unfold singleDepolGS3; rw [singleDepolInner_smul_right, h0w3, mul_zero]
  have h13 : singleDepolInner u v (singleDepolGS1 u v) (singleDepolGS3 u v) = 0 := by
    unfold singleDepolGS3; rw [singleDepolInner_smul_right, h1w3, mul_zero]
  have h23 : singleDepolInner u v (singleDepolGS2 u v) (singleDepolGS3 u v) = 0 := by
    unfold singleDepolGS3; rw [singleDepolInner_smul_right, h2w3, mul_zero]
  have h30 : singleDepolInner u v (singleDepolGS3 u v) (singleDepolGS0 u v) = 0 := by
    rw [singleDepolInner_conj, h03, star_zero]
  have h31 : singleDepolInner u v (singleDepolGS3 u v) (singleDepolGS1 u v) = 0 := by
    rw [singleDepolInner_conj, h13, star_zero]
  have h32 : singleDepolInner u v (singleDepolGS3 u v) (singleDepolGS2 u v) = 0 := by
    rw [singleDepolInner_conj, h23, star_zero]
  have h33 : singleDepolInner u v (singleDepolGS3 u v) (singleDepolGS3 u v) = 1 :=
    singleDepol_norm_unit u v (singleDepolW3_ne_zero u v)
  fin_cases i <;> fin_cases j <;> simp [singleDepolBasis, h00, h01, h02, h03,
    h10, h11, h12, h13, h20, h21, h22, h23, h30, h31, h32, h33]

/-- Every `pauliMat k` is a linear combination of `singleDepolBasis u v`, with `pauliMat 0` a
multiple of `singleDepolBasis u v 0`. -/
lemma pauliMat_expand_singleDepol (u v : Fin 6) (k : Fin 4) :
    pauliMat k = ∑ i : Fin 4, singleDepolInner u v (singleDepolBasis u v i) (pauliMat k) •
      singleDepolBasis u v i := by
  have hspan : ∃ c : Fin 4 → ℂ, pauliMat k = ∑ i : Fin 4, c i • singleDepolBasis u v i := by
    have h0 : ∃ n0 : ℂ, pauliMat 0 = n0 • singleDepolGS0 u v := by
      have hpos := singleDepolInner_self_pos u v (pauliMat_ne_zero 0)
      have hsr : (Real.sqrt (singleDepolInner u v (pauliMat 0) (pauliMat 0)).re : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
      refine ⟨(Real.sqrt (singleDepolInner u v (pauliMat 0) (pauliMat 0)).re : ℂ), ?_⟩
      unfold singleDepolGS0; rw [smul_smul, mul_inv_cancel₀ hsr, one_smul]
    have h1 : ∃ n1 : ℂ, singleDepolW1 u v = n1 • singleDepolGS1 u v := by
      have hpos := singleDepolInner_self_pos u v (singleDepolW1_ne_zero u v)
      have hsr : (Real.sqrt (singleDepolInner u v (singleDepolW1 u v) (singleDepolW1 u v)).re : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
      refine ⟨(Real.sqrt (singleDepolInner u v (singleDepolW1 u v) (singleDepolW1 u v)).re : ℂ), ?_⟩
      unfold singleDepolGS1; rw [smul_smul, mul_inv_cancel₀ hsr, one_smul]
    have h2 : ∃ n2 : ℂ, singleDepolW2 u v = n2 • singleDepolGS2 u v := by
      have hpos := singleDepolInner_self_pos u v (singleDepolW2_ne_zero u v)
      have hsr : (Real.sqrt (singleDepolInner u v (singleDepolW2 u v) (singleDepolW2 u v)).re : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
      refine ⟨(Real.sqrt (singleDepolInner u v (singleDepolW2 u v) (singleDepolW2 u v)).re : ℂ), ?_⟩
      unfold singleDepolGS2; rw [smul_smul, mul_inv_cancel₀ hsr, one_smul]
    have h3 : ∃ n3 : ℂ, singleDepolW3 u v = n3 • singleDepolGS3 u v := by
      have hpos := singleDepolInner_self_pos u v (singleDepolW3_ne_zero u v)
      have hsr : (Real.sqrt (singleDepolInner u v (singleDepolW3 u v) (singleDepolW3 u v)).re : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
      refine ⟨(Real.sqrt (singleDepolInner u v (singleDepolW3 u v) (singleDepolW3 u v)).re : ℂ), ?_⟩
      unfold singleDepolGS3; rw [smul_smul, mul_inv_cancel₀ hsr, one_smul]
    rcases h0 with ⟨n0, hn0⟩; rcases h1 with ⟨n1, hn1⟩
    rcases h2 with ⟨n2, hn2⟩; rcases h3 with ⟨n3, hn3⟩
    fin_cases k
    · refine ⟨fun i ↦ if i = 0 then n0 else 0, ?_⟩
      rw [Fin.sum_univ_four]; simp [singleDepolBasis, hn0]
    · refine ⟨fun i ↦ if i = 0 then singleDepolInner u v (singleDepolGS0 u v) (pauliMat 1)
          else if i = 1 then n1 else 0, ?_⟩
      rw [Fin.sum_univ_four]; simp [singleDepolBasis]
      rw [← hn1]; unfold singleDepolW1; abel
    · refine ⟨fun i ↦ if i = 0 then singleDepolInner u v (singleDepolGS0 u v) (pauliMat 2)
          else if i = 1 then singleDepolInner u v (singleDepolGS1 u v) (pauliMat 2)
          else if i = 2 then n2 else 0, ?_⟩
      rw [Fin.sum_univ_four]; simp [singleDepolBasis]
      rw [← hn2]; unfold singleDepolW2; abel
    · refine ⟨fun i ↦ if i = 0 then singleDepolInner u v (singleDepolGS0 u v) (pauliMat 3)
          else if i = 1 then singleDepolInner u v (singleDepolGS1 u v) (pauliMat 3)
          else if i = 2 then singleDepolInner u v (singleDepolGS2 u v) (pauliMat 3)
          else n3, ?_⟩
      rw [Fin.sum_univ_four]; simp [singleDepolBasis]
      rw [← hn3]; unfold singleDepolW3; abel
  rcases hspan with ⟨c, hc⟩
  conv_lhs => rw [hc]
  apply Finset.sum_congr rfl; intro i _
  congr 1
  rw [hc]
  have hlin : singleDepolInner u v (singleDepolBasis u v i)
      (∑ j : Fin 4, c j • singleDepolBasis u v j) =
      ∑ j : Fin 4, c j * singleDepolInner u v (singleDepolBasis u v i) (singleDepolBasis u v j) := by
    unfold singleDepolInner
    rw [Matrix.mul_sum, Matrix.trace_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [hlin]
  simp [singleDepolBasis_orthonormal]

/-- Product orthonormal basis `E_a^{(s,s')} = ⨂_{x=1}^N e_{a_x}^{(s_x, s'_x)}` of `QubitOp N`
for the depolarized product inner product `prodDepolInner s s'`. -/
noncomputable def prodDepolBasis {N : ℕ} (s s' : Fin N → Fin 6) (a : Fin N → Fin 4) : QubitOp N :=
  kronOp (fun x ↦ singleDepolBasis (s x) (s' x) (a x))

theorem prodDepolBasis_orthonormal {N : ℕ} (s s' : Fin N → Fin 6) (a b : Fin N → Fin 4) :
    prodDepolInner s s' (prodDepolBasis s s' a) (prodDepolBasis s s' b) =
      if a = b then 1 else 0 := by
  unfold prodDepolInner prodDepolBasis globalDepolP
  rw [kronOp_conjTranspose, kronOp_mul, kronOp_mul, kronOp_mul, kronOp_trace]
  have hfac : ∀ x : Fin N,
      (depolP (s x) * (singleDepolBasis (s x) (s' x) (a x))ᴴ *
        depolP (s' x) * singleDepolBasis (s x) (s' x) (b x)).trace =
      if a x = b x then 1 else 0 :=
    fun x ↦ singleDepolBasis_orthonormal (s x) (s' x) (a x) (b x)
  simp_rw [hfac]
  by_cases hab : a = b
  · subst hab; simp
  · rw [if_neg hab]
    have hex : ∃ x : Fin N, a x ≠ b x := by
      by_contra hall; push Not at hall; exact hab (funext hall)
    rcases hex with ⟨x₀, hx₀⟩
    exact Finset.prod_eq_zero (Finset.mem_univ x₀) (if_neg hx₀)

private lemma kronOp_sum_expand {N : ℕ} (F : Fin N → Fin 4 → Matrix (Fin 2) (Fin 2) ℂ) :
    kronOp (fun x ↦ ∑ i : Fin 4, F x i) =
      ∑ a : Fin N → Fin 4, kronOp (fun x ↦ F x (a x)) := by
  ext p q
  simp only [kronOp, Matrix.of_apply, Matrix.sum_apply]
  rw [Fintype.prod_sum]

/-- Every `A : QubitOp N` expands uniquely in `prodDepolBasis s s'`. -/
theorem prodDepolBasis_expand {N : ℕ} (s s' : Fin N → Fin 6) (A : QubitOp N) :
    A = ∑ a : Fin N → Fin 4, prodDepolInner s s' (prodDepolBasis s s' a) A • prodDepolBasis s s' a := by
  -- First show A is in the span of prodDepolBasis s s'
  have hpauli_span : ∀ α : Fin N → Fin 4,
      ∃ c : (Fin N → Fin 4) → ℂ, pauliString α = ∑ a : Fin N → Fin 4, c a • prodDepolBasis s s' a := by
    intro α
    refine ⟨fun a ↦ ∏ x : Fin N, singleDepolInner (s x) (s' x) (singleDepolBasis (s x) (s' x) (a x)) (pauliMat (α x)), ?_⟩
    unfold pauliString
    have h1 : (fun x : Fin N ↦ pauliMat (α x)) =
        fun x ↦ ∑ i : Fin 4, singleDepolInner (s x) (s' x) (singleDepolBasis (s x) (s' x) i) (pauliMat (α x)) •
          singleDepolBasis (s x) (s' x) i := funext fun x ↦ pauliMat_expand_singleDepol (s x) (s' x) (α x)
    rw [h1, kronOp_sum_expand]
    apply Finset.sum_congr rfl; intro a _
    ext p q
    simp only [prodDepolBasis, kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.prod_mul_distrib]
  have hexp_A : ∃ c : (Fin N → Fin 4) → ℂ, A = ∑ a : Fin N → Fin 4, c a • prodDepolBasis s s' a := by
    have hA := pauli_expansion_concrete A
    choose f hf using hpauli_span
    refine ⟨fun a ↦ ∑ α : Fin N → Fin 4, ((1 / (2 : ℂ) ^ N) * (pauliString α * A).trace) * f α a, ?_⟩
    conv_lhs => rw [hA]
    simp_rw [hf, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.sum_smul]
  rcases hexp_A with ⟨c, hc⟩
  conv_lhs => rw [hc]
  apply Finset.sum_congr rfl; intro a _
  congr 1
  rw [hc]
  unfold prodDepolInner
  rw [Matrix.mul_sum, Matrix.trace_sum]
  have hterm : ∀ b : Fin N → Fin 4,
      (globalDepolP N s * (prodDepolBasis s s' a)ᴴ * globalDepolP N s' *
        (c b • prodDepolBasis s s' b)).trace =
      if a = b then c b else 0 := by
    intro b
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have ho := prodDepolBasis_orthonormal s s' a b
    unfold prodDepolInner at ho
    rw [ho]; split_ifs <;> simp
  simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem prodDepolNormSq_expand {N : ℕ} (s s' : Fin N → Fin 6) (c : (Fin N → Fin 4) → ℂ) :
    prodDepolNormSq s s' (∑ a : Fin N → Fin 4, c a • prodDepolBasis s s' a) =
      ∑ a : Fin N → Fin 4, ‖c a‖ ^ 2 := by
  unfold prodDepolNormSq prodDepolInner
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  have hinner : ∀ a b : Fin N → Fin 4,
      (globalDepolP N s * (prodDepolBasis s s' a)ᴴ * globalDepolP N s' * prodDepolBasis s s' b).trace =
      if a = b then 1 else 0 :=
    fun a b ↦ prodDepolBasis_orthonormal s s' a b
  have hsum : (∑ b : Fin N → Fin 4, c b * ∑ a : Fin N → Fin 4,
      star (c a) * (globalDepolP N s * (prodDepolBasis s s' a)ᴴ *
        globalDepolP N s' * prodDepolBasis s s' b).trace) =
      ∑ b : Fin N → Fin 4, star (c b) * c b := by
    apply Finset.sum_congr rfl; intro b _
    simp only [hinner, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  rw [hsum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Helper: every `singleDepolBasis u v i` expands in `pauliMat`, with `i = 0` proportional to `pauliMat 0`. -/
private lemma singleDepolBasis_expand_pauli (u v : Fin 6) (i : Fin 4) :
    ∃ d : Fin 4 → ℂ, singleDepolBasis u v i = ∑ k : Fin 4, d k • pauliMat k ∧
      (i = 0 → ∀ k : Fin 4, k ≠ 0 → d k = 0) := by
  by_cases hi0 : i = 0
  · subst hi0
    refine ⟨fun k ↦ if k = 0 then ((Real.sqrt (singleDepolInner u v (pauliMat 0) (pauliMat 0)).re)⁻¹ : ℂ) else 0, ?_, ?_⟩
    · rw [Fin.sum_univ_four]; simp [singleDepolBasis, singleDepolGS0]
    · intro _ k hk; simp [hk]
  · -- Any Mat2 expands in pauliMat
    set M := singleDepolBasis u v i
    refine ⟨fun k ↦ (1 / 2 : ℂ) * (pauliMat k * M).trace, ?_, fun h ↦ (hi0 h).elim⟩
    have hM : M = ∑ k : Fin 4, ((1 / 2 : ℂ) * (pauliMat k * M).trace) • pauliMat k := by
      ext p q
      fin_cases p <;> fin_cases q <;>
        (simp [Fin.sum_univ_four, pauliMat, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Fin.sum_univ_two]; ring_nf; try simp only [Complex.I_sq]; ring)
    exact hM

lemma prodDepolBasis_mem_singleSiteTrivial {N : ℕ} (s s' : Fin N → Fin 6)
    (x : Fin N) {a : Fin N → Fin 4} (ha : a x = 0) :
    prodDepolBasis s s' a ∈ singleSiteTrivialSubmodule N x := by
  choose d hd hdz using fun y ↦ singleDepolBasis_expand_pauli (s y) (s' y) (a y)
  have h1 : prodDepolBasis s s' a =
      ∑ α : Fin N → Fin 4, (∏ y : Fin N, d y (α y)) • pauliString α := by
    unfold prodDepolBasis pauliString
    have hfn : (fun y : Fin N ↦ singleDepolBasis (s y) (s' y) (a y)) =
        fun y ↦ ∑ k : Fin 4, d y k • pauliMat k := funext hd
    rw [hfn, kronOp_sum_expand]
    apply Finset.sum_congr rfl; intro α _
    ext p q
    simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  rw [h1]
  apply Submodule.sum_mem; intro α _
  by_cases hαx : α x = 0
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, hαx, rfl⟩)
  · have hz : d x (α x) = 0 := hdz x ha (α x) hαx
    have hp0 : (∏ y : Fin N, d y (α y)) = 0 := Finset.prod_eq_zero (Finset.mem_univ x) hz
    rw [hp0, zero_smul]; exact Submodule.zero_mem _

lemma prodDepolBasis_mem_filtration {N : ℕ} (s s' : Fin N → Fin 6)
    {k : ℕ} {a : Fin N → Fin 4} (ha : stringWeight a ≤ k) :
    prodDepolBasis s s' a ∈ filtrationSubmodule N k := by
  choose d hd hdz using fun y ↦ singleDepolBasis_expand_pauli (s y) (s' y) (a y)
  have h1 : prodDepolBasis s s' a =
      ∑ α : Fin N → Fin 4, (∏ y : Fin N, d y (α y)) • pauliString α := by
    unfold prodDepolBasis pauliString
    have hfn : (fun y : Fin N ↦ singleDepolBasis (s y) (s' y) (a y)) =
        fun y ↦ ∑ k : Fin 4, d y k • pauliMat k := funext hd
    rw [hfn, kronOp_sum_expand]
    apply Finset.sum_congr rfl; intro α _
    ext p q
    simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  rw [h1]
  apply Submodule.sum_mem; intro α _
  by_cases hsub : ∀ y : Fin N, a y = 0 → α y = 0
  · have hwt : stringWeight α ≤ stringWeight a := by
      unfold stringWeight
      apply Finset.card_le_card
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      intro hay; exact hy (hsub y hay)
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, le_trans hwt ha, rfl⟩)
  · push Not at hsub
    rcases hsub with ⟨y₀, hay₀, hαy₀⟩
    have hz : d y₀ (α y₀) = 0 := hdz y₀ hay₀ (α y₀) hαy₀
    have hp0 : (∏ y : Fin N, d y (α y)) = 0 := Finset.prod_eq_zero (Finset.mem_univ y₀) hz
    rw [hp0, zero_smul]; exact Submodule.zero_mem _

private lemma prodDepolInner_pauli_zero {N : ℕ} (s s' : Fin N → Fin 6)
    (a α : Fin N → Fin 4) {x : Fin N} (hax : a x ≠ 0) (hαx : α x = 0) :
    prodDepolInner s s' (prodDepolBasis s s' a) (pauliString α) = 0 := by
  unfold prodDepolInner prodDepolBasis pauliString globalDepolP
  rw [kronOp_conjTranspose, kronOp_mul, kronOp_mul, kronOp_mul, kronOp_trace]
  apply Finset.prod_eq_zero (Finset.mem_univ x)
  change singleDepolInner (s x) (s' x) (singleDepolBasis (s x) (s' x) (a x)) (pauliMat (α x)) = 0
  rw [hαx]
  have hpos := singleDepolInner_self_pos (s x) (s' x) (pauliMat_ne_zero 0)
  have hsr : (Real.sqrt (singleDepolInner (s x) (s' x) (pauliMat 0) (pauliMat 0)).re : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
  have hp0 : pauliMat 0 =
      (Real.sqrt (singleDepolInner (s x) (s' x) (pauliMat 0) (pauliMat 0)).re : ℂ) •
        singleDepolBasis (s x) (s' x) 0 := by
    change pauliMat 0 = _ • singleDepolGS0 (s x) (s' x)
    unfold singleDepolGS0; rw [smul_smul, mul_inv_cancel₀ hsr, one_smul]
  rw [hp0, singleDepolInner_smul_right, singleDepolBasis_orthonormal, if_neg hax, mul_zero]

/-- Exact distance squared to `singleSiteTrivialSubmodule N x` in `prodDepolNormSq s s'`. -/
theorem prodDepolDistSq_singleSite_eq {N : ℕ} (s s' : Fin N → Fin 6) (x : Fin N) (A : QubitOp N) :
    prodDepolDistSq s s' (singleSiteTrivialSubmodule N x) A =
      ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ a x ≠ 0),
        ‖prodDepolInner s s' (prodDepolBasis s s' a) A‖ ^ 2 := by
  set c : (Fin N → Fin 4) → ℂ := fun a ↦ prodDepolInner s s' (prodDepolBasis s s' a) A
  set B₀ : QubitOp N := ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ a x = 0),
    c a • prodDepolBasis s s' a
  have hB₀_mem : B₀ ∈ singleSiteTrivialSubmodule N x :=
    Submodule.sum_mem _ fun a ha ↦
      Submodule.smul_mem _ _ (prodDepolBasis_mem_singleSiteTrivial s s' x (Finset.mem_filter.mp ha).2)
  have hdiff : A - B₀ = ∑ a : Fin N → Fin 4,
      (if a x ≠ 0 then c a else 0) • prodDepolBasis s s' a := by
    have hA := prodDepolBasis_expand s s' A
    have hpart := (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : Fin N → Fin 4 ↦ a x = 0) (fun a ↦ c a • prodDepolBasis s s' a)).symm
    have hne : Finset.univ.filter (fun a : Fin N → Fin 4 ↦ ¬ a x = 0) =
        Finset.univ.filter (fun a : Fin N → Fin 4 ↦ a x ≠ 0) := rfl
    rw [hne] at hpart
    calc A - B₀ = (∑ a : Fin N → Fin 4, c a • prodDepolBasis s s' a) - B₀ := by rw [← hA]
      _ = ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ a x ≠ 0),
            c a • prodDepolBasis s s' a := by
          rw [hpart]; dsimp only [B₀]; abel
      _ = ∑ a : Fin N → Fin 4, (if a x ≠ 0 then c a else 0) • prodDepolBasis s s' a := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl; intro a _; split_ifs <;> simp
  have hnorm_B₀ : prodDepolNormSq s s' (A - B₀) =
      ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ a x ≠ 0), ‖c a‖ ^ 2 := by
    rw [hdiff, prodDepolNormSq_expand, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro a _; split_ifs <;> simp
  apply le_antisymm
  · unfold prodDepolDistSq
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨B, _, rfl⟩
      exact prodDepolNormSq_nonneg s s' (A - B)
    · exact ⟨B₀, hB₀_mem, hnorm_B₀.symm⟩
  · unfold prodDepolDistSq
    apply le_csInf
    · exact ⟨_, B₀, hB₀_mem, rfl⟩
    · rintro r ⟨B, hB, rfl⟩
      have horth : ∀ a : Fin N → Fin 4, a x ≠ 0 →
          prodDepolInner s s' (prodDepolBasis s s' a) B = 0 := by
        intro a hax
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hB
        · rintro _ ⟨α, hαx, rfl⟩
          exact prodDepolInner_pauli_zero s s' a α hax hαx
        · unfold prodDepolInner; simp
        · intro X Y _ _ hX hY
          unfold prodDepolInner at hX hY ⊢
          rw [Matrix.mul_add, Matrix.trace_add, hX, hY, add_zero]
        · intro κ X _ hX
          unfold prodDepolInner at hX ⊢
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hX, mul_zero]
      have hAB := prodDepolBasis_expand s s' (A - B)
      rw [hAB, prodDepolNormSq_expand]
      have hsub : Finset.univ.filter (fun a : Fin N → Fin 4 ↦ a x ≠ 0) ⊆ Finset.univ :=
        Finset.filter_subset _ _
      calc ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ a x ≠ 0), ‖c a‖ ^ 2
          = ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ a x ≠ 0),
              ‖prodDepolInner s s' (prodDepolBasis s s' a) (A - B)‖ ^ 2 := by
            apply Finset.sum_congr rfl; intro a ha
            have hax : a x ≠ 0 := (Finset.mem_filter.mp ha).2
            have hlin : prodDepolInner s s' (prodDepolBasis s s' a) (A - B) =
                c a - prodDepolInner s s' (prodDepolBasis s s' a) B := by
              dsimp only [c]; unfold prodDepolInner; rw [Matrix.mul_sub, Matrix.trace_sub]
            rw [hlin, horth a hax, sub_zero]
        _ ≤ ∑ a : Fin N → Fin 4,
              ‖prodDepolInner s s' (prodDepolBasis s s' a) (A - B)‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ sq_nonneg _

/-- Exact distance squared to `filtrationSubmodule N k` in `prodDepolNormSq s s'`. -/
theorem prodDepolDistSq_filtration_eq {N : ℕ} (s s' : Fin N → Fin 6) (k : ℕ) (A : QubitOp N) :
    prodDepolDistSq s s' (filtrationSubmodule N k) A =
      ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ k < stringWeight a),
        ‖prodDepolInner s s' (prodDepolBasis s s' a) A‖ ^ 2 := by
  set c : (Fin N → Fin 4) → ℂ := fun a ↦ prodDepolInner s s' (prodDepolBasis s s' a) A
  set B₀ : QubitOp N := ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ stringWeight a ≤ k),
    c a • prodDepolBasis s s' a
  have hB₀_mem : B₀ ∈ filtrationSubmodule N k :=
    Submodule.sum_mem _ fun a ha ↦
      Submodule.smul_mem _ _ (prodDepolBasis_mem_filtration s s' (Finset.mem_filter.mp ha).2)
  have hdiff : A - B₀ = ∑ a : Fin N → Fin 4,
      (if k < stringWeight a then c a else 0) • prodDepolBasis s s' a := by
    have hA := prodDepolBasis_expand s s' A
    have hpart := (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : Fin N → Fin 4 ↦ stringWeight a ≤ k) (fun a ↦ c a • prodDepolBasis s s' a)).symm
    have hgt : Finset.univ.filter (fun a : Fin N → Fin 4 ↦ ¬ stringWeight a ≤ k) =
        Finset.univ.filter (fun a : Fin N → Fin 4 ↦ k < stringWeight a) := by
      ext a; simp
    rw [hgt] at hpart
    calc A - B₀ = (∑ a : Fin N → Fin 4, c a • prodDepolBasis s s' a) - B₀ := by rw [← hA]
      _ = ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ k < stringWeight a),
            c a • prodDepolBasis s s' a := by
          rw [hpart]; dsimp only [B₀]; abel
      _ = ∑ a : Fin N → Fin 4, (if k < stringWeight a then c a else 0) • prodDepolBasis s s' a := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl; intro a _; split_ifs <;> simp
  have hnorm_B₀ : prodDepolNormSq s s' (A - B₀) =
      ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ k < stringWeight a), ‖c a‖ ^ 2 := by
    rw [hdiff, prodDepolNormSq_expand, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro a _; split_ifs <;> simp
  apply le_antisymm
  · unfold prodDepolDistSq
    apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨B, _, rfl⟩
      exact prodDepolNormSq_nonneg s s' (A - B)
    · exact ⟨B₀, hB₀_mem, hnorm_B₀.symm⟩
  · unfold prodDepolDistSq
    apply le_csInf
    · exact ⟨_, B₀, hB₀_mem, rfl⟩
    · rintro r ⟨B, hB, rfl⟩
      have horth : ∀ a : Fin N → Fin 4, k < stringWeight a →
          prodDepolInner s s' (prodDepolBasis s s' a) B = 0 := by
        intro a ha
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hB
        · rintro _ ⟨α, hα, rfl⟩
          have hex : ∃ x : Fin N, a x ≠ 0 ∧ α x = 0 := by
            by_contra hall; push Not at hall
            have hle : stringWeight a ≤ stringWeight α := by
              unfold stringWeight
              apply Finset.card_le_card; intro x hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              exact hall x hx
            omega
          rcases hex with ⟨x₀, hax₀, hαx₀⟩
          exact prodDepolInner_pauli_zero s s' a α hax₀ hαx₀
        · unfold prodDepolInner; simp
        · intro X Y _ _ hX hY
          unfold prodDepolInner at hX hY ⊢
          rw [Matrix.mul_add, Matrix.trace_add, hX, hY, add_zero]
        · intro κ X _ hX
          unfold prodDepolInner at hX ⊢
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, hX, mul_zero]
      have hAB := prodDepolBasis_expand s s' (A - B)
      rw [hAB, prodDepolNormSq_expand]
      have hsub : Finset.univ.filter (fun a : Fin N → Fin 4 ↦ k < stringWeight a) ⊆ Finset.univ :=
        Finset.filter_subset _ _
      calc ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ k < stringWeight a), ‖c a‖ ^ 2
          = ∑ a ∈ Finset.univ.filter (fun a : Fin N → Fin 4 ↦ k < stringWeight a),
              ‖prodDepolInner s s' (prodDepolBasis s s' a) (A - B)‖ ^ 2 := by
            apply Finset.sum_congr rfl; intro a ha
            have hak : k < stringWeight a := (Finset.mem_filter.mp ha).2
            have hlin : prodDepolInner s s' (prodDepolBasis s s' a) (A - B) =
                c a - prodDepolInner s s' (prodDepolBasis s s' a) B := by
              dsimp only [c]; unfold prodDepolInner; rw [Matrix.mul_sub, Matrix.trace_sub]
            rw [hlin, horth a hak, sub_zero]
        _ ≤ ∑ a : Fin N → Fin 4,
              ‖prodDepolInner s s' (prodDepolBasis s s' a) (A - B)‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ sq_nonneg _

/-- **Lemma 7.3(3) (Concrete Operator-Level Product Filtration Identity on `QubitOp N`)**:
For EVERY `s, s' : Fin N → Fin 6` and EVERY operator `A : QubitOp N`:
`∑ x : Fin N, prodDepolDistSq s s' (singleSiteTrivialSubmodule N x) A =
 ∑ k ∈ Finset.range N, prodDepolDistSq s s' (filtrationSubmodule N k) A`. -/
theorem lemma_7_3_operator_filtration_identity {N : ℕ} (s s' : Fin N → Fin 6) (A : QubitOp N) :
    ∑ x : Fin N, prodDepolDistSq s s' (singleSiteTrivialSubmodule N x) A =
      ∑ k ∈ Finset.range N, prodDepolDistSq s s' (filtrationSubmodule N k) A := by
  simp_rw [prodDepolDistSq_singleSite_eq, prodDepolDistSq_filtration_eq, Finset.sum_filter]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  have hL : (∑ x : Fin N, if a x ≠ 0 then ‖prodDepolInner s s' (prodDepolBasis s s' a) A‖ ^ 2 else 0) =
      (stringWeight a : ℝ) * ‖prodDepolInner s s' (prodDepolBasis s s' a) A‖ ^ 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; rfl
  have hR : (∑ k ∈ Finset.range N,
        if k < stringWeight a then ‖prodDepolInner s s' (prodDepolBasis s s' a) A‖ ^ 2 else 0) =
      (stringWeight a : ℝ) * ‖prodDepolInner s s' (prodDepolBasis s s' a) A‖ ^ 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hwt_le : stringWeight a ≤ N := by
      unfold stringWeight
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    have hfilt : (Finset.range N).filter (fun k ↦ k < stringWeight a) = Finset.range (stringWeight a) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilt, Finset.card_range]
  rw [hL, hR]

/-- **Theorem 1.3(a) (Concrete Operator-Level Reverse Poincaré on `QubitOp N`, Flaw #2)**:
For ANY `G : GibbsData N` admitting a positive depolarized frame expansion
`G.ρHalf = ∑ s, (π s : ℂ) • globalDepolP N s` (`π s ≥ 0`) and EVERY operator `A : QubitOp N`:
`Re (A | 𝒬̃^{(β)} A)_β^W ≤ ∑ x, ‖𝒮_x(A)‖_{β,W}² ≤ 9 * Re (A | 𝒬^{(β)} A)_β^W`. -/
theorem theorem_1_3a_concrete_operator {N : ℕ} (G : GibbsData N)
    (π : (Fin N → Fin 6) → ℝ) (hπ_nn : ∀ s, 0 ≤ π s)
    (hρHalf : G.ρHalf = ∑ s : Fin N → Fin 6, (π s : ℂ) • globalDepolP N s)
    (A : QubitOp N) :
    (gibbsWightmanInner G A (quantumGlauberGen G A)).re ≤
      ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x A) ∧
    ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x A) ≤
      9 * (gibbsWightmanInner G A (wightmanQ G A)).re := by
  constructor
  · exact theorem_1_3a_lower_concrete G A
  · have hnorm_expand : ∀ X : QubitOp N,
        gibbsWightmanNormSq G X =
          ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6, π s * π s' * prodDepolNormSq s s' X := by
      intro X
      unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner prodDepolNormSq prodDepolInner
      rw [hρHalf]
      simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum, Complex.re_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro s _
      apply Finset.sum_congr rfl; intro s' _
      have hsc : ((π s' : ℂ) * ((π s : ℂ) *
          (globalDepolP N s * Xᴴ * globalDepolP N s' * X).trace)).re =
          π s * π s' * (globalDepolP N s * Xᴴ * globalDepolP N s' * X).trace.re := by
        rw [← mul_assoc, mul_comm (π s' : ℂ) (π s : ℂ), ← Complex.ofReal_mul, Complex.re_ofReal_mul]
      exact hsc
    have hQ_eq : (gibbsWightmanInner G A (wightmanQ G A)).re =
        ∑ k ∈ Finset.range N, (gibbsWightmanInner G A (A - wightmanFiltrationProj G k A)).re := by
      unfold wightmanQ
      simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply]
      unfold gibbsWightmanInner wightmanInner
      rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    calc ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x A)
        = ∑ x : Fin N, ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
            π s * π s' * prodDepolNormSq s s' (siteSizeOp x A) := by
          apply Finset.sum_congr rfl; intro x _; exact hnorm_expand (siteSizeOp x A)
      _ ≤ ∑ x : Fin N, ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
            π s * π s' * (9 * prodDepolDistSq s s' (singleSiteTrivialSubmodule N x) A) := by
          apply Finset.sum_le_sum; intro x _
          apply Finset.sum_le_sum; intro s _
          apply Finset.sum_le_sum; intro s' _
          exact mul_le_mul_of_nonneg_left (lemma_7_3_operator_best_approx s s' x A)
            (mul_nonneg (hπ_nn s) (hπ_nn s'))
      _ = 9 * ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
            π s * π s' * (∑ x : Fin N, prodDepolDistSq s s' (singleSiteTrivialSubmodule N x) A) := by
          rw [Finset.sum_comm]
          have h1 : ∀ s : Fin N → Fin 6,
              (∑ x : Fin N, ∑ s' : Fin N → Fin 6,
                π s * π s' * (9 * prodDepolDistSq s s' (singleSiteTrivialSubmodule N x) A)) =
              9 * ∑ s' : Fin N → Fin 6, π s * π s' *
                (∑ x : Fin N, prodDepolDistSq s s' (singleSiteTrivialSubmodule N x) A) := by
            intro s
            rw [Finset.sum_comm, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro s' _
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro x _; ring
          simp_rw [h1, ← Finset.mul_sum]
      _ = 9 * ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
            π s * π s' * (∑ k ∈ Finset.range N, prodDepolDistSq s s' (filtrationSubmodule N k) A) := by
          congr 1; apply Finset.sum_congr rfl; intro s _
          apply Finset.sum_congr rfl; intro s' _
          rw [lemma_7_3_operator_filtration_identity s s' A]
      _ = 9 * ∑ k ∈ Finset.range N, ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6,
            π s * π s' * prodDepolDistSq s s' (filtrationSubmodule N k) A := by
          congr 1
          have h2 : ∀ s : Fin N → Fin 6,
              (∑ s' : Fin N → Fin 6, π s * π s' *
                ∑ k ∈ Finset.range N, prodDepolDistSq s s' (filtrationSubmodule N k) A) =
              ∑ k ∈ Finset.range N, ∑ s' : Fin N → Fin 6,
                π s * π s' * prodDepolDistSq s s' (filtrationSubmodule N k) A := by
            intro s
            simp_rw [Finset.mul_sum]
            exact Finset.sum_comm
          simp_rw [h2]
          exact Finset.sum_comm
      _ ≤ 9 * ∑ k ∈ Finset.range N,
            (gibbsWightmanInner G A (A - wightmanFiltrationProj G k A)).re := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Finset.sum_le_sum; intro k _
          exact wightmanProj_convex_mixture_ge G π hπ_nn hρHalf (filtrationSubmodule N k) A
      _ = 9 * (gibbsWightmanInner G A (wightmanQ G A)).re := by rw [hQ_eq]

end ProductBasisAndFiltrationIdentity

section Theorem13bOperatorCW

/-- Concrete single-site commutator identity: `[A, σ_x^α] = [𝒮_x(A), σ_x^α]`. -/
lemma matComm_pauliSite_eq_siteSizeOp {N : ℕ} (x : Fin N) (α : Fin 3) (A : QubitOp N) :
    matComm A (pauliSite x α.succ) = matComm (siteSizeOp x A) (pauliSite x α.succ) := by
  have hp0 : pauliMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
  have hpt_pauli : ∀ a : Fin N → Fin 4,
      partialTraceSite x (pauliString a) = if a x = 0 then pauliString a else 0 := by
    intro a
    unfold partialTraceSite pauliString
    have hconj : ∀ c : Fin 4,
        pauliSite x c * kronOp (fun y ↦ pauliMat (a y)) * pauliSite x c =
        kronOp (fun y ↦ if y = x then pauliMat c * pauliMat (a x) * pauliMat c else pauliMat (a y)) := by
      intro c; unfold pauliSite pauliString; rw [kronOp_mul, kronOp_mul]
      congr 1; funext y
      by_cases hy : y = x
      · subst hy; simp
      · simp [hy, hp0]
    simp_rw [hconj]
    ext p q
    simp only [Matrix.smul_apply, Matrix.sum_apply, kronOp, Matrix.of_apply, smul_eq_mul]
    have hsplit : ∀ c : Fin 4,
        (∏ y : Fin N, (if y = x then pauliMat c * pauliMat (a x) * pauliMat c else pauliMat (a y)) (p y) (q y)) =
        (pauliMat c * pauliMat (a x) * pauliMat c) (p x) (q x) *
          ∏ y ∈ Finset.univ.erase x, pauliMat (a y) (p y) (q y) := by
      intro c; rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
      congr 1; · simp
      · apply Finset.prod_congr rfl; intro y hy; simp [(Finset.mem_erase.mp hy).1]
    simp_rw [hsplit, ← Finset.sum_mul, ← mul_assoc]
    have htw : (1 / 4 : ℂ) * (∑ c : Fin 4, (pauliMat c * pauliMat (a x) * pauliMat c) (p x) (q x)) =
        if a x = 0 then pauliMat 0 (p x) (q x) else 0 := by
      generalize a x = u; generalize p x = i1; generalize q x = j1
      fin_cases u <;> fin_cases i1 <;> fin_cases j1 <;>
        (simp [Fin.sum_univ_four, pauliMat, Matrix.mul_apply, Fin.sum_univ_two]; try norm_num)
    rw [htw]
    by_cases hax : a x = 0
    · rw [if_pos hax, if_pos hax]
      simp only [kronOp, Matrix.of_apply]
      rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ pauliMat (a y) (p y) (q y)) (Finset.mem_univ x), hax]
    · rw [if_neg hax, if_neg hax, zero_mul, Matrix.zero_apply]
  have hcomm : matComm (partialTraceSite x A) (pauliSite x α.succ) = 0 := by
    have hA := pauli_expansion_concrete A
    have hpt_comm : ∀ a : Fin N → Fin 4,
        matComm (partialTraceSite x (pauliString a)) (pauliSite x α.succ) = 0 := by
      intro a
      rw [hpt_pauli a]
      by_cases hax : a x = 0
      · rw [if_pos hax]
        unfold matComm pauliSite pauliString
        rw [kronOp_mul, kronOp_mul]
        have heq : (fun y : Fin N ↦ pauliMat (a y) * pauliMat (Function.update (fun _ ↦ (0 : Fin 4)) x α.succ y)) =
            fun y ↦ pauliMat (Function.update (fun _ ↦ (0 : Fin 4)) x α.succ y) * pauliMat (a y) := by
          funext y
          by_cases hy : y = x
          · subst hy; simp [hax, hp0]
          · simp [hy, hp0]
        rw [heq, sub_self]
      · rw [if_neg hax]; unfold matComm; simp
    rw [hA]
    have hpt_lin : partialTraceSite x (∑ a : Fin N → Fin 4,
        ((1 / (2 : ℂ) ^ N) * (pauliString a * A).trace) • pauliString a) =
        ∑ a : Fin N → Fin 4, ((1 / (2 : ℂ) ^ N) * (pauliString a * A).trace) •
          partialTraceSite x (pauliString a) := by
      unfold partialTraceSite
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro c _; rw [smul_comm]
    rw [hpt_lin]
    unfold matComm
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero; intro a _
    rw [← smul_sub]
    have h0 := hpt_comm a
    unfold matComm at h0
    rw [h0, smul_zero]
  unfold siteSizeOp matComm at hcomm ⊢
  rw [Matrix.sub_mul, Matrix.mul_sub]
  have : A * pauliSite x α.succ - partialTraceSite x A * pauliSite x α.succ -
      (pauliSite x α.succ * A - pauliSite x α.succ * partialTraceSite x A) =
      (A * pauliSite x α.succ - pauliSite x α.succ * A) -
      (partialTraceSite x A * pauliSite x α.succ - pauliSite x α.succ * partialTraceSite x A) := by
    abel
  rw [this, hcomm, sub_zero]

private def pauliConjIdx (c : Fin 4) (u : Fin 6) : Fin 6 :=
  match c.val, u.val with
  | 0, _ => u
  | 1, 0 => 0 | 1, 1 => 1 | 1, 2 => 3 | 1, 3 => 2 | 1, 4 => 5 | 1, 5 => 4
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 2 | 2, 3 => 3 | 2, 4 => 5 | 2, 5 => 4
  | 3, 0 => 1 | 3, 1 => 0 | 3, 2 => 3 | 3, 3 => 2 | 3, 4 => 4 | 3, 5 => 5
  | _, _ => u

private lemma pauli_conj_signedPauli (c : Fin 4) (u : Fin 6) :
    pauliMat c * signedPauli u * pauliMat c = signedPauli (pauliConjIdx c u) := by
  fin_cases c <;> fin_cases u <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliConjIdx, pauliMat, signedPauli, pauliX, pauliY, pauliZ, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_mul_I]

private lemma pauli_conj_depolP (c : Fin 4) (u : Fin 6) :
    ∃ v : Fin 6, pauliMat c * depolP u * pauliMat c = depolP v := by
  refine ⟨pauliConjIdx c u, ?_⟩
  unfold depolP
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, pauliMat_sq c, pauli_conj_signedPauli c u]

private lemma three_depolP_eq_depolP_add_psd (u v : Fin 6) :
    (3 : ℂ) • depolP u = depolP v +
      (1 / 8 : ℂ) • ((1 - signedPauli v) * (1 - signedPauli v)) +
      (3 / 8 : ℂ) • ((1 + signedPauli u) * (1 + signedPauli u)) := by
  have hu := depolP_sub_quarter u
  have hv := three_quarter_sub_depolP v
  rw [hu, smul_add, smul_smul, smul_smul]
  norm_num
  rw [hv]

private lemma prodDepolNormSq_replace_le_three {N : ℕ} (s s' : Fin N → Fin 6) (x : Fin N)
    (v : Fin 6) (B : QubitOp N) :
    prodDepolNormSq (Function.update s x v) s' B ≤ 3 * prodDepolNormSq s s' B ∧
    prodDepolNormSq s (Function.update s' x v) B ≤ 3 * prodDepolNormSq s s' B := by
  have hrep_add : ∀ (t : Fin N → Fin 6) (M₁ M₂ : Matrix (Fin 2) (Fin 2) ℂ),
      globalDepolPReplace t x (M₁ + M₂) =
        globalDepolPReplace t x M₁ + globalDepolPReplace t x M₂ := by
    intro t M₁ M₂; ext p q
    simp only [globalDepolPReplace, kronOp, Matrix.of_apply, Matrix.add_apply]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ (if y = x then M₁ + M₂ else depolP (t y)) (p y) (q y)) (Finset.mem_univ x)]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ (if y = x then M₁ else depolP (t y)) (p y) (q y)) (Finset.mem_univ x)]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ (if y = x then M₂ else depolP (t y)) (p y) (q y)) (Finset.mem_univ x)]
    have h1 : ∀ K : Matrix (Fin 2) (Fin 2) ℂ,
        (∏ y ∈ Finset.univ.erase x, (if y = x then K else depolP (t y)) (p y) (q y)) =
        ∏ y ∈ Finset.univ.erase x, depolP (t y) (p y) (q y) := fun K ↦
      Finset.prod_congr rfl fun y hy ↦ by simp [(Finset.mem_erase.mp hy).1]
    rw [h1, h1, h1]; simp only [↓reduceIte, Matrix.add_apply]; ring
  have hrep_smul : ∀ (t : Fin N → Fin 6) (c : ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ),
      globalDepolPReplace t x (c • M) = c • globalDepolPReplace t x M := by
    intro t c M; ext p q
    simp only [globalDepolPReplace, kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ (if y = x then c • M else depolP (t y)) (p y) (q y)) (Finset.mem_univ x)]
    rw [← Finset.mul_prod_erase Finset.univ (fun y ↦ (if y = x then M else depolP (t y)) (p y) (q y)) (Finset.mem_univ x)]
    have h1 : ∀ K : Matrix (Fin 2) (Fin 2) ℂ,
        (∏ y ∈ Finset.univ.erase x, (if y = x then K else depolP (t y)) (p y) (q y)) =
        ∏ y ∈ Finset.univ.erase x, depolP (t y) (p y) (q y) := fun K ↦
      Finset.prod_congr rfl fun y hy ↦ by simp [(Finset.mem_erase.mp hy).1]
    rw [h1, h1]; simp only [↓reduceIte, Matrix.smul_apply, smul_eq_mul]; ring
  have hrep_sq : ∀ (t : Fin N → Fin 6) (M : Matrix (Fin 2) (Fin 2) ℂ) (hMh : Mᴴ = M),
      globalDepolPReplace t x (M * M) =
        (kronOp (fun y ↦ if y = x then M else depolPHalf (t y)))ᴴ *
        kronOp (fun y ↦ if y = x then M else depolPHalf (t y)) := by
    intro t M hMh
    rw [kronOp_conjTranspose, kronOp_mul]; unfold globalDepolPReplace
    congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp [hMh]
    · simp [hy, depolPHalf_herm, depolPHalf_sq]
  have hrep_upd : ∀ (t : Fin N → Fin 6) (w : Fin 6),
      globalDepolPReplace t x (depolP w) = globalDepolP N (Function.update t x w) := by
    intro t w; unfold globalDepolPReplace globalDepolP; congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  have hrep_self : ∀ (t : Fin N → Fin 6),
      globalDepolPReplace t x (depolP (t x)) = globalDepolP N t := by
    intro t; unfold globalDepolPReplace globalDepolP; congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy]
  have hdepol_sq : ∀ (t : Fin N → Fin 6),
      globalDepolP N t = (globalDepolPHalf N t)ᴴ * globalDepolPHalf N t := fun t ↦ by
    rw [globalDepolPHalf_herm, globalDepolPHalf_sq]
  constructor
  · unfold prodDepolNormSq prodDepolInner
    have h3 : 3 * (Matrix.trace (globalDepolP N s * Bᴴ * globalDepolP N s' * B)).re =
        (Matrix.trace (globalDepolPReplace s x ((3 : ℂ) • depolP (s x)) * Bᴴ * globalDepolP N s' * B)).re := by
      rw [hrep_smul, hrep_self]; simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    rw [h3, three_depolP_eq_depolP_add_psd (s x) v, hrep_add, hrep_add, hrep_upd, hrep_smul, hrep_smul]
    set P0 := globalDepolP N (Function.update s x v)
    set M1 := (1 / 8 : ℂ) • globalDepolPReplace s x ((1 - signedPauli v) * (1 - signedPauli v))
    set M2 := (3 / 8 : ℂ) • globalDepolPReplace s x ((1 + signedPauli (s x)) * (1 + signedPauli (s x)))
    have hsplit : ((P0 + M1 + M2) * Bᴴ * globalDepolP N s' * B).trace.re =
        (P0 * Bᴴ * globalDepolP N s' * B).trace.re +
        (M1 * Bᴴ * globalDepolP N s' * B).trace.re +
        (M2 * Bᴴ * globalDepolP N s' * B).trace.re := by
      rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul,
        Matrix.trace_add, Matrix.trace_add, Complex.add_re, Complex.add_re]
    rw [hsplit]
    have ht1 : 0 ≤ (M1 * Bᴴ * globalDepolP N s' * B).trace.re := by
      dsimp only [M1]
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (1 / 8 : ℂ) = ((1 / 8 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
      apply mul_nonneg (by norm_num)
      rw [hrep_sq s (1 - signedPauli v) (by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, signedPauli_herm]),
        hdepol_sq s']
      exact trace_quad_nonneg _ _ B
    have ht2 : 0 ≤ (M2 * Bᴴ * globalDepolP N s' * B).trace.re := by
      dsimp only [M2]
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (3 / 8 : ℂ) = ((3 / 8 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
      apply mul_nonneg (by norm_num)
      rw [hrep_sq s (1 + signedPauli (s x)) (by rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, signedPauli_herm]),
        hdepol_sq s']
      exact trace_quad_nonneg _ _ B
    linarith
  · unfold prodDepolNormSq prodDepolInner
    have h3 : 3 * (Matrix.trace (globalDepolP N s * Bᴴ * globalDepolP N s' * B)).re =
        (Matrix.trace (globalDepolP N s * Bᴴ * globalDepolPReplace s' x ((3 : ℂ) • depolP (s' x)) * B)).re := by
      rw [hrep_smul, hrep_self]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    rw [h3, three_depolP_eq_depolP_add_psd (s' x) v, hrep_add, hrep_add, hrep_upd, hrep_smul, hrep_smul]
    set P0 := globalDepolP N (Function.update s' x v)
    set M1 := (1 / 8 : ℂ) • globalDepolPReplace s' x ((1 - signedPauli v) * (1 - signedPauli v))
    set M2 := (3 / 8 : ℂ) • globalDepolPReplace s' x ((1 + signedPauli (s' x)) * (1 + signedPauli (s' x)))
    have hsplit : (globalDepolP N s * Bᴴ * (P0 + M1 + M2) * B).trace.re =
        (globalDepolP N s * Bᴴ * P0 * B).trace.re +
        (globalDepolP N s * Bᴴ * M1 * B).trace.re +
        (globalDepolP N s * Bᴴ * M2 * B).trace.re := by
      rw [mul_add, mul_add, add_mul, add_mul,
        Matrix.trace_add, Matrix.trace_add, Complex.add_re, Complex.add_re]
    rw [hsplit]
    have ht1 : 0 ≤ (globalDepolP N s * Bᴴ * M1 * B).trace.re := by
      dsimp only [M1]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (1 / 8 : ℂ) = ((1 / 8 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
      apply mul_nonneg (by norm_num)
      rw [hdepol_sq s,
        hrep_sq s' (1 - signedPauli v) (by rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, signedPauli_herm])]
      exact trace_quad_nonneg _ _ B
    have ht2 : 0 ≤ (globalDepolP N s * Bᴴ * M2 * B).trace.re := by
      dsimp only [M2]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      rw [show (3 / 8 : ℂ) = ((3 / 8 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
      apply mul_nonneg (by norm_num)
      rw [hdepol_sq s,
        hrep_sq s' (1 + signedPauli (s' x)) (by rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, signedPauli_herm])]
      exact trace_quad_nonneg _ _ B
    linarith

private lemma prodDepolNormSq_sub_le {N : ℕ} (s s' : Fin N → Fin 6) (X Y : QubitOp N) :
    prodDepolNormSq s s' (X - Y) ≤ 2 * (prodDepolNormSq s s' X + prodDepolNormSq s s' Y) := by
  have h1 : prodDepolNormSq s s' (X - Y) + prodDepolNormSq s s' (X + Y) =
      2 * (prodDepolNormSq s s' X + prodDepolNormSq s s' Y) := by
    unfold prodDepolNormSq prodDepolInner
    set P1 := globalDepolP N s
    set P2 := globalDepolP N s'
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_add]
    simp only [mul_sub, sub_mul, mul_add, add_mul, Matrix.trace_sub, Matrix.trace_add,
      Complex.sub_re, Complex.add_re]
    ring
  linarith [prodDepolNormSq_nonneg s s' (X + Y)]

private lemma trace_pauli_conj_right {N : ℕ} (P S1 S2 B : QubitOp N) (hPh : Pᴴ = P) :
    (S1 * (B * P)ᴴ * S2 * (B * P)).trace = ((P * S1 * P) * Bᴴ * S2 * B).trace := by
  rw [Matrix.conjTranspose_mul, hPh]
  calc (S1 * (P * Bᴴ) * S2 * (B * P)).trace
      = ((S1 * P * Bᴴ * S2 * B) * P).trace := by simp only [Matrix.mul_assoc]
    _ = (P * (S1 * P * Bᴴ * S2 * B)).trace := Matrix.trace_mul_comm _ _
    _ = ((P * S1 * P) * Bᴴ * S2 * B).trace := by simp only [Matrix.mul_assoc]

private lemma trace_pauli_conj_left {N : ℕ} (P S1 S2 B : QubitOp N) (hPh : Pᴴ = P) :
    (S1 * (P * B)ᴴ * S2 * (P * B)).trace = (S1 * Bᴴ * (P * S2 * P) * B).trace := by
  rw [Matrix.conjTranspose_mul, hPh]
  simp only [Matrix.mul_assoc]

lemma prodDepolNormSq_matComm_pauliSite_le {N : ℕ} (s s' : Fin N → Fin 6)
    (x : Fin N) (α : Fin 3) (B : QubitOp N) :
    prodDepolNormSq s s' (matComm B (pauliSite x α.succ)) ≤ 12 * prodDepolNormSq s s' B := by
  let P := pauliSite x α.succ
  have hPh : Pᴴ = P := by
    dsimp only [P]; unfold pauliSite pauliString
    rw [kronOp_conjTranspose]; congr 1; funext y
    by_cases hy : y = x
    · subst hy; simp; exact pauliMat_herm α.succ
    · simp [hy]; exact pauliMat_herm 0
  have hpar : prodDepolNormSq s s' (B * P - P * B) ≤
      2 * (prodDepolNormSq s s' (B * P) + prodDepolNormSq s s' (P * B)) :=
    prodDepolNormSq_sub_le s s' (B * P) (P * B)
  have hBP : prodDepolNormSq s s' (B * P) ≤ 3 * prodDepolNormSq s s' B := by
    rcases pauli_conj_depolP α.succ (s x) with ⟨v, hv⟩
    have hconj : P * globalDepolP N s * P = globalDepolP N (Function.update s x v) := by
      dsimp only [P]; unfold pauliSite pauliString globalDepolP
      rw [kronOp_mul, kronOp_mul]; congr 1; funext y
      by_cases hy : y = x
      · subst hy; simp [hv]
      · have hp0 : pauliMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
        simp [hy, hp0]
    have heq : prodDepolNormSq s s' (B * P) = prodDepolNormSq (Function.update s x v) s' B := by
      unfold prodDepolNormSq prodDepolInner
      rw [trace_pauli_conj_right P (globalDepolP N s) (globalDepolP N s') B hPh, hconj]
    rw [heq]
    exact (prodDepolNormSq_replace_le_three s s' x v B).1
  have hPB : prodDepolNormSq s s' (P * B) ≤ 3 * prodDepolNormSq s s' B := by
    rcases pauli_conj_depolP α.succ (s' x) with ⟨v, hv⟩
    have hconj : P * globalDepolP N s' * P = globalDepolP N (Function.update s' x v) := by
      dsimp only [P]; unfold pauliSite pauliString globalDepolP
      rw [kronOp_mul, kronOp_mul]; congr 1; funext y
      by_cases hy : y = x
      · subst hy; simp [hv]
      · have hp0 : pauliMat 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat]
        simp [hy, hp0]
    have heq : prodDepolNormSq s s' (P * B) = prodDepolNormSq s (Function.update s' x v) B := by
      unfold prodDepolNormSq prodDepolInner
      rw [trace_pauli_conj_left P (globalDepolP N s) (globalDepolP N s') B hPh, hconj]
    rw [heq]
    exact (prodDepolNormSq_replace_le_three s s' x v B).2
  unfold matComm
  linarith

/-- **Theorem 1.3(b) — Equal-Time Commutator Bound on `QubitOp N` (Flaw #3)**:
For ANY `G : GibbsData N` with positive depolarized frame expansion
`G.ρHalf = ∑ s, (π s : ℂ) • globalDepolP N s` (`π s ≥ 0`) and EVERY operator `A : QubitOp N`:
`otocCW G A ≤ 54 * Re (A | 𝒬^{(β)} A)_β^W` (in fact `≤ (81/2) * Re (A | 𝒬^{(β)} A)_β^W`). -/
theorem theorem_1_3b_concrete_CW {N : ℕ} (G : GibbsData N)
    (π : (Fin N → Fin 6) → ℝ) (hπ_nn : ∀ s, 0 ≤ π s)
    (hρHalf : G.ρHalf = ∑ s : Fin N → Fin 6, (π s : ℂ) • globalDepolP N s)
    (A : QubitOp N) :
    otocCW G A ≤ 54 * (gibbsWightmanInner G A (wightmanQ G A)).re := by
  have hnorm_expand : ∀ X : QubitOp N,
      gibbsWightmanNormSq G X =
        ∑ s : Fin N → Fin 6, ∑ s' : Fin N → Fin 6, π s * π s' * prodDepolNormSq s s' X := by
    intro X
    unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner prodDepolNormSq prodDepolInner
    rw [hρHalf]
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro s _
    apply Finset.sum_congr rfl; intro s' _
    rw [← mul_assoc, mul_comm (π s' : ℂ) (π s : ℂ), ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hcomm_bound : ∀ (x : Fin N) (α : Fin 3),
      gibbsWightmanNormSq G (matComm A (pauliSite x α.succ)) ≤
        12 * gibbsWightmanNormSq G (siteSizeOp x A) := by
    intro x α
    rw [matComm_pauliSite_eq_siteSizeOp x α A, hnorm_expand, hnorm_expand]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro s' _
    have h1 := prodDepolNormSq_matComm_pauliSite_le s s' x α (siteSizeOp x A)
    have hnn := mul_nonneg (hπ_nn s) (hπ_nn s')
    nlinarith
  have hCW_le : otocCW G A ≤ (9 / 2 : ℝ) * ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x A) := by
    unfold otocCW
    have hsum : ∑ x : Fin N, ∑ α : Fin 3, gibbsWightmanNormSq G (matComm A (pauliSite x α.succ)) ≤
        36 * ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x A) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro x _
      calc ∑ α : Fin 3, gibbsWightmanNormSq G (matComm A (pauliSite x α.succ))
          ≤ ∑ _α : Fin 3, (12 * gibbsWightmanNormSq G (siteSizeOp x A)) :=
            Finset.sum_le_sum fun α _ ↦ hcomm_bound x α
        _ = 36 * gibbsWightmanNormSq G (siteSizeOp x A) := by
            simp [Finset.sum_const]; ring
    linarith
  have h13a := (theorem_1_3a_concrete_operator G π hπ_nn hρHalf A).2
  have hQ_nn := wightmanQ_nonneg G A
  linarith

end Theorem13bOperatorCW

end KrylovChaos
