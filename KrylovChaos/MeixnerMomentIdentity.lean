/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.CarlemanJacobi
import KrylovChaos.LanczosMoments
import KrylovChaos.SpectralDyck
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Exact Meixner (`η = 1`) Moment–`sech`-Integral Identity and Lemma 5.1 (Eq. 5.5)

Establishes the exact Meixner (`η = 1`) moment identity and the non-asymptotic comparison
inequality of Lemma 5.1 (Eq. 5.5) from Mathlib alone:
1. `meixnerPhi_hasDerivAt` and `iteratedDeriv_inv_cosh_zero_eq_jacobiMat_pow`:
   Proves that `φ_n(t) = (tanh t)^n / cosh t` solves the exact Lanczos ODE
   `φ_n'(t) = n φ_{n-1}(t) - (n + 1) φ_{n+1}(t)` with `φ_n(0) = δ_{n,0}`, hence
   `iteratedDeriv (2 * m) (fun t ↦ (Real.cosh t)⁻¹) 0 = (-1) ^ m * ((jacobiMat (2 * m + 1) (fun k ↦ (k : ℝ))) ^ (2 * m)) 0 0`.
2. `integral_cos_mul_inv_cosh_pi_half`:
   Proves via the rectangle Cauchy integral on `[-R, R] × [0, 2]` (subtracting the simple pole
   at `z = i`) that `∫ u : ℝ, Real.cos (u * t) * (Real.cosh (Real.pi * u / 2))⁻¹ = 2 * (Real.cosh t)⁻¹`.
3. `jacobiMat_meixner_even_moment_eq_sech_integral`:
   Differentiating `2 * m` times under the integral sign and rescaling by `α₁ > 0` yields the
   exact Meixner `η = 1` identity:
   `((jacobiMat (2 * m + 1) (fun k ↦ α₁ * (k : ℝ))) ^ (2 * m)) 0 0 = (1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * m) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹`.
4. `lemma_5_1_eq_5_5_exact_sech_comparison`:
   For any `b : ℕ → ℝ` with `b k > 0` (`k ≥ 1`) and `b k ≥ α₁ * k` (`k > N₀`), proves the
   verbatim non-asymptotic Lemma 5.1 Eq. (5.5) lower bound for every `n > N₀`.
-/

namespace KrylovChaos

open scoped BigOperators Matrix
open Complex Matrix MeasureTheory Filter Topology

section MeixnerLanczosODE

/-- Skew-symmetric Jacobi matrix `(S_D(b))_{i, l} = b_i δ_{l+1, i} - b_l δ_{i+1, l}`. -/
def skewJacobiMat (D : ℕ) (b : ℕ → ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun i l ↦
    if l.val + 1 = i.val then b i.val
    else if i.val + 1 = l.val then -(b l.val)
    else 0

/-- Diagonal unitary gauge identity relating `jacobiMat` and `skewJacobiMat`:
`((jacobiMat D b) ^ (2 * m)) 0 0 = (-1) ^ m * ((skewJacobiMat D b) ^ (2 * m)) 0 0`. -/
lemma jacobiMat_pow_even_zero_eq_skew (D : ℕ) (hD : 0 < D) (b : ℕ → ℝ) (m : ℕ) :
    ((jacobiMat D b) ^ (2 * m)) ⟨0, hD⟩ ⟨0, hD⟩ =
      (-1 : ℝ) ^ m * ((skewJacobiMat D b) ^ (2 * m)) ⟨0, hD⟩ ⟨0, hD⟩ := by
  let U : Matrix (Fin D) (Fin D) ℂ := Matrix.diagonal (fun j : Fin D ↦ Complex.I ^ j.val)
  let Uinv : Matrix (Fin D) (Fin D) ℂ := Matrix.diagonal (fun j : Fin D ↦ (-Complex.I) ^ j.val)
  have hUU : U * Uinv = 1 := by
    dsimp only [U, Uinv]; rw [Matrix.diagonal_mul_diagonal]
    have h1 : (fun j : Fin D ↦ Complex.I ^ j.val * (-Complex.I) ^ j.val) = fun _ ↦ (1 : ℂ) := by
      funext j; rw [← mul_pow]; norm_num
    rw [h1, Matrix.diagonal_one]
  have hUinvU : Uinv * U = 1 := by
    dsimp only [U, Uinv]; rw [Matrix.diagonal_mul_diagonal]
    have h1 : (fun j : Fin D ↦ (-Complex.I) ^ j.val * Complex.I ^ j.val) = fun _ ↦ (1 : ℂ) := by
      funext j; rw [← mul_pow]; norm_num
    rw [h1, Matrix.diagonal_one]
  have hconj : U * (jacobiMat D b).map Complex.ofReal * Uinv =
      Complex.I • (skewJacobiMat D b).map Complex.ofReal := by
    ext i l
    simp only [U, Uinv, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply,
      Matrix.smul_apply, smul_eq_mul, jacobiMat, skewJacobiMat, Matrix.of_apply]
    by_cases h1 : l.val + 1 = i.val
    · have h2 : ¬(l.val = i.val + 1) := by omega
      have h1' : i.val = l.val + 1 := h1.symm
      rw [if_neg h2, if_pos h1', if_pos h1, h1]
      have hpow : Complex.I ^ i.val * (-Complex.I) ^ l.val = Complex.I := by
        rw [← h1, pow_succ, mul_assoc, mul_comm Complex.I, ← mul_assoc, ← mul_pow]; norm_num
      calc Complex.I ^ i.val * (b i.val : ℂ) * (-Complex.I) ^ l.val
          = (Complex.I ^ i.val * (-Complex.I) ^ l.val) * (b i.val : ℂ) := by ring
        _ = Complex.I * (b i.val : ℂ) := by rw [hpow]
    · by_cases h2 : i.val + 1 = l.val
      · have h2' : l.val = i.val + 1 := h2.symm
        rw [if_pos h2', if_neg h1, if_pos h2, h2]
        have hpow : Complex.I ^ i.val * (-Complex.I) ^ l.val = -Complex.I := by
          rw [← h2, pow_succ, ← mul_assoc, ← mul_pow]; norm_num
        calc Complex.I ^ i.val * (b l.val : ℂ) * (-Complex.I) ^ l.val
            = (Complex.I ^ i.val * (-Complex.I) ^ l.val) * (b l.val : ℂ) := by ring
          _ = -Complex.I * (b l.val : ℂ) := by rw [hpow]
          _ = Complex.I * ((-b l.val : ℝ) : ℂ) := by push_cast; ring
      · have h1' : ¬(i.val = l.val + 1) := by omega
        have h2' : ¬(l.val = i.val + 1) := by omega
        rw [if_neg h2', if_neg h1', if_neg h1, if_neg h2]; simp
  have hpow_conj : ∀ k : ℕ,
      U * ((jacobiMat D b) ^ k).map Complex.ofReal * Uinv =
        (Complex.I ^ k) • ((skewJacobiMat D b) ^ k).map Complex.ofReal := by
    intro k
    induction k with
    | zero => simp [hUU]
    | succ k ih =>
      have hmap_mul : ∀ A B : Matrix (Fin D) (Fin D) ℝ,
          (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
        intro A B; ext i j; simp [Matrix.mul_apply, Complex.ofReal_sum]
      rw [pow_succ, pow_succ, pow_succ, hmap_mul, hmap_mul]
      calc U * ((jacobiMat D b ^ k).map Complex.ofReal * (jacobiMat D b).map Complex.ofReal) * Uinv
          = (U * (jacobiMat D b ^ k).map Complex.ofReal * Uinv) *
              (U * (jacobiMat D b).map Complex.ofReal * Uinv) := by
              calc U * ((jacobiMat D b ^ k).map Complex.ofReal * (jacobiMat D b).map Complex.ofReal) * Uinv
                  = U * (jacobiMat D b ^ k).map Complex.ofReal * 1 * (jacobiMat D b).map Complex.ofReal * Uinv := by
                      simp only [Matrix.mul_one, Matrix.mul_assoc]
                _ = U * (jacobiMat D b ^ k).map Complex.ofReal * (Uinv * U) *
                      (jacobiMat D b).map Complex.ofReal * Uinv := by rw [hUinvU]
                _ = _ := by simp only [Matrix.mul_assoc]
        _ = (Complex.I ^ k • (skewJacobiMat D b ^ k).map Complex.ofReal) *
              (Complex.I • (skewJacobiMat D b).map Complex.ofReal) := by rw [ih, hconj]
        _ = (Complex.I ^ k * Complex.I) •
              ((skewJacobiMat D b ^ k).map Complex.ofReal * (skewJacobiMat D b).map Complex.ofReal) := by
              rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have h00 := congrFun (congrFun (hpow_conj (2 * m)) ⟨0, hD⟩) ⟨0, hD⟩
  simp only [U, Uinv, Matrix.diagonal_mul, Matrix.mul_diagonal, pow_zero, one_mul, mul_one,
    Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h00
  have hI2m : Complex.I ^ (2 * m) = (((-1 : ℝ) ^ m : ℝ) : ℂ) := by
    rw [pow_mul, Complex.I_sq]; push_cast; rfl
  rw [hI2m, ← Complex.ofReal_mul] at h00
  exact Complex.ofReal_injective h00

/-- Exact Meixner (`η = 1`) Krylov wavefunction `φ_n(t) = (tanh t)^n / cosh t`. -/
noncomputable def meixnerPhi (n : ℕ) (t : ℝ) : ℝ :=
  (Real.tanh t) ^ n / Real.cosh t

lemma meixnerPhi_zero (n : ℕ) : meixnerPhi n 0 = if n = 0 then 1 else 0 := by
  unfold meixnerPhi
  cases n with
  | zero => simp
  | succ n => simp [Real.tanh_eq_sinh_div_cosh]

private lemma hasDerivAt_real_sinh (t : ℝ) : HasDerivAt Real.sinh (Real.cosh t) t := by
  have hrew : Real.sinh = fun x ↦ (Real.exp x - Real.exp (-x)) / 2 := funext Real.sinh_eq
  rw [hrew, Real.cosh_eq]
  have hneg : HasDerivAt (fun x : ℝ ↦ Real.exp (-x)) (Real.exp (-t) * (-1)) t :=
    (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
  have h1 : HasDerivAt (fun x : ℝ ↦ Real.exp x - Real.exp (-x)) (Real.exp t - Real.exp (-t) * (-1)) t :=
    (Real.hasDerivAt_exp t).fun_sub hneg
  convert h1.div_const 2 using 1; ring

private lemma hasDerivAt_real_cosh (t : ℝ) : HasDerivAt Real.cosh (Real.sinh t) t := by
  have hrew : Real.cosh = fun x ↦ (Real.exp x + Real.exp (-x)) / 2 := funext Real.cosh_eq
  rw [hrew, Real.sinh_eq]
  have hneg : HasDerivAt (fun x : ℝ ↦ Real.exp (-x)) (Real.exp (-t) * (-1)) t :=
    (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
  have h1 : HasDerivAt (fun x : ℝ ↦ Real.exp x + Real.exp (-x)) (Real.exp t + Real.exp (-t) * (-1)) t :=
    (Real.hasDerivAt_exp t).fun_add hneg
  convert h1.div_const 2 using 1; ring

private lemma hasDerivAt_complex_cosh (z : ℂ) : HasDerivAt Complex.cosh (Complex.sinh z) z := by
  change HasDerivAt (fun w : ℂ ↦ (Complex.exp w + Complex.exp (-w)) / 2)
    ((Complex.exp z - Complex.exp (-z)) / 2) z
  have hneg : HasDerivAt (fun w : ℂ ↦ Complex.exp (-w)) (Complex.exp (-z) * (-1)) z :=
    (Complex.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)
  have h1 : HasDerivAt (fun w : ℂ ↦ Complex.exp w + Complex.exp (-w)) (Complex.exp z + Complex.exp (-z) * (-1)) z :=
    (Complex.hasDerivAt_exp z).fun_add hneg
  convert h1.div_const 2 using 1; ring

/-- Exact derivative of `Real.tanh`: `HasDerivAt Real.tanh (1 - (Real.tanh t) ^ 2) t`. -/
lemma hasDerivAt_tanh (t : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh t ^ 2) t := by
  have hrew : Real.tanh = fun x ↦ Real.sinh x / Real.cosh x := funext Real.tanh_eq_sinh_div_cosh
  rw [hrew]
  have h := (hasDerivAt_real_sinh t).div (hasDerivAt_real_cosh t) (Real.cosh_pos t).ne'
  convert h using 1
  have hcs := Real.cosh_sq_sub_sinh_sq t
  dsimp only
  have hc : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  field_simp [hc]

/-- Exact Lanczos ODE satisfied by `meixnerPhi`:
`d/dt φ_n(t) = n * φ_{n - 1}(t) - (n + 1) * φ_{n + 1}(t)`. -/
lemma meixnerPhi_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (meixnerPhi n)
      ((n : ℝ) * meixnerPhi (n - 1) t - ((n + 1 : ℕ) : ℝ) * meixnerPhi (n + 1) t) t := by
  unfold meixnerPhi
  have hc_ne : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  have hsc : Real.sinh t = Real.tanh t * Real.cosh t := by
    rw [Real.tanh_eq_sinh_div_cosh, div_mul_cancel₀ _ hc_ne]
  cases n with
  | zero =>
    have hdiv := (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_real_cosh t) hc_ne
    convert hdiv using 1
    · funext s; simp
    · simp only [Nat.cast_zero, zero_mul, zero_sub, Nat.zero_add, Nat.cast_one, one_mul, pow_one,
        hsc]
      field_simp [hc_ne]
  | succ m =>
    have hnum : HasDerivAt (fun s ↦ Real.tanh s ^ (m + 1))
        (((m + 1 : ℕ) : ℝ) * Real.tanh t ^ m * (1 - Real.tanh t ^ 2)) t :=
      (hasDerivAt_tanh t).fun_pow (m + 1)
    have hdiv := hnum.div (hasDerivAt_real_cosh t) hc_ne
    convert hdiv using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ, hsc]
    field_simp [hc_ne]
    ring

/-- Bandedness of `skewJacobiMat D b ^ k`: entries vanish whenever `j.val + k < l.val`. -/
lemma skewJacobiMat_pow_eq_zero_of_lt {D : ℕ} (b : ℕ → ℝ) (k : ℕ) :
    ∀ (j l : Fin D), j.val + k < l.val → ((skewJacobiMat D b) ^ k) j l = 0 := by
  induction k with
  | zero =>
    intro j l hlt
    simp only [pow_zero, Matrix.one_apply]
    rw [if_neg (fun h ↦ by subst h; omega)]
  | succ k ih =>
    intro j l hlt
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero; intro r _
    by_cases hr : j.val + k < r.val
    · rw [ih j r hr, zero_mul]
    · have hS0 : skewJacobiMat D b r l = 0 := by
        unfold skewJacobiMat; simp only [Matrix.of_apply]
        split_ifs with h1 h2
        · omega
        · omega
        · rfl
      rw [hS0, mul_zero]

/-- Exact `k`-th derivative formula for `meixnerPhi`:
for `j.val + k < D`,
`iteratedDeriv k (meixnerPhi j.val) t = ∑ l : Fin D, ((skewJacobiMat D (fun r ↦ (r : ℝ))) ^ k) j l * meixnerPhi l.val t`. -/
lemma iteratedDeriv_meixnerPhi {D : ℕ} (k : ℕ) :
    ∀ (j : Fin D), j.val + k < D → ∀ t : ℝ,
      iteratedDeriv k (meixnerPhi j.val) t =
        ∑ l : Fin D, ((skewJacobiMat D (fun r ↦ (r : ℝ))) ^ k) j l * meixnerPhi l.val t := by
  induction k with
  | zero =>
    intro j _ t
    simp only [iteratedDeriv_zero, pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  | succ k ih =>
    intro j hjk t
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv k (meixnerPhi j.val) =
        fun s ↦ ∑ l : Fin D, ((skewJacobiMat D (fun r ↦ (r : ℝ))) ^ k) j l * meixnerPhi l.val s :=
      funext (ih j (by omega))
    rw [hfun]
    have hderiv : HasDerivAt
        (fun s ↦ ∑ l : Fin D, ((skewJacobiMat D (fun r ↦ (r : ℝ))) ^ k) j l * meixnerPhi l.val s)
        (∑ l : Fin D, ((skewJacobiMat D (fun r ↦ (r : ℝ))) ^ k) j l *
          ((l.val : ℝ) * meixnerPhi (l.val - 1) t - ((l.val + 1 : ℕ) : ℝ) * meixnerPhi (l.val + 1) t)) t :=
      HasDerivAt.fun_sum fun l _ ↦ (meixnerPhi_hasDerivAt l.val t).const_mul _
    rw [hderiv.deriv]
    let S := skewJacobiMat D (fun r ↦ (r : ℝ))
    have hterm : ∀ l : Fin D,
        (S ^ k) j l * ((l.val : ℝ) * meixnerPhi (l.val - 1) t - ((l.val + 1 : ℕ) : ℝ) * meixnerPhi (l.val + 1) t) =
        ∑ r : Fin D, (S ^ k) j l * S l r * meixnerPhi r.val t := by
      intro l
      by_cases hl : j.val + k < l.val
      · have h0 : (S ^ k) j l = 0 := skewJacobiMat_pow_eq_zero_of_lt _ k j l hl
        simp [h0]
      · have hlD : l.val + 1 < D := by omega
        have hstep : ∀ r : Fin D, (S ^ k) j l * S l r * meixnerPhi r.val t =
            (if r.val + 1 = l.val then (S ^ k) j l * (l.val : ℝ) * meixnerPhi r.val t else 0) +
            (if l.val + 1 = r.val then -(S ^ k) j l * ((l.val + 1 : ℕ) : ℝ) * meixnerPhi r.val t else 0) := by
          intro r
          dsimp only [S]; unfold skewJacobiMat; simp only [Matrix.of_apply]
          by_cases ha : r.val + 1 = l.val
          · have hb : ¬(l.val + 1 = r.val) := by omega
            rw [if_pos ha, if_pos ha, if_neg hb]; ring
          · by_cases hb : l.val + 1 = r.val
            · rw [if_neg ha, if_pos hb, if_neg ha, if_pos hb, ← hb]; ring
            · rw [if_neg ha, if_neg hb, if_neg ha, if_neg hb]; ring
        simp_rw [hstep, Finset.sum_add_distrib]
        have hsum1 : ∑ r : Fin D, (if r.val + 1 = l.val then (S ^ k) j l * (l.val : ℝ) * meixnerPhi r.val t else 0) =
            (S ^ k) j l * ((l.val : ℝ) * meixnerPhi (l.val - 1) t) := by
          by_cases hl0 : l.val = 0
          · rw [hl0, Nat.cast_zero, zero_mul, mul_zero]
            apply Finset.sum_eq_zero; intro r _; rw [if_neg (by omega)]
          · rw [Finset.sum_eq_single ⟨l.val - 1, by omega⟩]
            · rw [if_pos (by dsimp; omega)]; dsimp; ring
            · intro r _ hr; rw [if_neg (fun h ↦ hr (Fin.ext (by dsimp; omega)))]
            · intro h; exact absurd (Finset.mem_univ _) h
        have hsum2 : ∑ r : Fin D, (if l.val + 1 = r.val then -(S ^ k) j l * ((l.val + 1 : ℕ) : ℝ) * meixnerPhi r.val t else 0) =
            -((S ^ k) j l * (((l.val + 1 : ℕ) : ℝ) * meixnerPhi (l.val + 1) t)) := by
          rw [Finset.sum_eq_single ⟨l.val + 1, hlD⟩]
          · rw [if_pos rfl]; dsimp; ring
          · intro r _ hr; rw [if_neg (fun h ↦ hr (Fin.ext (by dsimp; omega)))]
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hsum1, hsum2]; ring
    calc ∑ l : Fin D, (S ^ k) j l *
            ((l.val : ℝ) * meixnerPhi (l.val - 1) t - ((l.val + 1 : ℕ) : ℝ) * meixnerPhi (l.val + 1) t)
        = ∑ l : Fin D, ∑ r : Fin D, (S ^ k) j l * S l r * meixnerPhi r.val t :=
          Finset.sum_congr rfl fun l _ ↦ hterm l
      _ = ∑ r : Fin D, ∑ l : Fin D, (S ^ k) j l * S l r * meixnerPhi r.val t := Finset.sum_comm
      _ = ∑ r : Fin D, (S ^ (k + 1)) j r * meixnerPhi r.val t := by
          apply Finset.sum_congr rfl; intro r _
          rw [pow_succ, Matrix.mul_apply, Finset.sum_mul]

/-- Exact `2m`-th derivative of `(Real.cosh t)⁻¹` at `t = 0` in terms of the Meixner `η = 1`
Jacobi matrix:
`iteratedDeriv (2 * m) (fun t ↦ (Real.cosh t)⁻¹) 0 = (-1) ^ m * ((jacobiMat (2 * m + 1) (fun r ↦ (r : ℝ))) ^ (2 * m)) 0 0`. -/
theorem iteratedDeriv_inv_cosh_zero_eq_jacobiMat_pow (m : ℕ) :
    iteratedDeriv (2 * m) (fun t : ℝ ↦ (Real.cosh t)⁻¹) 0 =
      (-1 : ℝ) ^ m *
        ((jacobiMat (2 * m + 1) (fun r ↦ (r : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ := by
  have hphi0 : meixnerPhi 0 = fun t : ℝ ↦ (Real.cosh t)⁻¹ := by
    funext t; simp [meixnerPhi, one_div]
  rw [← hphi0]
  have h1 := iteratedDeriv_meixnerPhi (D := 2 * m + 1) (2 * m) ⟨0, Nat.succ_pos _⟩ (by dsimp; omega) 0
  rw [h1]
  simp_rw [meixnerPhi_zero, mul_ite, mul_one, mul_zero]
  have hsum : ∑ l : Fin (2 * m + 1),
      (if l.val = 0 then ((skewJacobiMat (2 * m + 1) (fun r ↦ (r : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ l else 0) =
      ((skewJacobiMat (2 * m + 1) (fun r ↦ (r : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ := by
    rw [Finset.sum_eq_single ⟨0, Nat.succ_pos _⟩]
    · simp
    · intro l _ hl; rw [if_neg (fun h ↦ hl (Fin.ext h))]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hsum, jacobiMat_pow_even_zero_eq_skew (2 * m + 1) (Nat.succ_pos _) (fun r ↦ (r : ℝ)) m]
  rw [← mul_assoc, ← mul_pow]; norm_num

end MeixnerLanczosODE

section SechFourierTransform

private lemma real_sinh_eq_zero_imp {x : ℝ} (h : Real.sinh x = 0) : x = 0 := by
  rw [Real.sinh_eq] at h
  have heq : Real.exp x = Real.exp (-x) := by linarith
  have h1 := Real.exp_injective heq
  linarith

private lemma real_sinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  rw [Real.sinh_eq]
  have hlt : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- Lower bound on `‖Complex.cosh (a + i b)‖`: `|Real.sinh a| ≤ ‖Complex.cosh (a + i b)‖`. -/
private lemma abs_sinh_le_norm_cosh (z : ℂ) :
    |Real.sinh z.re| ≤ ‖Complex.cosh z‖ := by
  have hsq : ‖Complex.cosh z‖ ^ 2 = Real.sinh z.re ^ 2 + Real.cos z.im ^ 2 := by
    have h1 : Complex.cosh z =
        ((Real.cosh z.re * Real.cos z.im : ℝ) : ℂ) +
        ((Real.sinh z.re * Real.sin z.im : ℝ) : ℂ) * Complex.I := by
      have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
      conv_lhs => rw [hz]
      rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
        ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast; ring
    rw [h1, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add]
    have hcs := Real.cosh_sq_sub_sinh_sq z.re
    have hsc := Real.sin_sq_add_cos_sq z.im
    nlinarith
  have hle : |Real.sinh z.re| ^ 2 ≤ ‖Complex.cosh z‖ ^ 2 := by
    rw [sq_abs, hsq]; linarith [sq_nonneg (Real.cos z.im)]
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hle

/-- In the closed strip `0 ≤ z.im ≤ 2`, `Complex.cosh (π * z / 2) = 0 ↔ z = I`. -/
private lemma cosh_pi_half_eq_zero_iff_in_strip {z : ℂ} (h0 : 0 ≤ z.im) (h2 : z.im ≤ 2) :
    Complex.cosh ((Real.pi / 2 : ℝ) * z) = 0 ↔ z = Complex.I := by
  constructor
  · intro hz
    have hre : ((Real.pi / 2 : ℝ) * z).re = Real.pi / 2 * z.re := by simp
    have him : ((Real.pi / 2 : ℝ) * z).im = Real.pi / 2 * z.im := by simp
    have hsinh0 : Real.sinh (Real.pi / 2 * z.re) = 0 := by
      have h1 := abs_sinh_le_norm_cosh ((Real.pi / 2 : ℝ) * z)
      rw [hz, norm_zero, hre] at h1
      exact abs_nonpos_iff.mp h1
    have hzre : z.re = 0 := by
      have h1 : Real.pi / 2 * z.re = 0 := real_sinh_eq_zero_imp hsinh0
      exact (mul_eq_zero.mp h1).resolve_left (by positivity)
    have hcos0 : Real.cos (Real.pi / 2 * z.im) = 0 := by
      have h1 : Complex.cosh ((Real.pi / 2 : ℝ) * z) = (Real.cos (Real.pi / 2 * z.im) : ℂ) := by
        have hzeq : (Real.pi / 2 : ℝ) * z = ((Real.pi / 2 * z.im : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [hzre]
        rw [hzeq, Complex.cosh_mul_I, Complex.ofReal_cos]
      rw [h1] at hz
      exact Complex.ofReal_eq_zero.mp hz
    have hzim : z.im = 1 := by
      have hlo : -(Real.pi / 2) < Real.pi / 2 * z.im := by nlinarith [Real.pi_pos]
      have hhi : Real.pi / 2 * z.im < 3 * Real.pi / 2 := by nlinarith [Real.pi_pos]
      have hcos_iff : Real.pi / 2 * z.im = Real.pi / 2 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact (Real.cos_pos_of_mem_Ioo ⟨hlo, hlt⟩).ne' hcos0
        · have hneg : Real.cos (Real.pi / 2 * z.im) < 0 := by
            have h1 : Real.cos (Real.pi / 2 * z.im - Real.pi) > 0 :=
              Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
            rw [Real.cos_sub_pi] at h1; linarith
          exact hneg.ne hcos0
      have hpi_ne : Real.pi / 2 ≠ 0 := by positivity
      exact mul_left_cancel₀ hpi_ne (by linarith)
    exact Complex.ext (by simp [hzre]) (by simp [hzim])
  · rintro rfl
    rw [Complex.cosh_mul_I, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]

/-- Elementary integral of `1 / (x - i)` on `[-R, R]`:
`∫ x in (-R)..R, ((x : ℂ) - Complex.I)⁻¹ = (2 * Real.arctan R : ℝ) * Complex.I`. -/
private lemma intervalIntegral_inv_sub_I (R : ℝ) :
    ∫ x in (-R)..R, ((x : ℂ) - Complex.I)⁻¹ = ((2 * Real.arctan R : ℝ) : ℂ) * Complex.I := by
  have hrew : ∀ x : ℝ, ((x : ℂ) - Complex.I)⁻¹ =
      ((x / (x ^ 2 + 1) : ℝ) : ℂ) + ((1 / (x ^ 2 + 1) : ℝ) : ℂ) * Complex.I := by
    intro x
    have hden : (x ^ 2 + 1 : ℝ) ≠ 0 := by positivity
    have hne : ((x : ℂ) - Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this
    apply inv_eq_of_mul_eq_one_right
    have hmul : ((x : ℂ) - Complex.I) *
        (((x / (x ^ 2 + 1) : ℝ) : ℂ) + ((1 / (x ^ 2 + 1) : ℝ) : ℂ) * Complex.I) =
        (((x ^ 2 + 1) / (x ^ 2 + 1) : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [hmul, div_self hden, Complex.ofReal_one]
  simp_rw [hrew]
  have hc1 : Continuous (fun x : ℝ ↦ ((x / (x ^ 2 + 1) : ℝ) : ℂ)) := by
    exact Complex.continuous_ofReal.comp (continuous_id.div (by fun_prop) fun x ↦ by positivity)
  have hc2 : Continuous (fun x : ℝ ↦ ((1 / (x ^ 2 + 1) : ℝ) : ℂ) * Complex.I) := by
    exact (Complex.continuous_ofReal.comp (continuous_const.div (by fun_prop) fun x ↦ by positivity)).mul continuous_const
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)]
  have hodd : ∫ x in (-R)..R, ((x / (x ^ 2 + 1) : ℝ) : ℂ) = 0 := by
    rw [intervalIntegral.integral_ofReal]
    have h0 : ∫ x in (-R)..R, x / (x ^ 2 + 1) = 0 := by
      have h1 := intervalIntegral.integral_comp_neg (f := fun x : ℝ ↦ x / (x ^ 2 + 1)) (a := -R) (b := R)
      simp only [neg_neg, neg_sq, neg_div, intervalIntegral.integral_neg] at h1
      linarith
    rw [h0, Complex.ofReal_zero]
  have harc : ∫ x in (-R)..R, ((1 / (x ^ 2 + 1) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.arctan R : ℝ) : ℂ) * Complex.I := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
    congr 1; congr 1
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := Real.arctan) (f' := fun x : ℝ ↦ 1 / (1 + x ^ 2)) (a := -R) (b := R)
      (fun x _ ↦ Real.hasDerivAt_arctan x)
      ((continuous_const.div (continuous_const.add (continuous_pow 2))
        (fun x ↦ ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2))).intervalIntegrable (-R) R)
    have hrew2 : (fun x : ℝ ↦ 1 / (x ^ 2 + 1)) = fun x : ℝ ↦ 1 / (1 + x ^ 2) := by
      funext x; rw [add_comm]
    rw [hrew2, hftc, Real.arctan_neg]; ring
  rw [hodd, zero_add, harc]

/-- Elementary integral of `1 / (x + i)` on `[-R, R]`:
`∫ x in (-R)..R, ((x : ℂ) + Complex.I)⁻¹ = -((2 * Real.arctan R : ℝ) : ℂ) * Complex.I`. -/
private lemma intervalIntegral_inv_add_I (R : ℝ) :
    ∫ x in (-R)..R, ((x : ℂ) + Complex.I)⁻¹ = -(((2 * Real.arctan R : ℝ) : ℂ) * Complex.I) := by
  have h1 := intervalIntegral_inv_sub_I R
  have hrew : ∀ x : ℝ, ((x : ℂ) + Complex.I)⁻¹ = -((((-x : ℝ) : ℂ) - Complex.I)⁻¹) := by
    intro x; push_cast; rw [← inv_neg]; congr 1; ring
  simp_rw [hrew, intervalIntegral.integral_neg]
  have hsub := intervalIntegral.integral_comp_neg (f := fun x : ℝ ↦ ((x : ℂ) - Complex.I)⁻¹) (a := -R) (b := R)
  simp only [neg_neg] at hsub
  rw [hsub, h1]

/-- Integrability of `u ↦ |u| ^ k * (Real.cosh (c * u))⁻¹` for every `c > 0` and `k : ℕ`. -/
lemma integrable_pow_abs_mul_inv_cosh {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable (fun u : ℝ ↦ |u| ^ k * (Real.cosh (c * u))⁻¹) := by
  set C : ℝ := 2 * (k.factorial : ℝ) * (c / 2)⁻¹ ^ k
  have hC : 0 < C := by dsimp only [C]; positivity
  have hdom : Integrable (fun u : ℝ ↦ C * Real.exp (-(c / 2) * |u|)) := by
    have h1 : Integrable (fun u : ℝ ↦ Real.exp (-(c / 2) * |u|)) := by
      have hpos : Integrable (Set.indicator (Set.Ioi (0 : ℝ)) (fun u : ℝ ↦ Real.exp (-(c / 2) * u))) :=
        (integrableOn_exp_mul_Ioi (by linarith : -(c / 2) < 0) 0).integrable_indicator measurableSet_Ioi
      have hneg : Integrable (fun u : ℝ ↦ Set.indicator (Set.Ioi (0 : ℝ)) (fun v : ℝ ↦ Real.exp (-(c / 2) * v)) (-u)) :=
        hpos.comp_neg
      have hsum : Integrable (fun u : ℝ ↦
          Set.indicator (Set.Ioi (0 : ℝ)) (fun v : ℝ ↦ Real.exp (-(c / 2) * v)) u +
          Set.indicator (Set.Ioi (0 : ℝ)) (fun v : ℝ ↦ Real.exp (-(c / 2) * v)) (-u)) :=
        hpos.add hneg
      refine hsum.congr ?_
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu
      have hne : u ≠ 0 := hu
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have h1u : u ∉ Set.Ioi (0 : ℝ) := by simp [hlt.le]
        have h2u : -u ∈ Set.Ioi (0 : ℝ) := by simp [hlt]
        rw [Set.indicator_of_notMem h1u, Set.indicator_of_mem h2u, zero_add, abs_of_neg hlt]
      · have h1u : u ∈ Set.Ioi (0 : ℝ) := hgt
        have h2u : -u ∉ Set.Ioi (0 : ℝ) := by simp [hgt.le]
        rw [Set.indicator_of_mem h1u, Set.indicator_of_notMem h2u, add_zero, abs_of_pos hgt]
    exact h1.const_mul C
  refine hdom.mono' ?_ (Eventually.of_forall fun u ↦ ?_)
  · exact ((continuous_abs.pow k).mul ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀
      fun u ↦ (Real.cosh_pos _).ne')).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (abs_nonneg u) k)
      (inv_nonneg.mpr (Real.cosh_pos _).le))]
    have hpow_exp : ((c / 2) * |u|) ^ k / (k.factorial : ℝ) ≤ Real.exp ((c / 2) * |u|) :=
      Real.pow_div_factorial_le_exp ((c / 2) * |u|) (by positivity) k
    have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    have hpow_le : |u| ^ k ≤ (k.factorial : ℝ) * (c / 2)⁻¹ ^ k * Real.exp ((c / 2) * |u|) := by
      have h1 : ((c / 2) * |u|) ^ k ≤ (k.factorial : ℝ) * Real.exp ((c / 2) * |u|) := by
        have := (div_le_iff₀ hfac_pos).mp hpow_exp; linarith
      rw [mul_pow] at h1
      calc |u| ^ k = (c / 2)⁻¹ ^ k * ((c / 2) ^ k * |u| ^ k) := by
            rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by positivity : c / 2 ≠ 0), one_pow, one_mul]
        _ ≤ (c / 2)⁻¹ ^ k * ((k.factorial : ℝ) * Real.exp ((c / 2) * |u|)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (k.factorial : ℝ) * (c / 2)⁻¹ ^ k * Real.exp ((c / 2) * |u|) := by ring
    have hcosh_lb : Real.exp (c * |u|) / 2 ≤ Real.cosh (c * u) := by
      have habs : Real.cosh (c * u) = Real.cosh (c * |u|) := by
        rcases le_total 0 u with hu | hu
        · rw [abs_of_nonneg hu]
        · rw [abs_of_nonpos hu, mul_neg, Real.cosh_neg]
      rw [habs, Real.cosh_eq]; linarith [Real.exp_pos (-(c * |u|))]
    have hinv_le : (Real.cosh (c * u))⁻¹ ≤ 2 * Real.exp (-(c * |u|)) := by
      rw [inv_le_comm₀ (Real.cosh_pos _) (by positivity)]
      calc (2 * Real.exp (-(c * |u|)))⁻¹ = Real.exp (c * |u|) / 2 := by
            rw [mul_inv, Real.exp_neg, inv_inv, div_eq_mul_inv, mul_comm]
        _ ≤ Real.cosh (c * u) := hcosh_lb
    calc |u| ^ k * (Real.cosh (c * u))⁻¹
        ≤ ((k.factorial : ℝ) * (c / 2)⁻¹ ^ k * Real.exp ((c / 2) * |u|)) *
            (2 * Real.exp (-(c * |u|))) :=
          mul_le_mul hpow_le hinv_le (inv_nonneg.mpr (Real.cosh_pos _).le) (by positivity)
      _ = C * (Real.exp ((c / 2) * |u|) * Real.exp (-(c * |u|))) := by dsimp only [C]; ring
      _ = C * Real.exp (-(c / 2) * |u|) := by rw [← Real.exp_add]; congr 2; ring

/-- **Exact Fourier Transform of `sech(π u / 2)`**:
`∫ u : ℝ, Real.cos (u * t) * (Real.cosh (Real.pi * u / 2))⁻¹ = 2 * (Real.cosh t)⁻¹`. -/
theorem integral_cos_mul_inv_cosh_pi_half (t : ℝ) :
    ∫ u : ℝ, Real.cos (u * t) * (Real.cosh (Real.pi * u / 2))⁻¹ = 2 * (Real.cosh t)⁻¹ := by
  let f : ℂ → ℂ := fun z ↦ Complex.exp (Complex.I * (t : ℂ) * z) / Complex.cosh ((Real.pi / 2 : ℝ) * z)
  let res : ℂ := -((2 / Real.pi : ℝ) : ℂ) * Complex.I * Complex.exp (-(t : ℂ))
  let g : ℂ → ℂ := fun z ↦
    if z = Complex.I then
      -- Removable singularity value at `z = I` (irrelevant to boundary integral since `I` is interior)
      Function.update (fun w ↦ f w - res / (w - Complex.I)) Complex.I
        (limUnder (𝓝[≠] Complex.I) (fun w ↦ f w - res / (w - Complex.I))) z
    else f z - res / (z - Complex.I)
  have hg_eq_upd : g = Function.update (fun w ↦ f w - res / (w - Complex.I)) Complex.I
      (limUnder (𝓝[≠] Complex.I) (fun w ↦ f w - res / (w - Complex.I))) := by
    funext z; dsimp only [g]; by_cases hz : z = Complex.I
    · subst hz; simp
    · simp [hz]
  -- Holomorphy of `g` on the open strip `{z : ℂ | -1/2 < z.im ∧ z.im < 5/2}` via removable singularity at `z = I`.
  let Ω : Set ℂ := {z : ℂ | -(1 / 2 : ℝ) < z.im ∧ z.im < 5 / 2}
  have hΩ_open : IsOpen Ω :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hI_mem : Complex.I ∈ Ω := by simp [Ω]; norm_num
  have hcosh_ne_punct : ∀ z ∈ Ω, z ≠ Complex.I → Complex.cosh ((Real.pi / 2 : ℝ) * z) ≠ 0 := by
    intro z hz hne heq
    have hre : ((Real.pi / 2 : ℝ) * z).re = Real.pi / 2 * z.re := by simp
    have hsinh0 : Real.sinh (Real.pi / 2 * z.re) = 0 := by
      have h1 := abs_sinh_le_norm_cosh ((Real.pi / 2 : ℝ) * z)
      rw [heq, norm_zero, hre] at h1
      exact abs_nonpos_iff.mp h1
    have hzre : z.re = 0 :=
      (mul_eq_zero.mp (real_sinh_eq_zero_imp hsinh0)).resolve_left (by positivity)
    have hcos0 : Real.cos (Real.pi / 2 * z.im) = 0 := by
      have h1 : Complex.cosh ((Real.pi / 2 : ℝ) * z) = (Real.cos (Real.pi / 2 * z.im) : ℂ) := by
        have hzeq : (Real.pi / 2 : ℝ) * z = ((Real.pi / 2 * z.im : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [hzre]
        rw [hzeq, Complex.cosh_mul_I, Complex.ofReal_cos]
      rw [h1] at heq
      exact Complex.ofReal_eq_zero.mp heq
    have hlo : -(Real.pi / 2) < Real.pi / 2 * z.im := by nlinarith [hz.1, Real.pi_pos]
    have hhi : Real.pi / 2 * z.im < 3 * Real.pi / 2 := by nlinarith [hz.2, Real.pi_pos]
    have hcos_eq : Real.pi / 2 * z.im = Real.pi / 2 := by
      by_contra hne'
      rcases lt_or_gt_of_ne hne' with hlt | hgt
      · exact (Real.cos_pos_of_mem_Ioo ⟨hlo, hlt⟩).ne' hcos0
      · have hneg : Real.cos (Real.pi / 2 * z.im) < 0 := by
          have h1 : Real.cos (Real.pi / 2 * z.im - Real.pi) > 0 :=
            Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
          rw [Real.cos_sub_pi] at h1; linarith
        exact hneg.ne hcos0
    have hzim : z.im = 1 := mul_left_cancel₀ (by positivity : Real.pi / 2 ≠ 0) (by linarith)
    exact hne (Complex.ext (by simp [hzre]) (by simp [hzim]))
  have hdiff_punct : DifferentiableOn ℂ (fun w ↦ f w - res / (w - Complex.I)) (Ω \ {Complex.I}) := by
    intro w hw
    have hne : w ≠ Complex.I := hw.2
    have hcosh_ne := hcosh_ne_punct w hw.1 hne
    have hf_d : DifferentiableAt ℂ f w := by
      dsimp only [f]
      have hlin : DifferentiableAt ℂ (fun u : ℂ ↦ ((Real.pi / 2 : ℝ) : ℂ) * u) w :=
        (differentiableAt_const _).mul differentiableAt_id
      have hcd : DifferentiableAt ℂ (fun u : ℂ ↦ Complex.cosh (((Real.pi / 2 : ℝ) : ℂ) * u)) w :=
        (hasDerivAt_complex_cosh _).differentiableAt.comp w hlin
      exact ((differentiableAt_const _).mul differentiableAt_id).cexp.div hcd hcosh_ne
    have hp_d : DifferentiableAt ℂ (fun u ↦ res / (u - Complex.I)) w :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr hne)
    exact (hf_d.sub hp_d).differentiableWithinAt
  -- Show `(w - I) * (f w - res / (w - I)) → 0` as `w → I` (so `f w - res / (w - I) = o((w - I)⁻¹)`).
  have hlim_zero : Tendsto (fun w : ℂ ↦ (w - Complex.I) * (f w - res / (w - Complex.I)))
      (𝓝[≠] Complex.I) (nhds 0) := by
    -- Compute `lim_{w → I} (w - I) / cosh(π w / 2) = 1 / (I * π / 2)` via derivative of `cosh(π w / 2)` at `I`.
    have hderiv_cosh : HasDerivAt (fun w : ℂ ↦ Complex.cosh ((Real.pi / 2 : ℝ) * w))
        (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) Complex.I := by
      have h1 := (hasDerivAt_complex_cosh (((Real.pi / 2 : ℝ) : ℂ) * Complex.I)).comp Complex.I
        ((hasDerivAt_id Complex.I).const_mul ((Real.pi / 2 : ℝ) : ℂ))
      have hsinh : Complex.sinh (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) = Complex.I := by
        rw [Complex.sinh_mul_I, ← Complex.ofReal_sin, Real.sin_pi_div_two]; simp
      refine h1.congr_deriv ?_
      rw [hsinh]; ring
    have hslope : Tendsto (fun w : ℂ ↦ Complex.cosh ((Real.pi / 2 : ℝ) * w) / (w - Complex.I))
        (𝓝[≠] Complex.I) (nhds (((Real.pi / 2 : ℝ) : ℂ) * Complex.I)) := by
      have h0 : Complex.cosh ((Real.pi / 2 : ℝ) * Complex.I) = 0 :=
        (cosh_pi_half_eq_zero_iff_in_strip (by simp) (by simp)).mpr rfl
      have hs := hasDerivAt_iff_tendsto_slope.mp hderiv_cosh
      refine hs.congr' (Eventually.of_forall fun w ↦ ?_)
      rw [slope_def_field, h0, sub_zero]
    have hden_ne : (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) Complex.I_ne_zero
    have hinv_slope : Tendsto (fun w : ℂ ↦ (w - Complex.I) / Complex.cosh ((Real.pi / 2 : ℝ) * w))
        (𝓝[≠] Complex.I) (nhds ((((Real.pi / 2 : ℝ) : ℂ) * Complex.I)⁻¹)) := by
      have := hslope.inv₀ hden_ne
      refine this.congr' (Eventually.of_forall fun w ↦ by rw [inv_div])
    have hexp_lim : Tendsto (fun w : ℂ ↦ Complex.exp (Complex.I * (t : ℂ) * w))
        (𝓝[≠] Complex.I) (nhds (Complex.exp (-(t : ℂ)))) := by
      have hcont : Continuous (fun w : ℂ ↦ Complex.exp (Complex.I * (t : ℂ) * w)) := by fun_prop
      have hval : Complex.exp (Complex.I * (t : ℂ) * Complex.I) = Complex.exp (-(t : ℂ)) := by
        congr 1; ring_nf; rw [Complex.I_sq]; ring
      simpa [hval] using (hcont.tendsto Complex.I).mono_left nhdsWithin_le_nhds
    have hprod := hexp_lim.mul hinv_slope
    have hres_eq : Complex.exp (-(t : ℂ)) * ((((Real.pi / 2 : ℝ) : ℂ) * Complex.I)⁻¹) = res := by
      dsimp only [res]
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      push_cast
      field_simp [hpi, Complex.I_ne_zero]
      rw [Complex.I_sq]; ring
    rw [hres_eq] at hprod
    have hsub := hprod.sub tendsto_const_nhds
    rw [sub_self] at hsub
    refine hsub.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hne : w - Complex.I ≠ 0 := sub_ne_zero.mpr hw
    dsimp only [f]
    field_simp [hne]
  have hiso : (fun w ↦ (f w - res / (w - Complex.I)) - (f Complex.I - res / (Complex.I - Complex.I)))
      =o[𝓝[≠] Complex.I] fun w ↦ (w - Complex.I)⁻¹ := by
    rw [Asymptotics.isLittleO_iff_tendsto' (by
      filter_upwards [self_mem_nhdsWithin] with w hw h0
      exact absurd h0 (inv_ne_zero (sub_ne_zero.mpr hw)))]
    have hconst_lim : Tendsto (fun w : ℂ ↦ (w - Complex.I) * (f Complex.I - res / (Complex.I - Complex.I)))
        (𝓝[≠] Complex.I) (nhds 0) := by
      have h1 : Tendsto (fun w : ℂ ↦ w - Complex.I) (𝓝[≠] Complex.I) (nhds 0) := by
        have hcont : Continuous (fun w : ℂ ↦ w - Complex.I) := by fun_prop
        simpa [sub_self] using (hcont.tendsto Complex.I).mono_left nhdsWithin_le_nhds
      simpa using h1.mul_const (f Complex.I - res / (Complex.I - Complex.I))
    have hsub_lim : Tendsto (fun w : ℂ ↦ (w - Complex.I) * (f w - res / (w - Complex.I)) -
        (w - Complex.I) * (f Complex.I - res / (Complex.I - Complex.I))) (𝓝[≠] Complex.I) (nhds 0) := by
      simpa using hlim_zero.sub hconst_lim
    refine hsub_lim.congr' (Eventually.of_forall fun w ↦ ?_)
    dsimp only; rw [div_inv_eq_mul]; ring
  have hg_diff : DifferentiableOn ℂ g Ω := by
    rw [hg_eq_upd]
    exact Complex.differentiableOn_update_limUnder_of_isLittleO (hΩ_open.mem_nhds hI_mem) hdiff_punct hiso
  -- Rectangle contour integral of `g` on `[-R, R] × [0, 2]` equals 0 for every `R > 0`.
  have hrect_eq : ∀ R : ℝ, 0 < R →
      ((1 : ℂ) + Complex.exp (-2 * (t : ℂ))) * (∫ x in (-R)..R, f (x : ℂ)) +
      Complex.I * (∫ y in (0 : ℝ)..2, f ((R : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in (0 : ℝ)..2, f (-(R : ℂ) + (y : ℂ) * Complex.I)) =
      res * (((4 * Real.arctan R : ℝ) : ℂ) * Complex.I +
        Complex.I * (∫ y in (0 : ℝ)..2, ((R : ℂ) + (y : ℂ) * Complex.I - Complex.I)⁻¹) -
        Complex.I * (∫ y in (0 : ℝ)..2, (-(R : ℂ) + (y : ℂ) * Complex.I - Complex.I)⁻¹)) := by
    intro R hR
    set z₁ : ℂ := -(R : ℂ)
    set z₂ : ℂ := (R : ℂ) + 2 * Complex.I
    have hsub_rect : Set.uIcc z₁.re z₂.re ×ℂ Set.uIcc z₁.im z₂.im ⊆ Ω := by
      intro z hz
      have hre : z₁.re = -R := by simp [z₁]
      have hre2 : z₂.re = R := by simp [z₂]
      have him1 : z₁.im = 0 := by simp [z₁]
      have him2 : z₂.im = 2 := by simp [z₂]
      have hy := hz.2
      rw [him1, him2, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hy
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hzero := Complex.integral_boundary_rect_eq_zero_of_differentiableOn g z₁ z₂
      (hg_diff.mono hsub_rect)
    simp only [z₁, z₂, Complex.ofReal_neg, Complex.ofReal_zero, Complex.ofReal_ofNat, Complex.neg_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re,
      Complex.re_ofNat, Complex.I_re, mul_zero, zero_mul, Complex.im_ofNat, Complex.I_im, mul_one,
      sub_zero, add_zero, Complex.neg_im, Complex.ofReal_im, neg_zero, Complex.add_im,
      Complex.mul_im, zero_add] at hzero
    -- On all 4 boundary edges of the rectangle, `z ≠ I` so `g z = f z - res / (z - I)`.
    have hbot : ∀ x : ℝ, g (x : ℂ) = f (x : ℂ) - res * ((x : ℂ) - Complex.I)⁻¹ := by
      intro x
      have hne : (x : ℂ) ≠ Complex.I := by
        intro h; have := congrArg Complex.im h; simp at this
      dsimp only [g]; rw [if_neg hne, div_eq_mul_inv]
    have htop : ∀ x : ℝ, g ((x : ℂ) + 2 * Complex.I) =
        -Complex.exp (-2 * (t : ℂ)) * f (x : ℂ) - res * ((x : ℂ) + Complex.I)⁻¹ := by
      intro x
      have hne : ((x : ℂ) + 2 * Complex.I) ≠ Complex.I := by
        intro h; have := congrArg Complex.im h; simp at this
      have hf_top : f ((x : ℂ) + 2 * Complex.I) = -Complex.exp (-2 * (t : ℂ)) * f (x : ℂ) := by
        dsimp only [f]
        have hnum : Complex.exp (Complex.I * (t : ℂ) * ((x : ℂ) + 2 * Complex.I)) =
            Complex.exp (-2 * (t : ℂ)) * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) := by
          rw [← Complex.exp_add]; congr 1; ring_nf; rw [Complex.I_sq]; ring
        have hden : Complex.cosh ((Real.pi / 2 : ℝ) * ((x : ℂ) + 2 * Complex.I)) =
            -Complex.cosh ((Real.pi / 2 : ℝ) * (x : ℂ)) := by
          have harg : (Real.pi / 2 : ℝ) * ((x : ℂ) + 2 * Complex.I) =
              (Real.pi / 2 : ℝ) * (x : ℂ) + (Real.pi : ℂ) * Complex.I := by push_cast; ring
          rw [harg, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
            ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi, Real.sin_pi]
          simp
        rw [hnum, hden, div_neg, mul_div_assoc]; ring
      have hsub : (x : ℂ) + 2 * Complex.I - Complex.I = (x : ℂ) + Complex.I := by ring
      dsimp only [g]; rw [if_neg hne, hf_top, hsub, div_eq_mul_inv]
    have hright : ∀ y : ℝ, g ((R : ℂ) + (y : ℂ) * Complex.I) =
        f ((R : ℂ) + (y : ℂ) * Complex.I) - res * ((R : ℂ) + (y : ℂ) * Complex.I - Complex.I)⁻¹ := by
      intro y
      have hne : (R : ℂ) + (y : ℂ) * Complex.I ≠ Complex.I := by
        intro h; have := congrArg Complex.re h
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_im, mul_zero, sub_zero, add_zero] at this
        linarith
      dsimp only [g]; rw [if_neg hne, div_eq_mul_inv]
    have hleft : ∀ y : ℝ, g (-(R : ℂ) + (y : ℂ) * Complex.I) =
        f (-(R : ℂ) + (y : ℂ) * Complex.I) - res * (-(R : ℂ) + (y : ℂ) * Complex.I - Complex.I)⁻¹ := by
      intro y
      have hne : -(R : ℂ) + (y : ℂ) * Complex.I ≠ Complex.I := by
        intro h; have := congrArg Complex.re h
        simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero] at this
        linarith
      dsimp only [g]; rw [if_neg hne, div_eq_mul_inv]
    simp_rw [hbot, htop, hright, hleft] at hzero
    -- Split each of the 4 interval integrals into `f` and `res * pole` parts (all continuous on compact intervals).
    have hcf_bot : Continuous (fun x : ℝ ↦ f (x : ℂ)) := by
      dsimp only [f]
      refine (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).div
        (Complex.continuous_cosh.comp (continuous_const.mul Complex.continuous_ofReal)) fun x ↦ ?_
      have hne : (x : ℂ) ≠ Complex.I := fun h ↦ by have := congrArg Complex.im h; simp at this
      exact hcosh_ne_punct (x : ℂ) (by simp [Ω]; norm_num) hne
    have hcp_bot : Continuous (fun x : ℝ ↦ res * ((x : ℂ) - Complex.I)⁻¹) :=
      continuous_const.mul ((Complex.continuous_ofReal.sub continuous_const).inv₀ fun x ↦ by
        intro h; have := congrArg Complex.im h; simp at this)
    have hcp_top : Continuous (fun x : ℝ ↦ res * ((x : ℂ) + Complex.I)⁻¹) :=
      continuous_const.mul ((Complex.continuous_ofReal.add continuous_const).inv₀ fun x ↦ by
        intro h; have := congrArg Complex.im h; simp at this)
    have hcf_right : Continuous (fun y : ℝ ↦ f ((R : ℂ) + (y : ℂ) * Complex.I)) := by
      dsimp only [f]
      refine (Complex.continuous_exp.comp (continuous_const.mul (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)))).div
        (Complex.continuous_cosh.comp (continuous_const.mul (continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)))) fun y ↦ ?_
      have hre : ((Real.pi / 2 : ℝ) * ((R : ℂ) + (y : ℂ) * Complex.I)).re = Real.pi / 2 * R := by simp
      intro heq
      have h1 := abs_sinh_le_norm_cosh ((Real.pi / 2 : ℝ) * ((R : ℂ) + (y : ℂ) * Complex.I))
      rw [heq, norm_zero, hre] at h1
      have h2 : 0 < Real.sinh (Real.pi / 2 * R) := real_sinh_pos_of_pos (by positivity)
      linarith [abs_of_pos h2]
    have hcf_left : Continuous (fun y : ℝ ↦ f (-(R : ℂ) + (y : ℂ) * Complex.I)) := by
      dsimp only [f]
      refine (Complex.continuous_exp.comp (continuous_const.mul (continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)))).div
        (Complex.continuous_cosh.comp (continuous_const.mul (continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)))) fun y ↦ ?_
      have hre : ((Real.pi / 2 : ℝ) * (-(R : ℂ) + (y : ℂ) * Complex.I)).re = -(Real.pi / 2 * R) := by simp
      intro heq
      have h1 := abs_sinh_le_norm_cosh ((Real.pi / 2 : ℝ) * (-(R : ℂ) + (y : ℂ) * Complex.I))
      rw [heq, norm_zero, hre, Real.sinh_neg, abs_neg] at h1
      have h2 : 0 < Real.sinh (Real.pi / 2 * R) := real_sinh_pos_of_pos (by positivity)
      linarith [abs_of_pos h2]
    have hcp_right : Continuous (fun y : ℝ ↦ res * ((R : ℂ) + (y : ℂ) * Complex.I - Complex.I)⁻¹) :=
      continuous_const.mul (((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).inv₀ fun y h ↦ by
        have := congrArg Complex.re h; simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero] at this; linarith)
    have hcp_left : Continuous (fun y : ℝ ↦ res * (-(R : ℂ) + (y : ℂ) * Complex.I - Complex.I)⁻¹) :=
      continuous_const.mul (((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).inv₀ fun y h ↦ by
        have := congrArg Complex.re h; simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero] at this; linarith)
    rw [intervalIntegral.integral_sub (hcf_bot.intervalIntegrable _ _) (hcp_bot.intervalIntegrable _ _),
      intervalIntegral.integral_sub ((continuous_const.mul hcf_bot).intervalIntegrable _ _) (hcp_top.intervalIntegrable _ _),
      intervalIntegral.integral_sub (hcf_right.intervalIntegrable _ _) (hcp_right.intervalIntegrable _ _),
      intervalIntegral.integral_sub (hcf_left.intervalIntegrable _ _) (hcp_left.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral_inv_sub_I R, intervalIntegral_inv_add_I R] at hzero
    linear_combination hzero
  -- Take `R → ∞` on both sides of `hrect_eq R`.
  have hf_real_int : Integrable (fun x : ℝ ↦ f (x : ℂ)) := by
    have hbase : Integrable (fun x : ℝ ↦ (Real.cosh (Real.pi / 2 * x))⁻¹) :=
      (integrable_pow_abs_mul_inv_cosh (by positivity : 0 < Real.pi / 2) 0).congr
        (Eventually.of_forall fun x ↦ by simp)
    refine hbase.mono' ?_ (Eventually.of_forall fun x ↦ ?_)
    · dsimp only [f]
      exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).div
        (Complex.continuous_cosh.comp (continuous_const.mul Complex.continuous_ofReal)) fun x ↦ by
          dsimp only [Function.comp_apply, Pi.mul_apply]
          have : Complex.cosh ((Real.pi / 2 : ℝ) * (x : ℂ)) = (Real.cosh (Real.pi / 2 * x) : ℂ) := by
            rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]
          rw [this]; exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne').aestronglyMeasurable
    · dsimp only [f]
      have hnum : ‖Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))‖ = 1 := by
        rw [show Complex.I * (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) * Complex.I by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      have hden : ‖Complex.cosh ((Real.pi / 2 : ℝ) * (x : ℂ))‖ = Real.cosh (Real.pi / 2 * x) := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.cosh_pos _)]
      rw [norm_div, hnum, hden, one_div]
  have hlhs_f : Tendsto (fun R : ℝ ↦ ∫ x in (-R)..R, f (x : ℂ)) atTop (nhds (∫ x : ℝ, f (x : ℂ))) :=
    intervalIntegral_tendsto_integral hf_real_int tendsto_neg_atTop_atBot tendsto_id
  have hvert_f : ∀ s : ℝ, s = 1 ∨ s = -1 →
      Tendsto (fun R : ℝ ↦ ∫ y in (0 : ℝ)..2, f ((s * R : ℝ) + (y : ℂ) * Complex.I)) atTop (nhds 0) := by
    intro s hs
    have hupper : Tendsto (fun R : ℝ ↦ 2 * (Real.exp (2 * |t|) / Real.sinh (Real.pi / 2 * R)))
        atTop (nhds 0) := by
      have hsinh_top : Tendsto (fun R : ℝ ↦ Real.sinh (Real.pi / 2 * R)) atTop atTop := by
        have h1 : Tendsto (fun R : ℝ ↦ (Real.exp (Real.pi / 2 * R) - 1) / 2) atTop atTop :=
          ((Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop (by positivity) tendsto_id)).atTop_add
            tendsto_const_nhds).atTop_div_const (by norm_num)
        refine tendsto_atTop_mono' atTop ?_ h1
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
        rw [Real.sinh_eq]
        have : Real.exp (-(Real.pi / 2 * R)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
        linarith
      simpa using (tendsto_const_nhds.div_atTop hsinh_top).const_mul 2
    refine squeeze_zero_norm' ?_ hupper
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2)
      (C := Real.exp (2 * |t|) / Real.sinh (Real.pi / 2 * R))
      (f := fun y : ℝ ↦ f ((s * R : ℝ) + (y : ℂ) * Complex.I))
      (fun y hy ↦ by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hy
        dsimp only [f]
        rw [norm_div, Complex.norm_exp]
        have hre_exp : (Complex.I * (t : ℂ) * ((s * R : ℝ) + (y : ℂ) * Complex.I)).re = -(t * y) := by
          simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]; ring
        rw [hre_exp]
        have hnum_le : Real.exp (-(t * y)) ≤ Real.exp (2 * |t|) := by
          apply Real.exp_le_exp.mpr
          have : -(t * y) ≤ |t| * y := by nlinarith [neg_abs_le t, hy.1.le]
          nlinarith [hy.2, abs_nonneg t]
        have hden_ge : Real.sinh (Real.pi / 2 * R) ≤
            ‖Complex.cosh ((Real.pi / 2 : ℝ) * ((s * R : ℝ) + (y : ℂ) * Complex.I))‖ := by
          have h1 := abs_sinh_le_norm_cosh ((Real.pi / 2 : ℝ) * ((s * R : ℝ) + (y : ℂ) * Complex.I))
          have hre_c : ((Real.pi / 2 : ℝ) * ((s * R : ℝ) + (y : ℂ) * Complex.I)).re =
              s * (Real.pi / 2 * R) := by
            simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]; ring
          rw [hre_c] at h1
          have hspos : 0 < Real.sinh (Real.pi / 2 * R) := real_sinh_pos_of_pos (by positivity)
          rcases hs with rfl | rfl
          · rw [one_mul, abs_of_pos hspos] at h1; exact h1
          · rw [neg_one_mul, Real.sinh_neg, abs_neg, abs_of_pos hspos] at h1; exact h1
        exact div_le_div₀ (Real.exp_pos _).le hnum_le (real_sinh_pos_of_pos (by positivity)) hden_ge)
    simpa [abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm] using hbd
  have hvert_p : ∀ s : ℝ, s = 1 ∨ s = -1 →
      Tendsto (fun R : ℝ ↦ ∫ y in (0 : ℝ)..2, ((s * R : ℝ) + (y : ℂ) * Complex.I - Complex.I)⁻¹)
        atTop (nhds 0) := by
    intro s hs
    have hupper : Tendsto (fun R : ℝ ↦ 2 * R⁻¹) atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul 2
    refine squeeze_zero_norm' ?_ hupper
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hbd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2)
      (C := R⁻¹) (f := fun y : ℝ ↦ ((s * R : ℝ) + (y : ℂ) * Complex.I - Complex.I)⁻¹)
      (fun y _ ↦ by
        rw [norm_inv]
        apply inv_anti₀ hR
        have hre : ‖((s * R : ℝ) + (y : ℂ) * Complex.I - Complex.I)‖ ≥
            |(((s * R : ℝ) + (y : ℂ) * Complex.I - Complex.I)).re| := Complex.abs_re_le_norm _
        have hre_eq : (((s * R : ℝ) + (y : ℂ) * Complex.I - Complex.I)).re = s * R := by simp
        rw [hre_eq] at hre
        rcases hs with rfl | rfl
        · simpa [abs_of_pos hR] using hre
        · simpa [abs_of_pos hR] using hre)
    simpa [abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm] using hbd
  have hlhs_tend : Tendsto (fun R : ℝ ↦
      ((1 : ℂ) + Complex.exp (-2 * (t : ℂ))) * (∫ x in (-R)..R, f (x : ℂ)) +
      Complex.I * (∫ y in (0 : ℝ)..2, f ((R : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in (0 : ℝ)..2, f (-(R : ℂ) + (y : ℂ) * Complex.I)))
      atTop (nhds (((1 : ℂ) + Complex.exp (-2 * (t : ℂ))) * ∫ x : ℝ, f (x : ℂ))) := by
    have h1 := hlhs_f.const_mul ((1 : ℂ) + Complex.exp (-2 * (t : ℂ)))
    have h2 : Tendsto (fun R : ℝ ↦ Complex.I * ∫ y in (0 : ℝ)..2, f ((R : ℂ) + (y : ℂ) * Complex.I))
        atTop (nhds 0) := by
      simpa using (hvert_f 1 (Or.inl rfl)).const_mul Complex.I
    have h3 : Tendsto (fun R : ℝ ↦ Complex.I * ∫ y in (0 : ℝ)..2, f (-(R : ℂ) + (y : ℂ) * Complex.I))
        atTop (nhds 0) := by
      simpa [neg_one_mul] using (hvert_f (-1) (Or.inr rfl)).const_mul Complex.I
    simpa using (h1.add h2).sub h3
  have hrhs_tend : Tendsto (fun R : ℝ ↦
      res * (((4 * Real.arctan R : ℝ) : ℂ) * Complex.I +
        Complex.I * (∫ y in (0 : ℝ)..2, ((R : ℂ) + (y : ℂ) * Complex.I - Complex.I)⁻¹) -
        Complex.I * (∫ y in (0 : ℝ)..2, (-(R : ℂ) + (y : ℂ) * Complex.I - Complex.I)⁻¹)))
      atTop (nhds (res * (((2 * Real.pi : ℝ) : ℂ) * Complex.I))) := by
    have harc : Tendsto (fun R : ℝ ↦ ((4 * Real.arctan R : ℝ) : ℂ) * Complex.I)
        atTop (nhds (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) := by
      have h1 : Tendsto (fun R : ℝ ↦ 4 * Real.arctan R) atTop (nhds (2 * Real.pi)) := by
        have := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_mul 4
        convert this using 2; ring
      exact (Complex.continuous_ofReal.tendsto _).comp h1 |>.mul_const Complex.I
    have h2 : Tendsto (fun R : ℝ ↦ Complex.I * ∫ y in (0 : ℝ)..2, ((R : ℂ) + (y : ℂ) * Complex.I - Complex.I)⁻¹)
        atTop (nhds 0) := by
      simpa using (hvert_p 1 (Or.inl rfl)).const_mul Complex.I
    have h3 : Tendsto (fun R : ℝ ↦ Complex.I * ∫ y in (0 : ℝ)..2, (-(R : ℂ) + (y : ℂ) * Complex.I - Complex.I)⁻¹)
        atTop (nhds 0) := by
      simpa [neg_one_mul] using (hvert_p (-1) (Or.inr rfl)).const_mul Complex.I
    simpa using ((harc.add h2).sub h3).const_mul res
  have hlim_eq : ((1 : ℂ) + Complex.exp (-2 * (t : ℂ))) * (∫ x : ℝ, f (x : ℂ)) =
      res * (((2 * Real.pi : ℝ) : ℂ) * Complex.I) :=
    tendsto_nhds_unique (hlhs_tend.congr' (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR; exact hrect_eq R hR))
      hrhs_tend
  have hrhs_val : res * (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 4 * Complex.exp (-(t : ℂ)) := by
    dsimp only [res]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp [hpi]
    ring_nf; rw [Complex.I_sq]; ring
  have h1p_ne : (1 : ℂ) + Complex.exp (-2 * (t : ℂ)) ≠ 0 := by
    rw [show (1 : ℂ) + Complex.exp (-2 * (t : ℂ)) = ((1 + Real.exp (-2 * t) : ℝ) : ℂ) by
      rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_exp]; push_cast; rfl]
    exact Complex.ofReal_ne_zero.mpr (by linarith [Real.exp_pos (-2 * t)])
  have hf_int_val : ∫ x : ℝ, f (x : ℂ) = ((2 * (Real.cosh t)⁻¹ : ℝ) : ℂ) := by
    apply mul_left_cancel₀ h1p_ne
    rw [hlim_eq, hrhs_val]
    rw [show (1 : ℂ) + Complex.exp (-2 * (t : ℂ)) = ((1 + Real.exp (-2 * t) : ℝ) : ℂ) by
      rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_exp]; push_cast; rfl,
      show (4 : ℂ) * Complex.exp (-(t : ℂ)) = ((4 * Real.exp (-t) : ℝ) : ℂ) by
      rw [Complex.ofReal_mul, Complex.ofReal_exp]; push_cast; rfl,
      ← Complex.ofReal_mul]
    congr 1
    rw [Real.cosh_eq]
    have hden : Real.exp t + Real.exp (-t) ≠ 0 := by linarith [Real.exp_pos t, Real.exp_pos (-t)]
    have h2 : Real.exp (-2 * t) = Real.exp (-t) * Real.exp (-t) := by rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [h2]
    field_simp [hden]
    nlinarith [h3]
  -- Take real part of `∫ x : ℝ, f (x : ℂ) = 2 * (Real.cosh t)⁻¹`.
  have hre_int : ∫ x : ℝ, (f (x : ℂ)).re = 2 * (Real.cosh t)⁻¹ := by
    have h1 := Complex.reCLM.integral_comp_comm hf_real_int
    change ∫ x : ℝ, (f (x : ℂ)).re = (∫ x : ℝ, f (x : ℂ)).re at h1
    rw [h1, hf_int_val, Complex.ofReal_re]
  convert hre_int using 1
  congr 1; funext u
  dsimp only [f]
  have hden : Complex.cosh ((Real.pi / 2 : ℝ) * (u : ℂ)) = (Real.cosh (Real.pi * u / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]; congr 2; ring
  rw [hden, div_eq_mul_inv (Complex.exp _), ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have hnum_re : (Complex.exp (Complex.I * (t : ℂ) * (u : ℂ))).re = Real.cos (u * t) := by
    rw [show Complex.I * (t : ℂ) * (u : ℂ) = ((u * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, Complex.add_re, ← Complex.ofReal_cos, Complex.ofReal_re,
      ← Complex.ofReal_sin, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [hnum_re]

end SechFourierTransform

section MeixnerMomentIdentityAndLemma51

/-- Exact `k`-th derivative of `t ↦ ∫ u : ℝ, Real.cos (u * t) * (Real.cosh (Real.pi * u / 2))⁻¹`:
`iteratedDeriv k (...) t = ∫ u : ℝ, u ^ k * Real.cos (u * t + k * Real.pi / 2) * (Real.cosh (Real.pi * u / 2))⁻¹`. -/
lemma iteratedDeriv_sech_fourier (k : ℕ) :
    ∀ t : ℝ,
      iteratedDeriv k (fun s : ℝ ↦ ∫ u : ℝ, Real.cos (u * s) * (Real.cosh (Real.pi * u / 2))⁻¹) t =
        ∫ u : ℝ, u ^ k * Real.cos (u * t + (k : ℝ) * Real.pi / 2) * (Real.cosh (Real.pi * u / 2))⁻¹ := by
  induction k with
  | zero => intro t; simp
  | succ k ih =>
    intro t
    rw [iteratedDeriv_succ, show iteratedDeriv k (fun s : ℝ ↦ ∫ u : ℝ, Real.cos (u * s) * (Real.cosh (Real.pi * u / 2))⁻¹) =
      fun s ↦ ∫ u : ℝ, u ^ k * Real.cos (u * s + (k : ℝ) * Real.pi / 2) * (Real.cosh (Real.pi * u / 2))⁻¹ from funext ih]
    have hdom_int : Integrable (fun u : ℝ ↦ |u| ^ (k + 1) * (Real.cosh (Real.pi * u / 2))⁻¹) := by
      have h := integrable_pow_abs_mul_inv_cosh (by positivity : 0 < Real.pi / 2) (k + 1)
      convert h using 1; funext u; congr 2; ring
    have hdom_k : Integrable (fun u : ℝ ↦ |u| ^ k * (Real.cosh (Real.pi * u / 2))⁻¹) := by
      have h := integrable_pow_abs_mul_inv_cosh (by positivity : 0 < Real.pi / 2) k
      convert h using 1; funext u; congr 2; ring
    have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s u : ℝ ↦ u ^ k * Real.cos (u * s + (k : ℝ) * Real.pi / 2) * (Real.cosh (Real.pi * u / 2))⁻¹)
      (F' := fun s u : ℝ ↦ u ^ (k + 1) * Real.cos (u * s + ((k + 1 : ℕ) : ℝ) * Real.pi / 2) * (Real.cosh (Real.pi * u / 2))⁻¹)
      (s := Set.univ) (x₀ := t) (bound := fun u : ℝ ↦ |u| ^ (k + 1) * (Real.cosh (Real.pi * u / 2))⁻¹)
      Filter.univ_mem
      (Eventually.of_forall fun v ↦
        (((continuous_pow k).mul (Real.continuous_cos.comp ((continuous_id.mul continuous_const).add continuous_const))).mul
          ((Real.continuous_cosh.comp ((continuous_const.mul continuous_id).div_const 2)).inv₀ fun u ↦ (Real.cosh_pos _).ne')).aestronglyMeasurable)
      (hdom_k.mono'
        (((continuous_pow k).mul (Real.continuous_cos.comp ((continuous_id.mul continuous_const).add continuous_const))).mul
          ((Real.continuous_cosh.comp ((continuous_const.mul continuous_id).div_const 2)).inv₀ fun u ↦ (Real.cosh_pos _).ne')).aestronglyMeasurable
        (Eventually.of_forall fun u ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (inv_pos.mpr (Real.cosh_pos _))]
          calc |u| ^ k * |Real.cos (u * t + (k : ℝ) * Real.pi / 2)| * (Real.cosh (Real.pi * u / 2))⁻¹
              ≤ |u| ^ k * 1 * (Real.cosh (Real.pi * u / 2))⁻¹ := by
                gcongr; exact Real.abs_cos_le_one _
            _ = |u| ^ k * (Real.cosh (Real.pi * u / 2))⁻¹ := by ring))
      (((continuous_pow (k + 1)).mul (Real.continuous_cos.comp ((continuous_id.mul continuous_const).add continuous_const))).mul
        ((Real.continuous_cosh.comp ((continuous_const.mul continuous_id).div_const 2)).inv₀ fun u ↦ (Real.cosh_pos _).ne')).aestronglyMeasurable
      (Eventually.of_forall fun u v _ ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (inv_pos.mpr (Real.cosh_pos _))]
        calc |u| ^ (k + 1) * |Real.cos (u * v + ((k + 1 : ℕ) : ℝ) * Real.pi / 2)| * (Real.cosh (Real.pi * u / 2))⁻¹
            ≤ |u| ^ (k + 1) * 1 * (Real.cosh (Real.pi * u / 2))⁻¹ := by
              gcongr; exact Real.abs_cos_le_one _
          _ = |u| ^ (k + 1) * (Real.cosh (Real.pi * u / 2))⁻¹ := by ring)
      hdom_int
      (Eventually.of_forall fun u v _ ↦ by
        have hlin : HasDerivAt (fun s : ℝ ↦ u * s + (k : ℝ) * Real.pi / 2) u v := by
          simpa using ((hasDerivAt_id v).const_mul u).add_const ((k : ℝ) * Real.pi / 2)
        have hcos := (Real.hasDerivAt_cos _).comp v hlin
        have hmul := (hcos.const_mul (u ^ k)).mul_const (Real.cosh (Real.pi * u / 2))⁻¹
        dsimp only [Function.comp_apply] at hmul
        convert hmul using 1
        have hshift : Real.cos (u * v + ((k + 1 : ℕ) : ℝ) * Real.pi / 2) =
            -Real.sin (u * v + (k : ℝ) * Real.pi / 2) := by
          have : u * v + ((k + 1 : ℕ) : ℝ) * Real.pi / 2 =
              (u * v + (k : ℝ) * Real.pi / 2) + Real.pi / 2 := by push_cast; ring
          rw [this, Real.cos_add_pi_div_two]
        rw [hshift, pow_succ]; ring)
    exact hparam.2.deriv

/-- **Exact Meixner (`η = 1`) Moment–`sech`-Integral Identity (Unscaled `α₁ = 1`)**:
`((jacobiMat (2 * m + 1) (fun r ↦ (r : ℝ))) ^ (2 * m)) 0 0 = ∫ u in Set.Ioi (0 : ℝ), u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹`. -/
theorem jacobiMat_meixner_unit_moment_eq_sech_integral (m : ℕ) :
    ((jacobiMat (2 * m + 1) (fun r ↦ (r : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
      ∫ u in Set.Ioi (0 : ℝ), u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹ := by
  have h1 := iteratedDeriv_sech_fourier (2 * m) 0
  have hfun : (fun s : ℝ ↦ ∫ u : ℝ, Real.cos (u * s) * (Real.cosh (Real.pi * u / 2))⁻¹) =
      fun s : ℝ ↦ 2 * (Real.cosh s)⁻¹ := funext integral_cos_mul_inv_cosh_pi_half
  rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_inv_cosh_zero_eq_jacobiMat_pow] at h1
  have hcos : ∀ u : ℝ, Real.cos (u * 0 + ((2 * m : ℕ) : ℝ) * Real.pi / 2) = (-1 : ℝ) ^ m := by
    intro u
    rw [mul_zero, zero_add, show ((2 * m : ℕ) : ℝ) * Real.pi / 2 = (m : ℝ) * Real.pi by push_cast; ring,
      Real.cos_nat_mul_pi]
  simp_rw [hcos] at h1
  have hrew : (∫ u : ℝ, u ^ (2 * m) * (-1 : ℝ) ^ m * (Real.cosh (Real.pi * u / 2))⁻¹) =
      (-1 : ℝ) ^ m * ∫ u : ℝ, u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹ := by
    rw [← integral_const_mul]; congr 1; funext u; ring
  rw [hrew] at h1
  have hsign_ne : (-1 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  have hfull : 2 * ((jacobiMat (2 * m + 1) (fun r ↦ (r : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
      ∫ u : ℝ, u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹ := by
    apply mul_left_cancel₀ hsign_ne; linarith
  -- Split `∫_{-∞}^∞` into `2 * ∫_0^∞` by evenness of `u ^ (2 * m) / cosh (π u / 2)`.
  have hint : Integrable (fun u : ℝ ↦ u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹) := by
    have h := integrable_pow_abs_mul_inv_cosh (by positivity : 0 < Real.pi / 2) (2 * m)
    refine h.congr (Eventually.of_forall fun u ↦ ?_)
    dsimp only
    have : |u| ^ (2 * m) = u ^ (2 * m) := by rw [pow_mul, sq_abs, ← pow_mul]
    rw [this]; congr 2; ring
  have heven_split : ∫ u : ℝ, u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹ =
      2 * ∫ u in Set.Ioi (0 : ℝ), u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹ := by
    have hneg : ∫ u in Set.Iic (0 : ℝ), u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹ =
        ∫ u in Set.Ioi (0 : ℝ), u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹ := by
      have hcomp := integral_comp_neg_Ioi (f := fun u : ℝ ↦ u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹) 0
      rw [neg_zero] at hcomp
      rw [← hcomp]
      apply setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ ?_
      rw [Even.neg_pow (even_two_mul m), mul_neg, neg_div, Real.cosh_neg]
    have hunion : (∫ u in Set.Iic (0 : ℝ), u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹) +
        (∫ u in Set.Ioi (0 : ℝ), u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹) =
        ∫ u : ℝ, u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹ := by
      rw [← setIntegral_union (by rw [Set.disjoint_left]; intro x h1 h2; simp at h1 h2; linarith)
        measurableSet_Ioi hint.integrableOn hint.integrableOn, Set.Iic_union_Ioi, setIntegral_univ]
    linarith
  linarith

/-- **Exact Meixner (`η = 1`) Moment–`sech`-Integral Identity (Scaled `α₁ > 0`)**:
For every `α₁ > 0` and `m : ℕ`:
`((jacobiMat (2 * m + 1) (fun k ↦ α₁ * (k : ℝ))) ^ (2 * m)) 0 0 = (1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * m) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹`. -/
theorem jacobiMat_meixner_even_moment_eq_sech_integral {α₁ : ℝ} (hα : 0 < α₁) (m : ℕ) :
    ((jacobiMat (2 * m + 1) (fun k ↦ α₁ * (k : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
      (1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * m) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹ := by
  have hsmul : jacobiMat (2 * m + 1) (fun k ↦ α₁ * (k : ℝ)) =
      α₁ • jacobiMat (2 * m + 1) (fun k ↦ (k : ℝ)) := by
    ext i j; unfold jacobiMat; simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [hsmul, smul_pow, Matrix.smul_apply, smul_eq_mul, jacobiMat_meixner_unit_moment_eq_sech_integral m]
  -- Change of variables `ω = α₁ * u` on `(0, ∞)`.
  have hsub := integral_comp_mul_left_Ioi
    (fun ω : ℝ ↦ ω ^ (2 * m) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹) (0 : ℝ) hα
  rw [mul_zero] at hsub
  have hrew : (fun u : ℝ ↦ (α₁ * u) ^ (2 * m) * (Real.cosh (Real.pi * (α₁ * u) / (2 * α₁)))⁻¹) =
      fun u : ℝ ↦ α₁ ^ (2 * m) * (u ^ (2 * m) * (Real.cosh (Real.pi * u / 2))⁻¹) := by
    funext u
    rw [mul_pow, show Real.pi * (α₁ * u) / (2 * α₁) = Real.pi * u / 2 by field_simp [hα.ne']]
    ring
  rw [hrew, integral_const_mul, smul_eq_mul] at hsub
  rw [one_div, ← hsub]

/-- Entrywise monotonicity of powers of non-negative matrices. -/
private lemma mat_pow_mono_nonneg {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hAB : ∀ i j, A i j ≤ B i j) (k : ℕ) :
    ∀ i j, 0 ≤ (A ^ k) i j ∧ (A ^ k) i j ≤ (B ^ k) i j := by
  induction k with
  | zero =>
    intro i j; simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> constructor <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    constructor
    · exact Finset.sum_nonneg fun l _ ↦ mul_nonneg (ih i l).1 (hA l j)
    · refine Finset.sum_le_sum fun l _ ↦ ?_
      exact mul_le_mul (ih i l).2 (hAB l j) (hA l j) (le_trans (ih i l).1 (ih i l).2)

/-- Lower bound on `(jacobiMat D b ^ m) ⟨0, _⟩ ⟨m, _⟩` along the monotone ascending path `0 → 1 → ⋯ → m`. -/
private lemma jacobiMat_pow_asc_ge {D : ℕ} (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) :
    ∀ (m : ℕ) (hm : m < D),
      ∏ k ∈ Finset.range m, b (k + 1) ≤ ((jacobiMat D b) ^ m) ⟨0, by omega⟩ ⟨m, hm⟩ := by
  intro m
  induction m with
  | zero => intro hm; simp
  | succ m ih =>
    intro hm
    rw [Finset.prod_range_succ, pow_succ, Matrix.mul_apply]
    have hnn : ∀ l : Fin D, 0 ≤ ((jacobiMat D b) ^ m) ⟨0, by omega⟩ l * jacobiMat D b l ⟨m + 1, hm⟩ := by
      intro l
      have h1 := (mat_pow_mono_nonneg (jacobiMat D b) (jacobiMat D b)
        (fun i j ↦ by unfold jacobiMat; simp only [Matrix.of_apply]; split_ifs <;> [exact hb _; exact hb _; exact le_rfl])
        (fun _ _ ↦ le_rfl) m ⟨0, by omega⟩ l).1
      have h2 : 0 ≤ jacobiMat D b l ⟨m + 1, hm⟩ := by
        unfold jacobiMat; simp only [Matrix.of_apply]; split_ifs <;> [exact hb _; exact hb _; exact le_rfl]
      exact mul_nonneg h1 h2
    have hsingle := Finset.single_le_sum (fun l _ ↦ hnn l) (Finset.mem_univ (⟨m, by omega⟩ : Fin D))
    have hstep : jacobiMat D b ⟨m, by omega⟩ ⟨m + 1, hm⟩ = b (m + 1) := by
      unfold jacobiMat; simp only [Matrix.of_apply, ↓reduceIte]
    rw [hstep] at hsingle
    exact le_trans (mul_le_mul_of_nonneg_right (ih (by omega)) (hb (m + 1))) hsingle

/-- Lower bound on `(jacobiMat D b ^ m) ⟨m, _⟩ ⟨0, _⟩` along the monotone descending path `m → ⋯ → 0`. -/
private lemma jacobiMat_pow_desc_ge {D : ℕ} (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) :
    ∀ (m : ℕ) (hm : m < D),
      ∏ k ∈ Finset.range m, b (k + 1) ≤ ((jacobiMat D b) ^ m) ⟨m, hm⟩ ⟨0, by omega⟩ := by
  intro m hm
  have hsym : (jacobiMat D b)ᵀ = jacobiMat D b := by
    ext i j; unfold jacobiMat; simp only [Matrix.transpose_apply, Matrix.of_apply]
    by_cases h1 : i.val = j.val + 1
    · have h2 : ¬(j.val = i.val + 1) := by omega
      rw [if_pos h1, if_neg h2, if_pos h1]
    · by_cases h2 : j.val = i.val + 1
      · rw [if_neg h1, if_pos h2, if_pos h2]
      · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
  have hpow_sym : ((jacobiMat D b) ^ m)ᵀ = (jacobiMat D b) ^ m := by
    rw [Matrix.transpose_pow, hsym]
  have heq : ((jacobiMat D b) ^ m) ⟨m, hm⟩ ⟨0, by omega⟩ =
      ((jacobiMat D b) ^ m) ⟨0, by omega⟩ ⟨m, hm⟩ := by
    have := congrFun (congrFun hpow_sym ⟨0, by omega⟩) ⟨m, hm⟩
    exact this
  rw [heq]
  exact jacobiMat_pow_asc_ge b hb m hm

/-- Shifted-index comparison: if `b (N₀ + k) ≥ b' k ≥ 0` for all `k ≥ 1`, then for `N₀ + D' ≤ D`,
`((jacobiMat D' b') ^ m) i j ≤ ((jacobiMat D b) ^ m) ⟨N₀ + i, _⟩ ⟨N₀ + j, _⟩`. -/
private lemma jacobiMat_pow_shifted_ge {D D' N₀ : ℕ} (hsub : N₀ + D' ≤ D)
    (b b' : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k) (hb' : ∀ k, 0 ≤ b' k)
    (hge : ∀ k ≥ 1, b' k ≤ b (N₀ + k)) (m : ℕ) :
    ∀ (i j : Fin D'),
      0 ≤ ((jacobiMat D' b') ^ m) i j ∧
      ((jacobiMat D' b') ^ m) i j ≤
        ((jacobiMat D b) ^ m) ⟨N₀ + i.val, by omega⟩ ⟨N₀ + j.val, by omega⟩ := by
  induction m with
  | zero =>
    intro i j; simp only [pow_zero, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · have hne : (⟨N₀ + i.val, by omega⟩ : Fin D) ≠ ⟨N₀ + j.val, by omega⟩ := by
        intro heq; apply h; apply Fin.ext; have := congrArg Fin.val heq; dsimp at this; omega
      rw [if_neg h, if_neg hne]; exact ⟨le_rfl, le_rfl⟩
  | succ m ih =>
    intro i j
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    have hnn_b : ∀ l : Fin D, 0 ≤ ((jacobiMat D b) ^ m) ⟨N₀ + i.val, by omega⟩ l *
        jacobiMat D b l ⟨N₀ + j.val, by omega⟩ := by
      intro l
      have h1 := (mat_pow_mono_nonneg (jacobiMat D b) (jacobiMat D b)
        (fun a c ↦ by unfold jacobiMat; simp only [Matrix.of_apply]; split_ifs <;> [exact hb _; exact hb _; exact le_rfl])
        (fun _ _ ↦ le_rfl) m ⟨N₀ + i.val, by omega⟩ l).1
      have h2 : 0 ≤ jacobiMat D b l ⟨N₀ + j.val, by omega⟩ := by
        unfold jacobiMat; simp only [Matrix.of_apply]; split_ifs <;> [exact hb _; exact hb _; exact le_rfl]
      exact mul_nonneg h1 h2
    have hnn_b' : ∀ l : Fin D', 0 ≤ jacobiMat D' b' l j := by
      intro l; unfold jacobiMat; simp only [Matrix.of_apply]; split_ifs <;> [exact hb' _; exact hb' _; exact le_rfl]
    constructor
    · exact Finset.sum_nonneg fun l _ ↦ mul_nonneg (ih i l).1 (hnn_b' l)
    · let emb : Fin D' ↪ Fin D :=
        ⟨fun l ↦ ⟨N₀ + l.val, by omega⟩, fun l₁ l₂ h ↦ Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩
      have hle_sum : ∑ l : Fin D',
            ((jacobiMat D b) ^ m) ⟨N₀ + i.val, by omega⟩ (emb l) *
              jacobiMat D b (emb l) ⟨N₀ + j.val, by omega⟩ ≤
          ∑ l : Fin D,
            ((jacobiMat D b) ^ m) ⟨N₀ + i.val, by omega⟩ l *
              jacobiMat D b l ⟨N₀ + j.val, by omega⟩ := by
        have hm := Finset.sum_map Finset.univ emb
          (fun l : Fin D ↦ ((jacobiMat D b) ^ m) ⟨N₀ + i.val, by omega⟩ l *
            jacobiMat D b l ⟨N₀ + j.val, by omega⟩)
        rw [← hm]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun l _ _ ↦ hnn_b l)
      refine le_trans ?_ hle_sum
      apply Finset.sum_le_sum; intro l _
      have hemb_val : (emb l).val = N₀ + l.val := rfl
      have hstep_le : jacobiMat D' b' l j ≤ jacobiMat D b (emb l) ⟨N₀ + j.val, by omega⟩ := by
        unfold jacobiMat; simp only [Matrix.of_apply, hemb_val]
        by_cases h1 : j.val = l.val + 1
        · rw [if_pos h1, if_pos (by omega), show N₀ + l.val + 1 = N₀ + (l.val + 1) by omega]
          exact hge (l.val + 1) (by omega)
        · by_cases h2 : l.val = j.val + 1
          · rw [if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega),
              show N₀ + j.val + 1 = N₀ + (j.val + 1) by omega]
            exact hge (j.val + 1) (by omega)
          · rw [if_neg h1, if_neg h2, if_neg (by omega), if_neg (by omega)]
      exact mul_le_mul (ih i l).2 hstep_le (hnn_b' l) (le_trans (ih i l).1 (ih i l).2)

/-- **Lemma 5.1 (Eq. 5.5 — Verbatim Non-Asymptotic `sech`-Integral Comparison)**:
Let `b : ℕ → ℝ` satisfy `b k ≥ 0` for all `k` and `b k ≥ α₁ * k` for all `k > N₀` (with `α₁ > 0`).
Then for EVERY `n > N₀`:
1. `(∏ k ∈ Finset.range N₀, b (k + 1) ^ 2) * ((1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * (n - N₀)) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹) ≤ ((jacobiMat (2 * n + 1) b) ^ (2 * n)) 0 0`.
2. In particular, when `N₀ = 0` (`b k ≥ α₁ * k` for all `k ≥ 1`), for EVERY `n : ℕ`:
   `(1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * n) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹ ≤ ((jacobiMat (2 * n + 1) b) ^ (2 * n)) 0 0`. -/
theorem lemma_5_1_eq_5_5_exact_sech_comparison (b : ℕ → ℝ) (N₀ : ℕ) {α₁ : ℝ}
    (hα : 0 < α₁) (hb_nn : ∀ k, 0 ≤ b k) (hb_ge : ∀ k, N₀ < k → α₁ * (k : ℝ) ≤ b k)
    (n : ℕ) (hn : N₀ ≤ n) :
    (∏ k ∈ Finset.range N₀, b (k + 1) ^ 2) *
      ((1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ),
        ω ^ (2 * (n - N₀)) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹) ≤
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ := by
  set D : ℕ := 2 * n + 1
  set m : ℕ := n - N₀
  have h2n : 2 * n = N₀ + (2 * m + N₀) := by omega
  have hT_nn : ∀ i j : Fin D, 0 ≤ jacobiMat D b i j := fun i j ↦ by
    unfold jacobiMat; simp only [Matrix.of_apply]; split_ifs <;> [exact hb_nn _; exact hb_nn _; exact le_rfl]
  have hpow_nn : ∀ (k : ℕ) (i j : Fin D), 0 ≤ ((jacobiMat D b) ^ k) i j :=
    fun k i j ↦ (mat_pow_mono_nonneg _ _ hT_nn (fun _ _ ↦ le_rfl) k i j).1
  have hN0_lt : N₀ < D := by omega
  -- Factor `T^{2n} = T^{N₀} * T^{2m} * T^{N₀}` and pick the intermediate vertex `⟨N₀, hN0_lt⟩`.
  have hsplit : ((jacobiMat D b) ^ N₀) ⟨0, Nat.succ_pos _⟩ ⟨N₀, hN0_lt⟩ *
      ((jacobiMat D b) ^ (2 * m)) ⟨N₀, hN0_lt⟩ ⟨N₀, hN0_lt⟩ *
      ((jacobiMat D b) ^ N₀) ⟨N₀, hN0_lt⟩ ⟨0, Nat.succ_pos _⟩ ≤
      ((jacobiMat D b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ := by
    have hpow_eq : (jacobiMat D b) ^ (2 * n) =
        (jacobiMat D b) ^ N₀ * (jacobiMat D b) ^ (2 * m) * (jacobiMat D b) ^ N₀ := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [hpow_eq, Matrix.mul_apply]
    have h1 := Finset.single_le_sum
      (f := fun l : Fin D ↦ ((jacobiMat D b ^ N₀ * jacobiMat D b ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ l) *
        (jacobiMat D b ^ N₀) l ⟨0, Nat.succ_pos _⟩)
      (fun l _ ↦ mul_nonneg (by rw [← pow_add]; exact hpow_nn _ _ _) (hpow_nn _ _ _))
      (Finset.mem_univ (⟨N₀, hN0_lt⟩ : Fin D))
    have h2 : ((jacobiMat D b) ^ N₀) ⟨0, Nat.succ_pos _⟩ ⟨N₀, hN0_lt⟩ *
        ((jacobiMat D b) ^ (2 * m)) ⟨N₀, hN0_lt⟩ ⟨N₀, hN0_lt⟩ ≤
        (jacobiMat D b ^ N₀ * jacobiMat D b ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨N₀, hN0_lt⟩ := by
      rw [Matrix.mul_apply]
      exact Finset.single_le_sum
        (f := fun l : Fin D ↦ ((jacobiMat D b) ^ N₀) ⟨0, Nat.succ_pos _⟩ l * ((jacobiMat D b) ^ (2 * m)) l ⟨N₀, hN0_lt⟩)
        (fun l _ ↦ mul_nonneg (hpow_nn _ _ _) (hpow_nn _ _ _)) (Finset.mem_univ (⟨N₀, hN0_lt⟩ : Fin D))
    exact le_trans (mul_le_mul_of_nonneg_right h2 (hpow_nn _ _ _)) h1
  -- Lower bound each of the 3 factors: ascending `∏ b_k`, shifted Meixner `sech` integral, descending `∏ b_k`.
  have hasc := jacobiMat_pow_asc_ge (D := D) b hb_nn N₀ hN0_lt
  have hdesc := jacobiMat_pow_desc_ge (D := D) b hb_nn N₀ hN0_lt
  have hmid := (jacobiMat_pow_shifted_ge (D := D) (D' := 2 * m + 1) (N₀ := N₀) (by omega)
    b (fun k ↦ α₁ * (k : ℝ)) hb_nn (fun k ↦ by positivity)
    (fun k hk ↦ by
      have hle1 : α₁ * (k : ℝ) ≤ α₁ * ((N₀ + k : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hα.le; exact_mod_cast (by omega : k ≤ N₀ + k)
      exact le_trans hle1 (hb_ge (N₀ + k) (by omega)))
    (2 * m) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩).2
  have hmid_eq : ((jacobiMat (2 * m + 1) (fun k ↦ α₁ * (k : ℝ))) ^ (2 * m)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
      (1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * m) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹ :=
    jacobiMat_meixner_even_moment_eq_sech_integral hα m
  rw [hmid_eq] at hmid
  have hprod_sq : (∏ k ∈ Finset.range N₀, b (k + 1)) * (∏ k ∈ Finset.range N₀, b (k + 1)) =
      ∏ k ∈ Finset.range N₀, b (k + 1) ^ 2 := by
    rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro k _; ring
  have hprod_nn : 0 ≤ ∏ k ∈ Finset.range N₀, b (k + 1) :=
    Finset.prod_nonneg fun k _ ↦ hb_nn (k + 1)
  have hint_nn : 0 ≤ (1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * m) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹ :=
    mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun ω _ ↦
      mul_nonneg (Even.pow_nonneg (even_two_mul m) ω) (inv_nonneg.mpr (Real.cosh_pos _).le))
  have hcomb : (∏ k ∈ Finset.range N₀, b (k + 1) ^ 2) *
      ((1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * m) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹) ≤
      ((jacobiMat D b) ^ N₀) ⟨0, Nat.succ_pos _⟩ ⟨N₀, hN0_lt⟩ *
      ((jacobiMat D b) ^ (2 * m)) ⟨N₀, hN0_lt⟩ ⟨N₀, hN0_lt⟩ *
      ((jacobiMat D b) ^ N₀) ⟨N₀, hN0_lt⟩ ⟨0, Nat.succ_pos _⟩ := by
    rw [← hprod_sq]
    calc (∏ k ∈ Finset.range N₀, b (k + 1)) * (∏ k ∈ Finset.range N₀, b (k + 1)) *
            ((1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * m) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹)
        = (∏ k ∈ Finset.range N₀, b (k + 1)) *
            ((1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * m) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹) *
            (∏ k ∈ Finset.range N₀, b (k + 1)) := by ring
      _ ≤ ((jacobiMat D b) ^ N₀) ⟨0, Nat.succ_pos _⟩ ⟨N₀, hN0_lt⟩ *
            ((jacobiMat D b) ^ (2 * m)) ⟨N₀, hN0_lt⟩ ⟨N₀, hN0_lt⟩ *
            ((jacobiMat D b) ^ N₀) ⟨N₀, hN0_lt⟩ ⟨0, Nat.succ_pos _⟩ := by
          have h12 : (∏ k ∈ Finset.range N₀, b (k + 1)) *
              ((1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * m) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹) ≤
              ((jacobiMat D b) ^ N₀) ⟨0, Nat.succ_pos _⟩ ⟨N₀, hN0_lt⟩ *
              ((jacobiMat D b) ^ (2 * m)) ⟨N₀, hN0_lt⟩ ⟨N₀, hN0_lt⟩ :=
            mul_le_mul hasc (by simpa using hmid) hint_nn (hpow_nn _ _ _)
          exact mul_le_mul h12 hdesc hprod_nn (mul_nonneg (hpow_nn _ _ _) (hpow_nn _ _ _))
  exact le_trans hcomb hsplit

end MeixnerMomentIdentityAndLemma51

end KrylovChaos
