/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.GibbsConstruction
import KrylovChaos.Filtration
import KrylovChaos.BimodalExact
import KrylovChaos.SpectralSmearingAndDoubleWell
import KrylovChaos.Milestone4StructuralNecessity
import KrylovChaos.Milestone4Section9AppB
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# Structural Necessity, Fixed-σ Gaussian OTOC Preservation, and D × D Double-Well Tunneling
# (Proposition 9.1(1)–(3) and Lemma B.1)

Formalizes Section 9 and Appendix B strictly on top of Mathlib:
1. **Proposition 9.1(1) (Fixed-`σ > 0` Gaussian-Smeared OTOC Lyapunov Preservation)**:
   Proves `∫ s, gaussianKernel σ s = 1`, `∫ s, gaussianKernel σ s * exp(a * s) = exp(σ² a² / 2)`,
   and concludes that fixed-`σ` Gaussian smearing preserves the Lyapunov exponent `λ_L` of any
   OTOC `F(t) = F_d - ε e^{λ_L t} + R(t)` with only a positive constant prefactor shift.
2. **Proposition 9.1(2) (Direct Bimodal Violation of Hypothesis (H2) for ALL `δ ∈ [0, 1)`)**:
   Wires `prop_9_1_bimodal_operator_exact_size` directly into the inequality
   `C₁ * 1 + C₂ * N^δ * 1^(1 - δ) < Re (⟨𝒥(A), 𝒮 𝒥(A)⟩_HS - ⟨ρ^{1/2}, 𝒮 ρ^{1/2}⟩_HS)`.
3. **Lemma B.1 (Actual `D × D` Real Symmetric Tridiagonal Double-Well Matrix `ℒ`, `D ≥ 4, E_B > 2`)**:
   Constructs `doubleWellTridiag D E_B : Matrix (Fin D) (Fin D) ℝ` and `parityMat D`, and proves:
   - Real symmetry and parity commutation `P ℒ = ℒ P`, `P² = 1`.
   - Sturm simplicity (`v_0 = 0 → v = 0`, every eigenspace is 1-dimensional).
   - Definite parity of every eigenvector (`P v = v` or `P v = -v`).
   - Eigenvalue localization (`-(E_B - 2)⁻¹ ≤ E ≤ E_B + 2`, with exactly 2 distinct eigenvalues
     in `[-(E_B - 2)⁻¹, 0]` and the remaining `D - 2` eigenvalues in `[E_B - 2, E_B + 2]`).
   - Discrete maximum principle yielding exponential eigenvector decay Eq. (B.2)
     `|v_j| ≤ |v_0| (q^j + q^{D - 1 - j})` (`q = (E_B - √(E_B² - 4)) / 2 < 1`) and
     boundary localization Eq. (B.3) `1 - 2 v_0² ≤ 4 (q² / (1 - q²)) v_0²`.
4. **Proposition 9.1(3) (Exact `D`-Dimensional Limit Eq. 9.3)**:
   Proves `Tendsto (fun E_B ↦ ΔQ(E_B) / (K(E_B) + σ₀(E_B) * √(K(E_B)))) atTop (nhds ((D : ℝ) - 1))`
   using the exact boundary localization `q(E_B) → 0` as `E_B → ∞`.
-/

namespace KrylovChaos

open Matrix MeasureTheory Filter Topology

section Prop91Part1FixedSigmaOTOC

/-- Normalization of the Gaussian smearing kernel: `∫ s, gaussianKernel σ s = 1` for `σ > 0`. -/
theorem integral_gaussianKernel_eq_one {σ : ℝ} (hσ : 0 < σ) :
    ∫ s : ℝ, gaussianKernel σ s = 1 := by
  unfold gaussianKernel
  rw [integral_div]
  have hrew : (fun s : ℝ ↦ Real.exp (-(s ^ 2) / (2 * σ ^ 2))) =
      fun s : ℝ ↦ Real.exp (-(1 / (2 * σ ^ 2)) * s ^ 2) := by
    funext s; congr 1; ring
  rw [hrew, integral_gaussian (1 / (2 * σ ^ 2))]
  have hpi : Real.sqrt (Real.pi / (1 / (2 * σ ^ 2))) = Real.sqrt (2 * Real.pi) * σ := by
    rw [div_div_eq_mul_div, div_one, show Real.pi * (2 * σ ^ 2) = (2 * Real.pi) * σ ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hσ.le]
  rw [hpi, div_self (by positivity)]

/-- Laplace transform of the Gaussian smearing kernel:
`∫ s, gaussianKernel σ s * exp (a * s) = exp (σ² a² / 2)` for `σ > 0`. -/
theorem integral_gaussianKernel_mul_exp {σ : ℝ} (hσ : 0 < σ) (a : ℝ) :
    ∫ s : ℝ, gaussianKernel σ s * Real.exp (a * s) = Real.exp (σ ^ 2 * a ^ 2 / 2) := by
  unfold gaussianKernel
  have hrew : (fun s : ℝ ↦ Real.exp (-(s ^ 2) / (2 * σ ^ 2)) / (Real.sqrt (2 * Real.pi) * σ) *
        Real.exp (a * s)) =
      fun s : ℝ ↦ (Real.exp (σ ^ 2 * a ^ 2 / 2) / (Real.sqrt (2 * Real.pi) * σ)) *
        Real.exp (-(1 / (2 * σ ^ 2)) * (s - a * σ ^ 2) ^ 2) := by
    funext s
    rw [div_mul_eq_mul_div, ← Real.exp_add, div_mul_eq_mul_div, ← Real.exp_add]
    congr 1; congr 1
    field_simp [hσ.ne']; ring
  rw [hrew, integral_const_mul, integral_sub_right_eq_self
    (fun s : ℝ ↦ Real.exp (-(1 / (2 * σ ^ 2)) * s ^ 2)) (a * σ ^ 2),
    integral_gaussian (1 / (2 * σ ^ 2))]
  have hpi : Real.sqrt (Real.pi / (1 / (2 * σ ^ 2))) = Real.sqrt (2 * Real.pi) * σ := by
    rw [div_div_eq_mul_div, div_one, show Real.pi * (2 * σ ^ 2) = (2 * Real.pi) * σ ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hσ.le]
  rw [hpi, div_mul_cancel₀ _ (by positivity)]

/-- Integrability of `gaussianKernel σ s * exp (a * s)` for `σ > 0`. -/
lemma integrable_gaussianKernel_mul_exp {σ : ℝ} (hσ : 0 < σ) (a : ℝ) :
    Integrable (fun s : ℝ ↦ gaussianKernel σ s * Real.exp (a * s)) := by
  have hrew : (fun s : ℝ ↦ gaussianKernel σ s * Real.exp (a * s)) =
      fun s : ℝ ↦ (Real.exp (σ ^ 2 * a ^ 2 / 2) / (Real.sqrt (2 * Real.pi) * σ)) *
        Real.exp (-(1 / (2 * σ ^ 2)) * (s - a * σ ^ 2) ^ 2) := by
    funext s; unfold gaussianKernel
    rw [div_mul_eq_mul_div, ← Real.exp_add, div_mul_eq_mul_div, ← Real.exp_add]
    congr 1; congr 1; field_simp [hσ.ne']; ring
  rw [hrew]
  have hb : 0 < 1 / (2 * σ ^ 2) := by positivity
  have hint0 : Integrable (fun s : ℝ ↦ Real.exp (-(1 / (2 * σ ^ 2)) * s ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  exact (hint0.comp_sub_right (a * σ ^ 2)).const_mul _

/-- **Proposition 9.1(1) (Fixed-`σ > 0` Gaussian-Smeared OTOC Lyapunov Preservation)**:
If `F : ℝ → ℝ` is measurable and obeys the Lyapunov-regime ansatz
`|F s - (F_d - ε * exp (lamL * s))| ≤ C_R` for all `s : ℝ`, then at ANY fixed smearing width
`σ > 0`, the Gaussian-smeared OTOC `F_σ t := ∫ s, gaussianKernel σ s * F (t + s)` preserves
the exact Lyapunov exponent `lamL` with positive constant prefactor shift `exp (σ² lamL² / 2)`:
`|F_σ t - (F_d - (ε * exp (σ² lamL² / 2)) * exp (lamL * t))| ≤ C_R`. -/
theorem prop_9_1_part1_fixed_sigma_otoc_lyapunov {σ : ℝ} (hσ : 0 < σ)
    (F : ℝ → ℝ) (hF_meas : AEStronglyMeasurable F volume)
    (F_d ε lamL C_R : ℝ) (hCR : 0 ≤ C_R)
    (hF_err : ∀ s : ℝ, |F s - (F_d - ε * Real.exp (lamL * s))| ≤ C_R) (t : ℝ) :
    |(∫ s : ℝ, gaussianKernel σ s * F (t + s)) -
      (F_d - (ε * Real.exp (σ ^ 2 * lamL ^ 2 / 2)) * Real.exp (lamL * t))| ≤ C_R := by
  have hg_nn : ∀ s : ℝ, 0 ≤ gaussianKernel σ s := fun s ↦ by
    unfold gaussianKernel; positivity
  have hg_int : Integrable (fun s : ℝ ↦ gaussianKernel σ s) := by
    simpa using integrable_gaussianKernel_mul_exp hσ 0
  have hexp_int : Integrable (fun s : ℝ ↦ gaussianKernel σ s * Real.exp (lamL * s)) :=
    integrable_gaussianKernel_mul_exp hσ lamL
  let model : ℝ → ℝ := fun s ↦ F_d - ε * Real.exp (lamL * (t + s))
  have hmodel_int : Integrable (fun s : ℝ ↦ gaussianKernel σ s * model s) := by
    have hrew : (fun s : ℝ ↦ gaussianKernel σ s * model s) =
        fun s : ℝ ↦ F_d * gaussianKernel σ s -
          (ε * Real.exp (lamL * t)) * (gaussianKernel σ s * Real.exp (lamL * s)) := by
      funext s; dsimp only [model]; rw [mul_add, Real.exp_add]; ring
    rw [hrew]
    exact (hg_int.const_mul F_d).sub (hexp_int.const_mul _)
  have hmodel_val : ∫ s : ℝ, gaussianKernel σ s * model s =
      F_d - (ε * Real.exp (σ ^ 2 * lamL ^ 2 / 2)) * Real.exp (lamL * t) := by
    have hrew : (fun s : ℝ ↦ gaussianKernel σ s * model s) =
        fun s : ℝ ↦ F_d * gaussianKernel σ s -
          (ε * Real.exp (lamL * t)) * (gaussianKernel σ s * Real.exp (lamL * s)) := by
      funext s; dsimp only [model]; rw [mul_add, Real.exp_add]; ring
    rw [hrew, integral_sub (hg_int.const_mul F_d) (hexp_int.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_gaussianKernel_eq_one hσ, integral_gaussianKernel_mul_exp hσ lamL]
    ring
  have hdiff_int : Integrable (fun s : ℝ ↦ gaussianKernel σ s * (F (t + s) - model s)) := by
    refine (hg_int.const_mul C_R).mono' ?_ (Filter.Eventually.of_forall fun s ↦ ?_)
    · have h1 : AEStronglyMeasurable (fun s : ℝ ↦ F (t + s)) volume := by
        have hmp : MeasurePreserving (fun s : ℝ ↦ t + s) volume volume :=
          measurePreserving_add_left volume t
        exact hF_meas.comp_measurePreserving hmp
      have h2 : AEStronglyMeasurable model volume :=
        (continuous_const.sub (continuous_const.mul
          (Real.continuous_exp.comp (continuous_const.mul (continuous_const.add continuous_id))))).aestronglyMeasurable
      have h3 : AEStronglyMeasurable (fun s : ℝ ↦ gaussianKernel σ s) volume :=
        hg_int.aestronglyMeasurable
      exact h3.mul (h1.sub h2)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg_nn s)]
      calc gaussianKernel σ s * |F (t + s) - model s|
          ≤ gaussianKernel σ s * C_R := mul_le_mul_of_nonneg_left (hF_err (t + s)) (hg_nn s)
        _ = C_R * gaussianKernel σ s := mul_comm _ _
  have hF_int : Integrable (fun s : ℝ ↦ gaussianKernel σ s * F (t + s)) := by
    have heq : (fun s : ℝ ↦ gaussianKernel σ s * F (t + s)) =
        fun s : ℝ ↦ gaussianKernel σ s * (F (t + s) - model s) + gaussianKernel σ s * model s := by
      funext s; ring
    rw [heq]
    exact hdiff_int.add hmodel_int
  have hsub_eq : (∫ s : ℝ, gaussianKernel σ s * F (t + s)) -
      (F_d - (ε * Real.exp (σ ^ 2 * lamL ^ 2 / 2)) * Real.exp (lamL * t)) =
      ∫ s : ℝ, gaussianKernel σ s * (F (t + s) - model s) := by
    rw [← hmodel_val, ← integral_sub hF_int hmodel_int]
    congr 1; funext s; ring
  rw [hsub_eq]
  calc |∫ s : ℝ, gaussianKernel σ s * (F (t + s) - model s)|
      ≤ ∫ s : ℝ, |gaussianKernel σ s * (F (t + s) - model s)| := abs_integral_le_integral_abs
    _ ≤ ∫ s : ℝ, C_R * gaussianKernel σ s := by
        refine integral_mono hdiff_int.abs (hg_int.const_mul C_R) fun s ↦ ?_
        rw [abs_mul, abs_of_nonneg (hg_nn s)]
        calc gaussianKernel σ s * |F (t + s) - model s|
            ≤ gaussianKernel σ s * C_R := mul_le_mul_of_nonneg_left (hF_err (t + s)) (hg_nn s)
          _ = C_R * gaussianKernel σ s := mul_comm _ _
    _ = C_R := by rw [integral_const_mul, integral_gaussianKernel_eq_one hσ, mul_one]

end Prop91Part1FixedSigmaOTOC

section Prop91Part2BimodalDirectH2Violation

/-- **Proposition 9.1(2) (Direct Bimodal Operator Violation of Hypothesis (H2) for ALL `δ ∈ [0, 1)`)**:
Directly wires `prop_9_1_bimodal_operator_exact_size` (exact thermal size `N - 1` of the 1-local
bimodal operator) to prove that for EVERY `δ ∈ [0, 1)` and ANY constants `C₁, C₂ ≥ 0`, there exists
`N₀ ≥ 2` such that for all `N ≥ N₀`:
`C₁ * 1 + C₂ * N^δ * 1^(1 - δ) < Re (⟨𝒥(A), 𝒮 𝒥(A)⟩_HS - ⟨ρ^{1/2}, 𝒮 ρ^{1/2}⟩_HS)`. -/
theorem prop_9_1_part2_bimodal_direct_H2_violation {δ C₁ C₂ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ (N₀ : ℕ) (hN₀ : 2 ≤ N₀), ∀ (N : ℕ) (hN : N₀ ≤ N) (x : Fin N),
      have hN2 : 2 ≤ N := le_trans hN₀ hN
      pauliSite x 3 ∈ filtrationSubmodule N 1 ∧
      C₁ * (1 : ℝ) + C₂ * (N : ℝ) ^ δ * (1 : ℝ) ^ (1 - δ) <
        (hsInner (Matrix.diagonal (fun s ↦ (bimodalJADiag hN2 s : ℂ)))
          (totalSizeOp (Matrix.diagonal (fun s ↦ (bimodalJADiag hN2 s : ℂ))))).re -
        (hsInner (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN2 s : ℂ)))
          (totalSizeOp (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN2 s : ℂ))))).re := by
  rcases prop_9_1_part2_violates_H2_all_delta hδ0 hδ1 (by positivity : 0 ≤ 4 * C₁)
    (by positivity : 0 ≤ 4 * C₂) with ⟨N₀, hN₀, hmain⟩
  refine ⟨N₀, hN₀, fun N hN x ↦ ?_⟩
  have hN2 : 2 ≤ N := le_trans hN₀ hN
  rcases hmain N hN x with ⟨hmem, S, hS_eq, hlt⟩
  have hexact := prop_9_1_bimodal_operator_exact_size (N := N) hN2
  have hS : S = (N : ℝ) - 1 := by exact_mod_cast hS_eq
  rw [hS] at hlt
  have hpos : 0 < (Real.sqrt ((2 : ℝ) ^ (N + 1)))⁻¹ := by positivity
  refine ⟨hmem, ?_⟩
  rw [hexact]
  linarith

end Prop91Part2BimodalDirectH2Violation

section LemmaB1DoubleWellTridiagonal

/-- Actual `D × D` real symmetric tridiagonal double-well matrix `ℒ(E_B)` from Appendix B:
diagonal `(0, E_B, ..., E_B, 0)` and unit super- and sub-diagonals `b_j = 1`. -/
def doubleWellTridiag (D : ℕ) (E_B : ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun i j ↦
    if i = j then (if i.val = 0 ∨ i.val = D - 1 then 0 else E_B)
    else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1
    else 0

/-- Parity reflection matrix `P` on `Fin D`: `P_{i, j} = δ_{i + j + 1, D}`. -/
def parityMat (D : ℕ) : Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun i j ↦ if i.val + j.val + 1 = D then 1 else 0

/-- Reflection index `j ↦ D - 1 - j` on `Fin D`. -/
def revFin {D : ℕ} (i : Fin D) : Fin D :=
  ⟨D - 1 - i.val, by omega⟩

lemma revFin_revFin {D : ℕ} (i : Fin D) : revFin (revFin i) = i := by
  ext; simp only [revFin]; omega

lemma parityMat_mulVec {D : ℕ} (v : Fin D → ℝ) (i : Fin D) :
    (parityMat D *ᵥ v) i = v (revFin i) := by
  simp only [Matrix.mulVec, dotProduct, parityMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (revFin i)]
  · have h : i.val + (revFin i).val + 1 = D := by simp only [revFin]; omega
    simp [h]
  · intro j _ hne
    have h : ¬(i.val + j.val + 1 = D) := by
      intro heq; apply hne; ext; simp only [revFin]; omega
    simp [h]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma parityMat_mul_self (D : ℕ) : parityMat D * parityMat D = 1 := by
  ext i j
  simp only [Matrix.mul_apply, parityMat, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (revFin i)]
  · have hi : i.val + (revFin i).val + 1 = D := by simp only [revFin]; omega
    by_cases hij : i = j
    · subst hij; simp [hi, add_comm]
    · have hj : ¬((revFin i).val + j.val + 1 = D) := by
        intro h; apply hij; ext; simp only [revFin] at h; omega
      simp [hi, hj, hij]
  · intro k _ hne
    have hk : ¬(i.val + k.val + 1 = D) := by
      intro h; apply hne; ext; simp only [revFin]; omega
    simp [hk]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma doubleWellTridiag_isHermitian (D : ℕ) (E_B : ℝ) :
    (doubleWellTridiag D E_B).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, doubleWellTridiag, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, ↓reduceIte, or_comm]

lemma doubleWellTridiag_comm_parityMat (D : ℕ) (E_B : ℝ) :
    parityMat D * doubleWellTridiag D E_B = doubleWellTridiag D E_B * parityMat D := by
  ext i j
  simp only [Matrix.mul_apply, parityMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (revFin i), Finset.sum_eq_single (revFin j)]
  · have hi : i.val + (revFin i).val + 1 = D := by simp only [revFin]; omega
    have hj : (revFin j).val + j.val + 1 = D := by simp only [revFin]; omega
    simp only [hi, hj, ↓reduceIte, one_mul, mul_one, doubleWellTridiag, Matrix.of_apply]
    by_cases heq : revFin i = j
    · have heq' : i = revFin j := by rw [← heq, revFin_revFin]
      simp only [heq, heq', revFin_revFin, ↓reduceIte]
      have hiff : (j.val = 0 ∨ j.val = D - 1) ↔ ((revFin j).val = 0 ∨ (revFin j).val = D - 1) := by
        simp only [revFin]; omega
      by_cases hj0 : (revFin j).val = 0 ∨ (revFin j).val = D - 1
      · rw [if_pos (hiff.mpr hj0), if_pos hj0]
      · rw [if_neg (fun h ↦ hj0 (hiff.mp h)), if_neg hj0]
    · have heq' : i ≠ revFin j := fun h ↦ heq (by rw [h, revFin_revFin])
      simp only [heq, heq', ↓reduceIte]
      have hiff : ((revFin i).val + 1 = j.val ∨ j.val + 1 = (revFin i).val) ↔
          (i.val + 1 = (revFin j).val ∨ (revFin j).val + 1 = i.val) := by
        simp only [revFin]; omega
      simp [hiff]
  · intro k _ hne
    have hk : ¬(k.val + j.val + 1 = D) := by
      intro h; apply hne; ext; simp only [revFin]; omega
    simp [hk]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro k _ hne
    have hk : ¬(i.val + k.val + 1 = D) := by
      intro h; apply hne; ext; simp only [revFin]; omega
    simp [hk]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Action of `doubleWellTridiag D E_B` on any vector `v : Fin D → ℝ` at index `i`. -/
lemma doubleWellTridiag_mulVec_apply {D : ℕ} (hD : 2 ≤ D) (E_B : ℝ) (v : Fin D → ℝ) (i : Fin D) :
    (doubleWellTridiag D E_B *ᵥ v) i =
      (if i.val = 0 ∨ i.val = D - 1 then 0 else E_B) * v i +
      (if h : 0 < i.val then v ⟨i.val - 1, by omega⟩ else 0) +
      (if h : i.val + 1 < D then v ⟨i.val + 1, h⟩ else 0) := by
  simp only [Matrix.mulVec, dotProduct, doubleWellTridiag, Matrix.of_apply]
  let S : Finset (Fin D) :=
    ({i} ∪ (if h : 0 < i.val then {⟨i.val - 1, by omega⟩} else ∅)) ∪
    (if h : i.val + 1 < D then {⟨i.val + 1, h⟩} else ∅)
  have hzero : ∀ j ∈ Finset.univ, j ∉ S →
      (if i = j then (if i.val = 0 ∨ i.val = D - 1 then 0 else E_B)
       else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0) * v j = 0 := by
    intro j _ hj
    have h1 : i ≠ j := fun heq ↦ hj (by subst heq; simp [S])
    have h2 : ¬(i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
      rintro (h | h)
      · apply hj; simp only [S, Finset.mem_union]
        right; rw [dif_pos (by omega)]; simp [Fin.ext_iff, h]
      · apply hj; simp only [S, Finset.mem_union]
        left; right; rw [dif_pos (by omega)]; simp only [Finset.mem_singleton, Fin.ext_iff]; omega
    simp [h1, h2]
  rw [← Finset.sum_subset (Finset.subset_univ S) hzero]
  by_cases h0 : 0 < i.val <;> by_cases h1 : i.val + 1 < D
  · set im : Fin D := ⟨i.val - 1, by omega⟩
    set ip : Fin D := ⟨i.val + 1, h1⟩
    have hS : S = {i, im, ip} := by ext j; simp [S, h0, h1, im, ip]; tauto
    have him_ne : i ≠ im := by intro h; have := congrArg Fin.val h; simp [im] at this; omega
    have hip_ne : i ≠ ip := by intro h; have := congrArg Fin.val h; simp [ip] at this
    have hmp_ne : im ≠ ip := by intro h; have := congrArg Fin.val h; simp [im, ip] at this; omega
    rw [hS, Finset.sum_insert (by simp [him_ne, hip_ne]),
      Finset.sum_insert (by simp [hmp_ne]), Finset.sum_singleton]
    have him_adj : i.val + 1 = im.val ∨ im.val + 1 = i.val := Or.inr (by simp [im]; omega)
    have hip_adj : i.val + 1 = ip.val ∨ ip.val + 1 = i.val := Or.inl (by simp [ip])
    simp only [↓reduceIte, him_ne, hip_ne, him_adj, hip_adj, one_mul, h0, h1, ↓reduceDIte]
    ring
  · set im : Fin D := ⟨i.val - 1, by omega⟩
    have hS : S = {i, im} := by ext j; simp [S, h0, h1, im]
    have him_ne : i ≠ im := by intro h; have := congrArg Fin.val h; simp [im] at this; omega
    rw [hS, Finset.sum_insert (by simp [him_ne]), Finset.sum_singleton]
    have him_adj : i.val + 1 = im.val ∨ im.val + 1 = i.val := Or.inr (by simp [im]; omega)
    simp only [↓reduceIte, him_ne, him_adj, one_mul, h0, h1, ↓reduceDIte, add_zero]; rfl
  · set ip : Fin D := ⟨i.val + 1, h1⟩
    have hS : S = {i, ip} := by ext j; simp [S, h0, h1, ip]
    have hip_ne : i ≠ ip := by intro h; have := congrArg Fin.val h; simp [ip] at this
    rw [hS, Finset.sum_insert (by simp [hip_ne]), Finset.sum_singleton]
    have hip_adj : i.val + 1 = ip.val ∨ ip.val + 1 = i.val := Or.inl (by simp [ip])
    simp only [↓reduceIte, hip_ne, hip_adj, one_mul, h0, h1, ↓reduceDIte, add_zero]; rfl
  · omega

/-- **Sturm Simplicity (Lemma B.1)**: If `(doubleWellTridiag D E_B) *ᵥ v = E • v` and `v 0 = 0`,
then `v = 0`. Consequently every eigenvalue of `doubleWellTridiag D E_B` is simple! -/
theorem doubleWellTridiag_sturm_zero {D : ℕ} (hD : 2 ≤ D) (E_B E : ℝ) (v : Fin D → ℝ)
    (heig : doubleWellTridiag D E_B *ᵥ v = E • v) (hv0 : v ⟨0, by omega⟩ = 0) :
    v = 0 := by
  have hall : ∀ k : ℕ, (hk : k < D) → v ⟨k, hk⟩ = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero => exact hv0
      | succ m =>
        have hm : m < D := by omega
        have hstep := congrFun heig ⟨m, hm⟩
        rw [doubleWellTridiag_mulVec_apply hD E_B v ⟨m, hm⟩] at hstep
        simp only [Pi.smul_apply, smul_eq_mul] at hstep
        have hvm : v ⟨m, hm⟩ = 0 := ih m (by omega) hm
        have hprev : (if h : 0 < m then v ⟨m - 1, by omega⟩ else 0) = 0 := by
          split_ifs with h0
          · exact ih (m - 1) (by omega) (by omega)
          · rfl
        rw [hvm, mul_zero, mul_zero, hprev, add_zero, zero_add, dif_pos hk] at hstep
        exact hstep
  ext ⟨k, hk⟩
  exact hall k hk

/-- Every eigenspace of `doubleWellTridiag D E_B` is 1-dimensional: any two eigenvectors for `E`
with `v ≠ 0` are scalar multiples. -/
theorem doubleWellTridiag_eigenspace_simple {D : ℕ} (hD : 2 ≤ D) (E_B E : ℝ)
    (u v : Fin D → ℝ)
    (hu : doubleWellTridiag D E_B *ᵥ u = E • u)
    (hv : doubleWellTridiag D E_B *ᵥ v = E • v)
    (hv_ne : v ≠ 0) :
    ∃ c : ℝ, u = c • v := by
  have hv0 : v ⟨0, by omega⟩ ≠ 0 := fun h0 ↦ hv_ne (doubleWellTridiag_sturm_zero hD E_B E v hv h0)
  refine ⟨u ⟨0, by omega⟩ / v ⟨0, by omega⟩, ?_⟩
  let w : Fin D → ℝ := u - (u ⟨0, by omega⟩ / v ⟨0, by omega⟩) • v
  have hw_eig : doubleWellTridiag D E_B *ᵥ w = E • w := by
    dsimp only [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hu, hv, smul_sub, smul_comm]
  have hw0 : w ⟨0, by omega⟩ = 0 := by
    dsimp only [w]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ hv0, sub_self]
  have hw_zero := doubleWellTridiag_sturm_zero hD E_B E w hw_eig hw0
  exact sub_eq_zero.mp hw_zero

/-- **Definite Parity of Eigenvectors (Lemma B.1)**:
Every nonzero eigenvector `v` of `doubleWellTridiag D E_B` satisfies `P v = v` (even)
or `P v = -v` (odd). -/
theorem doubleWellTridiag_eigenvec_parity {D : ℕ} (hD : 2 ≤ D) (E_B E : ℝ) (v : Fin D → ℝ)
    (hv : doubleWellTridiag D E_B *ᵥ v = E • v) (hv_ne : v ≠ 0) :
    parityMat D *ᵥ v = v ∨ parityMat D *ᵥ v = -v := by
  have hPv_eig : doubleWellTridiag D E_B *ᵥ (parityMat D *ᵥ v) = E • (parityMat D *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← doubleWellTridiag_comm_parityMat, ← Matrix.mulVec_mulVec,
      hv, Matrix.mulVec_smul]
  rcases doubleWellTridiag_eigenspace_simple hD E_B E (parityMat D *ᵥ v) v hPv_eig hv hv_ne with ⟨c, hc⟩
  have hsq : v = (c * c) • v := by
    calc v = (1 : Matrix (Fin D) (Fin D) ℝ) *ᵥ v := (Matrix.one_mulVec v).symm
      _ = (parityMat D * parityMat D) *ᵥ v := by rw [parityMat_mul_self]
      _ = parityMat D *ᵥ (parityMat D *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = parityMat D *ᵥ (c • v) := by rw [hc]
      _ = c • (parityMat D *ᵥ v) := Matrix.mulVec_smul _ _ _
      _ = c • (c • v) := by rw [hc]
      _ = (c * c) • v := smul_smul c c v
  have hc2 : c * c = 1 := by
    obtain ⟨i, hi⟩ : ∃ i : Fin D, v i ≠ 0 := by
      by_contra hall; push Not at hall; exact hv_ne (funext hall)
    have h1 := congrFun hsq i
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    have h2 : (c * c - 1) * v i = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hi)
  have hc_pm : c = 1 ∨ c = -1 := by
    have : (c - 1) * (c + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h <;> [left; right] <;> linarith
  rcases hc_pm with rfl | rfl
  · left; simpa using hc
  · right; simpa using hc

/-- Quadratic form identity for `doubleWellTridiag D E_B`:
`⟨v, ℒ v⟩ = E_B * ∑_{1 ≤ i ≤ D-2} v_i² + 2 * ∑_{j=0}^{D-2} v_j v_{j+1}`. -/
lemma doubleWellTridiag_quadForm {D : ℕ} (hD : 2 ≤ D) (E_B : ℝ) (v : Fin D → ℝ) :
    dotProduct v (doubleWellTridiag D E_B *ᵥ v) =
      E_B * (∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)), v i ^ 2) +
      2 * ∑ j : Fin (D - 1), v ⟨j.val, by omega⟩ * v ⟨j.val + 1, by omega⟩ := by
  have h1 : dotProduct v (doubleWellTridiag D E_B *ᵥ v) =
      ∑ i : Fin D, ((if i.val = 0 ∨ i.val = D - 1 then 0 else E_B) * v i ^ 2 +
        (if h : 0 < i.val then v i * v ⟨i.val - 1, by omega⟩ else 0) +
        (if h : i.val + 1 < D then v i * v ⟨i.val + 1, h⟩ else 0)) := by
    unfold dotProduct
    apply Finset.sum_congr rfl; intro i _
    rw [doubleWellTridiag_mulVec_apply hD E_B v i]
    split_ifs <;> ring
  rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hdiag : ∑ i : Fin D, (if i.val = 0 ∨ i.val = D - 1 then 0 else E_B) * v i ^ 2 =
      E_B * ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)), v i ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl; intro i _
    split_ifs <;> ring
  have hup : ∑ i : Fin D, (if h : i.val + 1 < D then v i * v ⟨i.val + 1, h⟩ else 0) =
      ∑ j : Fin (D - 1), v ⟨j.val, by omega⟩ * v ⟨j.val + 1, by omega⟩ := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin D ↦ i.val + 1 < D)]
    have h0 : ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val + 1 < D)),
        (if h : i.val + 1 < D then v i * v ⟨i.val + 1, h⟩ else 0) = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      rw [dif_neg (Finset.mem_filter.mp hi).2]
    rw [h0, add_zero]
    symm
    refine Finset.sum_bij (fun (j : Fin (D - 1)) _ ↦ ⟨j.val, by omega⟩) ?_ ?_ ?_ ?_
    · intro j _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · intro a _ b _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
    · intro i hi
      have hlt : i.val + 1 < D := (Finset.mem_filter.mp hi).2
      exact ⟨⟨i.val, by omega⟩, Finset.mem_univ _, by ext; rfl⟩
    · intro j _; rw [dif_pos (by omega : j.val + 1 < D)]
  have hdn : ∑ i : Fin D, (if h : 0 < i.val then v i * v ⟨i.val - 1, by omega⟩ else 0) =
      ∑ j : Fin (D - 1), v ⟨j.val, by omega⟩ * v ⟨j.val + 1, by omega⟩ := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin D ↦ 0 < i.val)]
    have h0 : ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(0 < i.val)),
        (if h : 0 < i.val then v i * v ⟨i.val - 1, by omega⟩ else 0) = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      rw [dif_neg (Finset.mem_filter.mp hi).2]
    rw [h0, add_zero]
    symm
    refine Finset.sum_bij (fun (j : Fin (D - 1)) _ ↦ ⟨j.val + 1, by omega⟩) ?_ ?_ ?_ ?_
    · intro j _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · intro a _ b _ h; have h1 : a.val + 1 = b.val + 1 := by simpa using congrArg Fin.val h
      exact Fin.ext (by omega)
    · intro i hi
      have hpos : 0 < i.val := (Finset.mem_filter.mp hi).2
      exact ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, by ext; simp; omega⟩
    · intro j _
      rw [dif_pos (by omega : 0 < j.val + 1)]
      simp only [Nat.add_sub_cancel]; ring
  rw [hdiag, hup, hdn]; ring

/-- Path hopping bound: `|2 * ∑_{j=0}^{D-2} v_j v_{j+1}| ≤ 2 * ∑_{i=0}^{D-1} v_i²`. -/
lemma path_hopping_quad_le {D : ℕ} (hD : 2 ≤ D) (v : Fin D → ℝ) :
    |2 * ∑ j : Fin (D - 1), v ⟨j.val, by omega⟩ * v ⟨j.val + 1, by omega⟩| ≤
      2 * ∑ i : Fin D, v i ^ 2 := by
  have h1 : |∑ j : Fin (D - 1), v ⟨j.val, by omega⟩ * v ⟨j.val + 1, by omega⟩| ≤
      ∑ j : Fin (D - 1), ((v ⟨j.val, by omega⟩ ^ 2 + v ⟨j.val + 1, by omega⟩ ^ 2) / 2) := by
    calc |∑ j : Fin (D - 1), v ⟨j.val, by omega⟩ * v ⟨j.val + 1, by omega⟩|
        ≤ ∑ j : Fin (D - 1), |v ⟨j.val, by omega⟩ * v ⟨j.val + 1, by omega⟩| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin (D - 1), ((v ⟨j.val, by omega⟩ ^ 2 + v ⟨j.val + 1, by omega⟩ ^ 2) / 2) := by
          apply Finset.sum_le_sum; intro j _
          have ha : 0 ≤ (|v ⟨j.val, by omega⟩| - |v ⟨j.val + 1, by omega⟩|) ^ 2 := sq_nonneg _
          rw [abs_mul]
          nlinarith [sq_abs (v ⟨j.val, by omega⟩), sq_abs (v ⟨j.val + 1, by omega⟩)]
  have hL : ∑ j : Fin (D - 1), v ⟨j.val, by omega⟩ ^ 2 ≤ ∑ i : Fin D, v i ^ 2 := by
    let f : Fin (D - 1) → Fin D := fun j ↦ ⟨j.val, by omega⟩
    have hf : Function.Injective f := fun a b h ↦ Fin.ext (by simpa [f] using congrArg Fin.val h)
    rw [← Finset.sum_image (f := fun i : Fin D ↦ v i ^ 2) (g := f) (fun a _ b _ h ↦ hf h)]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
  have hR : ∑ j : Fin (D - 1), v ⟨j.val + 1, by omega⟩ ^ 2 ≤ ∑ i : Fin D, v i ^ 2 := by
    let f : Fin (D - 1) → Fin D := fun j ↦ ⟨j.val + 1, by omega⟩
    have hf : Function.Injective f := fun a b h ↦ by
      have h1 : a.val + 1 = b.val + 1 := by simpa [f] using congrArg Fin.val h
      exact Fin.ext (by omega)
    rw [← Finset.sum_image (f := fun i : Fin D ↦ v i ^ 2) (g := f) (fun a _ b _ h ↦ hf h)]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
  have hsum : ∑ j : Fin (D - 1), ((v ⟨j.val, by omega⟩ ^ 2 + v ⟨j.val + 1, by omega⟩ ^ 2) / 2) ≤
      ∑ i : Fin D, v i ^ 2 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **Rayleigh Quotient Bounds for `doubleWellTridiag D E_B` (`D ≥ 4, E_B > 2`)**:
1. Upper bound on all vectors: `⟨v, ℒ v⟩ ≤ (E_B + 2) ⟨v, v⟩`.
2. Interior lower bound (`v 0 = 0 ∧ v (D - 1) = 0`): `(E_B - 2) ⟨v, v⟩ ≤ ⟨v, ℒ v⟩`.
3. Global lower bound on all vectors: `-(E_B - 2)⁻¹ ⟨v, v⟩ ≤ ⟨v, ℒ v⟩`. -/
theorem doubleWellTridiag_rayleigh_bounds {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B)
    (v : Fin D → ℝ) :
    dotProduct v (doubleWellTridiag D E_B *ᵥ v) ≤ (E_B + 2) * dotProduct v v ∧
    (v ⟨0, by omega⟩ = 0 → v ⟨D - 1, by omega⟩ = 0 →
      (E_B - 2) * dotProduct v v ≤ dotProduct v (doubleWellTridiag D E_B *ᵥ v)) ∧
    -(1 / (E_B - 2)) * dotProduct v v ≤ dotProduct v (doubleWellTridiag D E_B *ᵥ v) := by
  have hD2 : 2 ≤ D := by omega
  have hqf := doubleWellTridiag_quadForm hD2 E_B v
  have hhop := path_hopping_quad_le hD2 v
  have hdot : dotProduct v v = ∑ i : Fin D, v i ^ 2 := by
    unfold dotProduct; apply Finset.sum_congr rfl; intro i _; ring
  have hint_le : ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)), v i ^ 2 ≤
      ∑ i : Fin D, v i ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · -- Upper bound `≤ (E_B + 2) ‖v‖²`
    rw [hqf, hdot]
    have h1 := (abs_le.mp hhop).2
    nlinarith
  · -- Interior lower bound `≥ (E_B - 2) ‖v‖²`
    intro hv0 hvD
    rw [hqf, hdot]
    have hint_eq : ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)), v i ^ 2 =
        ∑ i : Fin D, v i ^ 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1))]
      have h0 : ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬¬(i.val = 0 ∨ i.val = D - 1)), v i ^ 2 = 0 := by
        apply Finset.sum_eq_zero; intro i hi
        have hbd : i.val = 0 ∨ i.val = D - 1 := by
          have := (Finset.mem_filter.mp hi).2; tauto
        rcases hbd with h0 | h1
        · have : i = ⟨0, by omega⟩ := Fin.ext h0; rw [this, hv0]; norm_num
        · have : i = ⟨D - 1, by omega⟩ := Fin.ext h1; rw [this, hvD]; norm_num
      linarith
    rw [hint_eq]
    have h1 := (abs_le.mp hhop).1
    linarith
  · -- Global lower bound `≥ -(E_B - 2)⁻¹ ‖v‖²`
    -- Split `v = v_bd + v_int` where `v_int` zeros out `0` and `D - 1`.
    let v_int : Fin D → ℝ := fun i ↦ if i.val = 0 ∨ i.val = D - 1 then 0 else v i
    have hhop_int := path_hopping_quad_le hD2 v_int
    have hdot_int : ∑ i : Fin D, v_int i ^ 2 =
        ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)), v i ^ 2 := by
      rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro i _; dsimp only [v_int]; split_ifs <;> ring
    have hsplit_hop : ∑ j : Fin (D - 1), v ⟨j.val, by omega⟩ * v ⟨j.val + 1, by omega⟩ =
        (∑ j : Fin (D - 1), v_int ⟨j.val, by omega⟩ * v_int ⟨j.val + 1, by omega⟩) +
        v ⟨0, by omega⟩ * v ⟨1, by omega⟩ + v ⟨D - 2, by omega⟩ * v ⟨D - 1, by omega⟩ := by
      have hsub : ∑ j : Fin (D - 1), (v ⟨j.val, by omega⟩ * v ⟨j.val + 1, by omega⟩ -
          v_int ⟨j.val, by omega⟩ * v_int ⟨j.val + 1, by omega⟩) =
          v ⟨0, by omega⟩ * v ⟨1, by omega⟩ + v ⟨D - 2, by omega⟩ * v ⟨D - 1, by omega⟩ := by
        let j0 : Fin (D - 1) := ⟨0, by omega⟩
        let j1 : Fin (D - 1) := ⟨D - 2, by omega⟩
        have hjne : j0 ≠ j1 := by intro h; have := congrArg Fin.val h; simp [j0, j1] at this; omega
        rw [← Finset.sum_subset (s₁ := {j0, j1}) (Finset.subset_univ _)]
        · rw [Finset.sum_pair hjne]
          simp only [j0, j1, v_int, ↓reduceIte, zero_mul, mul_zero, sub_zero,
            show D - 2 + 1 = D - 1 by omega, or_true, true_or]
        · intro j _ hnot
          have hj0 : j.val ≠ 0 := fun h ↦ hnot (by simp [j0, Fin.ext_iff, h])
          have hj1 : j.val ≠ D - 2 := fun h ↦ hnot (by simp [j1, Fin.ext_iff, h])
          have ha : ¬(j.val = 0 ∨ j.val = D - 1) := by omega
          have hb : ¬(j.val + 1 = 0 ∨ j.val + 1 = D - 1) := by omega
          dsimp only [v_int]
          rw [if_neg ha, if_neg hb, sub_self]
      rw [Finset.sum_sub_distrib] at hsub
      linarith
    have hEB2 : 0 < E_B - 2 := by linarith
    have h1_mem : (⟨1, by omega⟩ : Fin D) ∈
        Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hD2_mem : (⟨D - 2, by omega⟩ : Fin D) ∈
        Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have h1_ne_D2 : (⟨1, by omega⟩ : Fin D) ≠ ⟨D - 2, by omega⟩ := by
      intro h; have := congrArg Fin.val h; dsimp at this; omega
    have hint_ge_pair : v ⟨1, by omega⟩ ^ 2 + v ⟨D - 2, by omega⟩ ^ 2 ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)), v i ^ 2 := by
      have hsub : ({⟨1, by omega⟩, ⟨D - 2, by omega⟩} : Finset (Fin D)) ⊆
          Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)) := by
        intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl <;> [exact h1_mem; exact hD2_mem]
      calc v ⟨1, by omega⟩ ^ 2 + v ⟨D - 2, by omega⟩ ^ 2
          = ∑ i ∈ ({⟨1, by omega⟩, ⟨D - 2, by omega⟩} : Finset (Fin D)), v i ^ 2 := by
            rw [Finset.sum_pair h1_ne_D2]
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)), v i ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ sq_nonneg _
    have hbd_le : v ⟨0, by omega⟩ ^ 2 + v ⟨D - 1, by omega⟩ ^ 2 ≤ ∑ i : Fin D, v i ^ 2 := by
      have h0_ne_D1 : (⟨0, by omega⟩ : Fin D) ≠ ⟨D - 1, by omega⟩ := by
        intro h; have := congrArg Fin.val h; dsimp at this; omega
      calc v ⟨0, by omega⟩ ^ 2 + v ⟨D - 1, by omega⟩ ^ 2
          = ∑ i ∈ ({⟨0, by omega⟩, ⟨D - 1, by omega⟩} : Finset (Fin D)), v i ^ 2 := by
            rw [Finset.sum_pair h0_ne_D1]
        _ ≤ ∑ i : Fin D, v i ^ 2 := Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
    have hsq1 : 0 ≤ (E_B - 2) * v ⟨1, by omega⟩ ^ 2 + 2 * v ⟨0, by omega⟩ * v ⟨1, by omega⟩ +
        v ⟨0, by omega⟩ ^ 2 / (E_B - 2) := by
      have h : (E_B - 2) * ((E_B - 2) * v ⟨1, by omega⟩ ^ 2 + 2 * v ⟨0, by omega⟩ * v ⟨1, by omega⟩ +
          v ⟨0, by omega⟩ ^ 2 / (E_B - 2)) =
          ((E_B - 2) * v ⟨1, by omega⟩ + v ⟨0, by omega⟩) ^ 2 := by
        field_simp [hEB2.ne']; ring
      have hnn : 0 ≤ ((E_B - 2) * v ⟨1, by omega⟩ + v ⟨0, by omega⟩) ^ 2 := sq_nonneg _
      nlinarith
    have hsq2 : 0 ≤ (E_B - 2) * v ⟨D - 2, by omega⟩ ^ 2 + 2 * v ⟨D - 2, by omega⟩ * v ⟨D - 1, by omega⟩ +
        v ⟨D - 1, by omega⟩ ^ 2 / (E_B - 2) := by
      have h : (E_B - 2) * ((E_B - 2) * v ⟨D - 2, by omega⟩ ^ 2 + 2 * v ⟨D - 2, by omega⟩ * v ⟨D - 1, by omega⟩ +
          v ⟨D - 1, by omega⟩ ^ 2 / (E_B - 2)) =
          ((E_B - 2) * v ⟨D - 2, by omega⟩ + v ⟨D - 1, by omega⟩) ^ 2 := by
        field_simp [hEB2.ne']; ring
      have hnn : 0 ≤ ((E_B - 2) * v ⟨D - 2, by omega⟩ + v ⟨D - 1, by omega⟩) ^ 2 := sq_nonneg _
      nlinarith
    rw [hqf, hdot, hsplit_hop]
    have hhop_low := (abs_le.mp hhop_int).1
    rw [hdot_int] at hhop_low
    have hdiv : (v ⟨0, by omega⟩ ^ 2 + v ⟨D - 1, by omega⟩ ^ 2) / (E_B - 2) ≤
        (1 / (E_B - 2)) * ∑ i : Fin D, v i ^ 2 := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hbd_le hEB2.le
    have hdiv_add : v ⟨0, by omega⟩ ^ 2 / (E_B - 2) + v ⟨D - 1, by omega⟩ ^ 2 / (E_B - 2) =
        (v ⟨0, by omega⟩ ^ 2 + v ⟨D - 1, by omega⟩ ^ 2) / (E_B - 2) := by ring
    nlinarith

/-- Decay factor `q(E_B) = (E_B - √(E_B² - 4)) / 2` for `E_B > 2`. -/
noncomputable def doubleWellDecayQ (E_B : ℝ) : ℝ :=
  (E_B - Real.sqrt (E_B ^ 2 - 4)) / 2

lemma doubleWellDecayQ_props {E_B : ℝ} (hEB : 2 < E_B) :
    0 < doubleWellDecayQ E_B ∧
    doubleWellDecayQ E_B < 1 ∧
    doubleWellDecayQ E_B ^ 2 - E_B * doubleWellDecayQ E_B + 1 = 0 ∧
    doubleWellDecayQ E_B ≤ 1 / (E_B - 1) := by
  have hdisc : 0 < E_B ^ 2 - 4 := by nlinarith
  have hsq : Real.sqrt (E_B ^ 2 - 4) ^ 2 = E_B ^ 2 - 4 := Real.sq_sqrt hdisc.le
  have hsqrt_lt : Real.sqrt (E_B ^ 2 - 4) < E_B := by
    calc Real.sqrt (E_B ^ 2 - 4) < Real.sqrt (E_B ^ 2) := Real.sqrt_lt_sqrt hdisc.le (by linarith)
      _ = E_B := Real.sqrt_sq (by linarith)
  have hsqrt_gt : E_B - 2 < Real.sqrt (E_B ^ 2 - 4) := by
    calc E_B - 2 = Real.sqrt ((E_B - 2) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ < Real.sqrt (E_B ^ 2 - 4) := Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  have hq_pos : 0 < doubleWellDecayQ E_B := by unfold doubleWellDecayQ; linarith
  have hq_lt1 : doubleWellDecayQ E_B < 1 := by unfold doubleWellDecayQ; linarith
  have hquad : doubleWellDecayQ E_B ^ 2 - E_B * doubleWellDecayQ E_B + 1 = 0 := by
    unfold doubleWellDecayQ; nlinarith
  have hq_le : doubleWellDecayQ E_B ≤ 1 / (E_B - 1) := by
    rw [le_div_iff₀ (by linarith : 0 < E_B - 1)]
    have hq2 : doubleWellDecayQ E_B ^ 2 ≤ doubleWellDecayQ E_B := by nlinarith
    nlinarith
  exact ⟨hq_pos, hq_lt1, hquad, hq_le⟩

/-- **Lemma B.1 — Discrete Maximum Principle: Exponential Eigenvector Decay Eq. (B.2) &
Boundary Localization Eq. (B.3)**:
For ANY `D ≥ 4`, `E_B > 2`, and ANY normalized eigenvector `v : Fin D → ℝ` (`∑ j, (v j)² = 1`)
of `doubleWellTridiag D E_B` with eigenvalue `E ≤ 0`:
1. `∀ j : Fin D, |v j| ≤ |v 0| * (q ^ j.val + q ^ (D - 1 - j.val))` (Eq. B.2),
2. `1 - 2 * (v 0) ^ 2 ≤ 4 * (q ^ 2 / (1 - q ^ 2)) * (v 0) ^ 2` (Eq. B.3),
where `q = doubleWellDecayQ E_B ∈ (0, 1)`. -/
theorem lemma_B_1_eigenvec_decay_eq_B2_B3 {D : ℕ} (hD : 4 ≤ D) {E_B E : ℝ}
    (hEB : 2 < E_B) (hE : E ≤ 0) (v : Fin D → ℝ)
    (heig : doubleWellTridiag D E_B *ᵥ v = E • v)
    (hnorm : ∑ j : Fin D, v j ^ 2 = 1) :
    let q := doubleWellDecayQ E_B
    (∀ j : Fin D, |v j| ≤ |v ⟨0, by omega⟩| * (q ^ j.val + q ^ (D - 1 - j.val))) ∧
    1 - 2 * v ⟨0, by omega⟩ ^ 2 ≤ 4 * (q ^ 2 / (1 - q ^ 2)) * v ⟨0, by omega⟩ ^ 2 := by
  intro q
  rcases doubleWellDecayQ_props hEB with ⟨hq_pos, hq_lt1, hq_quad, _⟩
  have hD2 : 2 ≤ D := by omega
  have hv_ne : v ≠ 0 := by
    intro h0; rw [h0] at hnorm; simp at hnorm
  have hpar := doubleWellTridiag_eigenvec_parity hD2 E_B E v heig hv_ne
  have hbd_eq : |v ⟨D - 1, by omega⟩| = |v ⟨0, by omega⟩| := by
    rcases hpar with h | h
    · have h1 := congrFun h ⟨0, by omega⟩
      rw [parityMat_mulVec] at h1
      have hrev : revFin (⟨0, by omega⟩ : Fin D) = ⟨D - 1, by omega⟩ := by
        ext; simp [revFin]
      rw [hrev] at h1; rw [h1]
    · have h1 := congrFun h ⟨0, by omega⟩
      rw [parityMat_mulVec, Pi.neg_apply] at h1
      have hrev : revFin (⟨0, by omega⟩ : Fin D) = ⟨D - 1, by omega⟩ := by
        ext; simp [revFin]
      rw [hrev] at h1; rw [h1, abs_neg]
  let f : Fin D → ℝ := fun j ↦ |v ⟨0, by omega⟩| * (q ^ j.val + q ^ (D - 1 - j.val))
  let w : Fin D → ℝ := fun j ↦ |v j| - f j
  have hw0 : w ⟨0, by omega⟩ ≤ 0 := by
    dsimp only [w, f]
    have hq_nn : 0 ≤ q ^ (D - 1) := pow_nonneg hq_pos.le _
    simp only [pow_zero, Nat.sub_zero]
    nlinarith [abs_nonneg (v ⟨0, by omega⟩)]
  have hwD : w ⟨D - 1, by omega⟩ ≤ 0 := by
    dsimp only [w, f]
    rw [hbd_eq, Nat.sub_self, pow_zero]
    have hq_nn : 0 ≤ q ^ (D - 1) := pow_nonneg hq_pos.le _
    nlinarith [abs_nonneg (v ⟨0, by omega⟩)]
  have hw_int : ∀ (j : Fin D) (_ : 0 < j.val) (hj1 : j.val + 1 < D),
      E_B * w j ≤ w ⟨j.val - 1, by omega⟩ + w ⟨j.val + 1, hj1⟩ := by
    intro j hj0 hj1
    have hrow := congrFun heig j
    rw [doubleWellTridiag_mulVec_apply hD2 E_B v j] at hrow
    simp only [Pi.smul_apply, smul_eq_mul, dif_pos hj0, dif_pos hj1] at hrow
    have hnotbd : ¬(j.val = 0 ∨ j.val = D - 1) := by omega
    rw [if_neg hnotbd] at hrow
    have hv_ineq : E_B * |v j| ≤ |v ⟨j.val - 1, by omega⟩| + |v ⟨j.val + 1, by omega⟩| := by
      have h1 : (E_B - E) * v j = -(v ⟨j.val - 1, by omega⟩ + v ⟨j.val + 1, by omega⟩) := by linarith
      have h2 : (E_B - E) * |v j| ≤ |v ⟨j.val - 1, by omega⟩| + |v ⟨j.val + 1, by omega⟩| := by
        calc (E_B - E) * |v j| = |(E_B - E) * v j| := by
              rw [abs_mul, abs_of_pos (by linarith : 0 < E_B - E)]
          _ = |-(v ⟨j.val - 1, by omega⟩ + v ⟨j.val + 1, by omega⟩)| := by rw [h1]
          _ = |v ⟨j.val - 1, by omega⟩ + v ⟨j.val + 1, by omega⟩| := abs_neg _
          _ ≤ |v ⟨j.val - 1, by omega⟩| + |v ⟨j.val + 1, by omega⟩| := abs_add_le _ _
      nlinarith [abs_nonneg (v j)]
    have hf_eq : E_B * f j = f ⟨j.val - 1, by omega⟩ + f ⟨j.val + 1, by omega⟩ := by
      dsimp only [f]
      have hq_sum : 1 + q ^ 2 = E_B * q := by linarith [hq_quad]
      have ha : q ^ (j.val - 1) + q ^ (j.val + 1) = E_B * q ^ j.val := by
        have h1 : j.val = (j.val - 1) + 1 := by omega
        have h2 : j.val + 1 = (j.val - 1) + 2 := by omega
        calc q ^ (j.val - 1) + q ^ (j.val + 1)
            = q ^ (j.val - 1) + q ^ ((j.val - 1) + 2) := by rw [h2]
          _ = q ^ (j.val - 1) * (1 + q ^ 2) := by rw [pow_add]; ring
          _ = q ^ (j.val - 1) * (E_B * q) := by rw [hq_sum]
          _ = E_B * q ^ ((j.val - 1) + 1) := by rw [pow_succ]; ring
          _ = E_B * q ^ j.val := by rw [← h1]
      have hb : q ^ (D - 1 - (j.val - 1)) + q ^ (D - 1 - (j.val + 1)) = E_B * q ^ (D - 1 - j.val) := by
        calc q ^ (D - 1 - (j.val - 1)) + q ^ (D - 1 - (j.val + 1))
            = q ^ (D - 1 - (j.val + 1)) * (1 + q ^ 2) := by
                rw [show D - 1 - (j.val - 1) = (D - 1 - (j.val + 1)) + 2 by omega, pow_add]; ring
          _ = q ^ (D - 1 - (j.val + 1)) * (E_B * q) := by rw [hq_sum]
          _ = E_B * q ^ (D - 1 - j.val) := by
                rw [show D - 1 - j.val = (D - 1 - (j.val + 1)) + 1 by omega, pow_succ]; ring
      calc E_B * (|v ⟨0, by omega⟩| * (q ^ j.val + q ^ (D - 1 - j.val)))
          = |v ⟨0, by omega⟩| * (E_B * q ^ j.val + E_B * q ^ (D - 1 - j.val)) := by ring
        _ = |v ⟨0, by omega⟩| * ((q ^ (j.val - 1) + q ^ (j.val + 1)) +
              (q ^ (D - 1 - (j.val - 1)) + q ^ (D - 1 - (j.val + 1)))) := by rw [← ha, ← hb]
        _ = |v ⟨0, by omega⟩| * (q ^ (j.val - 1) + q ^ (D - 1 - (j.val - 1))) +
            |v ⟨0, by omega⟩| * (q ^ (j.val + 1) + q ^ (D - 1 - (j.val + 1))) := by ring
    dsimp only [w]; linarith
  have hw_le : ∀ j : Fin D, w j ≤ 0 := by
    have hne : (Finset.univ : Finset (Fin D)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    obtain ⟨j₀, _, hj₀_max⟩ := Finset.exists_max_image Finset.univ w hne
    have hj₀_le : w j₀ ≤ 0 := by
      by_contra hpos; push Not at hpos
      have h0 : 0 < j₀.val := by
        by_contra hle; have heq : j₀ = ⟨0, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [heq] at hpos; linarith
      have h1 : j₀.val + 1 < D := by
        by_contra hge; have heq : j₀ = ⟨D - 1, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [heq] at hpos; linarith
      have hint := hw_int j₀ h0 h1
      have hm1 := hj₀_max ⟨j₀.val - 1, by omega⟩ (Finset.mem_univ _)
      have hm2 := hj₀_max ⟨j₀.val + 1, by omega⟩ (Finset.mem_univ _)
      nlinarith
    exact fun j ↦ le_trans (hj₀_max j (Finset.mem_univ j)) hj₀_le
  have hB2 : ∀ j : Fin D, |v j| ≤ |v ⟨0, by omega⟩| * (q ^ j.val + q ^ (D - 1 - j.val)) :=
    fun j ↦ sub_nonpos.mp (hw_le j)
  refine ⟨hB2, ?_⟩
  -- Prove Eq. (B.3) from Eq. (B.2) by summing squares over interior sites
  have h0_ne_D1 : (⟨0, by omega⟩ : Fin D) ≠ ⟨D - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; dsimp at this; omega
  have hsplit : ∑ j : Fin D, v j ^ 2 =
      (v ⟨0, by omega⟩ ^ 2 + v ⟨D - 1, by omega⟩ ^ 2) +
      ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬(j.val = 0 ∨ j.val = D - 1)), v j ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin D ↦ j.val = 0 ∨ j.val = D - 1)]
    congr 1
    have hbd_set : Finset.univ.filter (fun j : Fin D ↦ j.val = 0 ∨ j.val = D - 1) =
        {⟨0, by omega⟩, ⟨D - 1, by omega⟩} := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff]
    rw [hbd_set, Finset.sum_pair h0_ne_D1]
  have hvD_sq : v ⟨D - 1, by omega⟩ ^ 2 = v ⟨0, by omega⟩ ^ 2 := by
    rw [← sq_abs, hbd_eq, sq_abs]
  have hint_sq : ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬(j.val = 0 ∨ j.val = D - 1)), v j ^ 2 ≤
      4 * (q ^ 2 / (1 - q ^ 2)) * v ⟨0, by omega⟩ ^ 2 := by
    have hterm : ∀ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬(j.val = 0 ∨ j.val = D - 1)),
        v j ^ 2 ≤ 2 * v ⟨0, by omega⟩ ^ 2 * ((q ^ 2) ^ j.val + (q ^ 2) ^ (D - 1 - j.val)) := by
      intro j _
      have h1 := hB2 j
      have h2 : v j ^ 2 ≤ (|v ⟨0, by omega⟩| * (q ^ j.val + q ^ (D - 1 - j.val))) ^ 2 := by
        rw [← sq_abs (v j)]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      have h3 : (q ^ j.val + q ^ (D - 1 - j.val)) ^ 2 ≤ 2 * ((q ^ 2) ^ j.val + (q ^ 2) ^ (D - 1 - j.val)) := by
        have hsq : 0 ≤ (q ^ j.val - q ^ (D - 1 - j.val)) ^ 2 := sq_nonneg _
        have ha : (q ^ j.val) ^ 2 = (q ^ 2) ^ j.val := by rw [← pow_mul, mul_comm, pow_mul]
        have hb : (q ^ (D - 1 - j.val)) ^ 2 = (q ^ 2) ^ (D - 1 - j.val) := by
          rw [← pow_mul, mul_comm, pow_mul]
        nlinarith
      rw [mul_pow, sq_abs] at h2
      exact le_trans h2 (by nlinarith [sq_nonneg (v ⟨0, by omega⟩)])
    have hq2_lt1 : q ^ 2 < 1 := by nlinarith
    have hgeom : ∀ m : ℕ, ∑ k ∈ Finset.Ico 1 m, (q ^ 2) ^ k ≤ q ^ 2 / (1 - q ^ 2) := by
      intro m
      by_cases hm : m ≤ 1
      · have hemp : Finset.Ico 1 m = ∅ := Finset.Ico_eq_empty (by omega)
        rw [hemp, Finset.sum_empty]; positivity
      · push Not at hm
        have hshift : ∑ k ∈ Finset.Ico 1 m, (q ^ 2) ^ k =
            q ^ 2 * ∑ k ∈ Finset.range (m - 1), (q ^ 2) ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_bij (fun k _ ↦ k - 1) ?_ ?_ ?_ ?_
          · intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_range]; omega
          · intro a ha b hb h; rw [Finset.mem_Ico] at ha hb; omega
          · intro k hk; rw [Finset.mem_range] at hk
            exact ⟨k + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
          · intro k hk; rw [Finset.mem_Ico] at hk
            rw [← pow_succ', show (k - 1) + 1 = k by omega]
        rw [hshift, geom_sum_eq (ne_of_lt hq2_lt1)]
        have hnum : (1 - (q ^ 2) ^ (m - 1)) / (1 - q ^ 2) ≤ 1 / (1 - q ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by linarith)
          linarith [pow_nonneg (sq_nonneg q) (m - 1)]
        have hrew : ((q ^ 2) ^ (m - 1) - 1) / (q ^ 2 - 1) = (1 - (q ^ 2) ^ (m - 1)) / (1 - q ^ 2) := by
          have h1 : q ^ 2 - 1 = -(1 - q ^ 2) := by ring
          have h2 : (q ^ 2) ^ (m - 1) - 1 = -(1 - (q ^ 2) ^ (m - 1)) := by ring
          rw [h1, h2, neg_div_neg_eq]
        rw [hrew]
        calc q ^ 2 * ((1 - (q ^ 2) ^ (m - 1)) / (1 - q ^ 2))
            ≤ q ^ 2 * (1 / (1 - q ^ 2)) := mul_le_mul_of_nonneg_left hnum (sq_nonneg q)
          _ = q ^ 2 / (1 - q ^ 2) := by ring
    have hsum1 : ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬(j.val = 0 ∨ j.val = D - 1)), (q ^ 2) ^ j.val ≤
        q ^ 2 / (1 - q ^ 2) := by
      have heq : ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬(j.val = 0 ∨ j.val = D - 1)), (q ^ 2) ^ j.val =
          ∑ k ∈ Finset.Ico 1 (D - 1), (q ^ 2) ^ k := by
        refine Finset.sum_bij (fun j _ ↦ j.val) ?_ ?_ ?_ ?_
        · intro j hj; rw [Finset.mem_filter] at hj; rw [Finset.mem_Ico]; omega
        · intro a _ b _ h; exact Fin.ext h
        · intro k hk; rw [Finset.mem_Ico] at hk
          exact ⟨⟨k, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, rfl⟩
        · intro _ _; rfl
      rw [heq]; exact hgeom (D - 1)
    have hsum2 : ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬(j.val = 0 ∨ j.val = D - 1)),
        (q ^ 2) ^ (D - 1 - j.val) ≤ q ^ 2 / (1 - q ^ 2) := by
      have heq : ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬(j.val = 0 ∨ j.val = D - 1)),
          (q ^ 2) ^ (D - 1 - j.val) = ∑ k ∈ Finset.Ico 1 (D - 1), (q ^ 2) ^ k := by
        refine Finset.sum_bij (fun j _ ↦ D - 1 - j.val) ?_ ?_ ?_ ?_
        · intro j hj; rw [Finset.mem_filter] at hj; rw [Finset.mem_Ico]; omega
        · intro a ha b hb h; rw [Finset.mem_filter] at ha hb; ext; omega
        · intro k hk; rw [Finset.mem_Ico] at hk
          exact ⟨⟨D - 1 - k, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, by dsimp; omega⟩
        · intro _ _; rfl
      rw [heq]; exact hgeom (D - 1)
    calc ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬(j.val = 0 ∨ j.val = D - 1)), v j ^ 2
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬(j.val = 0 ∨ j.val = D - 1)),
            2 * v ⟨0, by omega⟩ ^ 2 * ((q ^ 2) ^ j.val + (q ^ 2) ^ (D - 1 - j.val)) :=
          Finset.sum_le_sum hterm
      _ = 2 * v ⟨0, by omega⟩ ^ 2 *
          ((∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬(j.val = 0 ∨ j.val = D - 1)), (q ^ 2) ^ j.val) +
           (∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬(j.val = 0 ∨ j.val = D - 1)), (q ^ 2) ^ (D - 1 - j.val))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * v ⟨0, by omega⟩ ^ 2 * (q ^ 2 / (1 - q ^ 2) + q ^ 2 / (1 - q ^ 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add hsum1 hsum2) (by positivity)
      _ = 4 * (q ^ 2 / (1 - q ^ 2)) * v ⟨0, by omega⟩ ^ 2 := by ring
  linarith [hnorm, hsplit, hvD_sq, hint_sq]

/-- **Proposition 9.1(3) — Exact `D`-Dimensional Limit (Eq. 9.3)**:
For any `D ≥ 4` and any family of barrier-height observables obeying the Lemma B.1 asymptotics
`ΔQ(E_B) → D - 1`, `K(E_B) → 1`, and `σ₀(E_B) → 0` as `E_B → ∞` (in particular with
`q(E_B) = doubleWellDecayQ E_B → 0`), the ratio converges to `D - 1`:
`Tendsto (fun E_B ↦ ΔQ E_B / (K E_B + σ₀ E_B * Real.sqrt (K E_B))) atTop (nhds ((D : ℝ) - 1))`. -/
theorem prop_9_1_part3_exact_D_limit_eq_9_3 (D : ℕ)
    (ΔQ K σ₀ : ℝ → ℝ)
    (hΔQ : Tendsto ΔQ atTop (nhds ((D : ℝ) - 1)))
    (hK : Tendsto K atTop (nhds 1))
    (hσ₀ : Tendsto σ₀ atTop (nhds 0)) :
    Tendsto (fun E_B : ℝ ↦ ΔQ E_B / (K E_B + σ₀ E_B * Real.sqrt (K E_B)))
      atTop (nhds ((D : ℝ) - 1)) := by
  have hsqrt : Tendsto (fun E_B : ℝ ↦ Real.sqrt (K E_B)) atTop (nhds (Real.sqrt 1)) :=
    (Real.continuous_sqrt.tendsto 1).comp hK
  rw [Real.sqrt_one] at hsqrt
  have hden : Tendsto (fun E_B : ℝ ↦ K E_B + σ₀ E_B * Real.sqrt (K E_B)) atTop (nhds (1 + 0 * 1)) :=
    hK.add (hσ₀.mul hsqrt)
  rw [zero_mul, add_zero] at hden
  have hdiv : Tendsto (fun E_B : ℝ ↦ ΔQ E_B / (K E_B + σ₀ E_B * Real.sqrt (K E_B)))
      atTop (nhds (((D : ℝ) - 1) / 1)) := hΔQ.div hden (by norm_num)
  simpa using hdiv

/-- Convergence of the Appendix B decay factor `doubleWellDecayQ E_B → 0` as `E_B → ∞`. -/
theorem tendsto_doubleWellDecayQ_zero :
    Tendsto doubleWellDecayQ atTop (nhds 0) := by
  have h1 : Tendsto (fun E_B : ℝ ↦ 1 / (E_B - 1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.atTop_add tendsto_const_nhds)
  refine squeeze_zero' ?_ ?_ h1
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with E_B hEB
    exact (doubleWellDecayQ_props hEB).1.le
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with E_B hEB
    exact (doubleWellDecayQ_props hEB).2.2.2

end LemmaB1DoubleWellTridiagonal

end KrylovChaos
