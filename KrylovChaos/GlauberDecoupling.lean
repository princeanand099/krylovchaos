/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.WightmanIsometry
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Section 6: Quantum Glauber Bound and Entropic Background Decoupling

Formalizes:
- **Lemma 6.1**: Single-site Wightman commutator bound (Eq. 6.1).
- **Proposition 6.2**: High-temperature quantum Glauber bound (Eq. 6.2).
- **Proposition 6.4(1)**: Exact three-term matrix decomposition `𝒮_β(A) = I(A) + II(A) + III(A)`
  (Eqs. 6.4–6.7).
- **Proposition 6.4(2)**: Variational Gibbs–Donsker–Varadhan optimization, geometric shell
  summation, and Cauchy–Schwarz decoupling bound (Eqs. 6.8–6.10).
-/

open scoped Matrix

namespace KrylovChaos

section GlauberBounds

/-- **Lemma 6.1** (Single-Site Wightman Commutator Bound, Eq. 6.1):
Given `‖[V_x, A]‖ ≤ ‖V_x B‖ + ‖B V_x‖`, `‖V_x B‖ ≤ M_β ‖B‖`, `‖B V_x‖ ≤ M_β ‖B‖`,
and best-approximation `‖B‖ ≤ ‖S_x(A)‖`, we obtain
`‖[V_x, A]‖ ≤ 2 M_β ‖B‖ ≤ 2 M_β ‖S_x(A)‖`. -/
theorem lemma_6_1_single_site_commutator
    {normComm normVB normBV normB normSx Mβ : ℝ}
    (hMβ : 0 ≤ Mβ)
    (htri : normComm ≤ normVB + normBV)
    (hleft : normVB ≤ Mβ * normB)
    (hright : normBV ≤ Mβ * normB)
    (hbest : normB ≤ normSx) :
    normComm ≤ 2 * Mβ * normB ∧ 2 * Mβ * normB ≤ 2 * Mβ * normSx := by
  exact ⟨by linarith, by nlinarith⟩

/-- **Proposition 6.2** (High-Temperature Quantum Glauber Bound, Eq. 6.2):
For `β ∈ [0, 4κ)`, summing Lemma 6.1 squared over `N` sites and 3 Pauli probes with
prefactor `1/8` and `M_β ≤ (1 - β/(4κ))⁻¹` yields
`C_W(A) ≤ (3/2) (1 - β/(4κ))⁻² (A | Q̃^{(β)} | A)_β^W`. -/
theorem prop_6_2_high_temp_glauber {N : ℕ} {β κ : ℝ}
    (commSq : Fin N → Fin 3 → ℝ) (projSq : Fin N → ℝ)
    (hβ0 : 0 ≤ β) (hκ : 0 < κ) (hβlt : β < 4 * κ)
    (hproj_nn : ∀ x, 0 ≤ projSq x)
    (hbound : ∀ x α, commSq x α ≤ (2 * (1 - β / (4 * κ))⁻¹) ^ 2 * projSq x) :
    (1 / 8 : ℝ) * (∑ x : Fin N, ∑ α : Fin 3, commSq x α) ≤
    (3 / 2 : ℝ) * (1 - β / (4 * κ))⁻¹ ^ 2 * (∑ x : Fin N, projSq x) := by
  have hinner : ∀ x : Fin N,
      ∑ α : Fin 3, commSq x α ≤ 3 * (2 * (1 - β / (4 * κ))⁻¹) ^ 2 * projSq x := by
    intro x
    calc ∑ α : Fin 3, commSq x α
        ≤ ∑ _ : Fin 3, (2 * (1 - β / (4 * κ))⁻¹) ^ 2 * projSq x :=
          Finset.sum_le_sum fun α _ ↦ hbound x α
      _ = 3 * (2 * (1 - β / (4 * κ))⁻¹) ^ 2 * projSq x := by simp [mul_assoc]
  calc (1 / 8 : ℝ) * (∑ x : Fin N, ∑ α : Fin 3, commSq x α)
      ≤ (1 / 8 : ℝ) * (∑ x : Fin N, 3 * (2 * (1 - β / (4 * κ))⁻¹) ^ 2 * projSq x) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun x _ ↦ hinner x
    _ = (3 / 2 : ℝ) * (1 - β / (4 * κ))⁻¹ ^ 2 * (∑ x : Fin N, projSq x) := by
        rw [← Finset.mul_sum]; ring

end GlauberBounds

section ThreeTermDecomposition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Proposition 6.4(1)** (Exact Single-Probe Algebraic Splitting):
For invertible Hermitian `ρ^{1/4}` with `(ρ^{1/4})² = ρ^{1/2}` and `ρ^{1/4} ρ^{-1/4} = 1`,
`[σ, 𝒥_β(A)] = 𝒥_β([σ(-iβ/4), A]) + A(iβ/4) [σ, ρ^{1/2}]`. -/
theorem prop_6_4_comm_splitting
    (ρQ ρQinv ρH A σ : Matrix ι ι ℂ)
    (hSq : ρQ * ρQ = ρH)
    (hInvL : ρQinv * ρQ = 1) (hInvR : ρQ * ρQinv = 1) :
    let σMinus := ρQinv * σ * ρQ
    let APlus := ρQ * A * ρQinv
    let D := matComm σ ρH
    matComm σ (jBeta ρQ A) = jBeta ρQ (matComm σMinus A) + APlus * D := by
  intro σMinus APlus D
  simp only [matComm, jBeta, σMinus, APlus, D]
  rw [← hSq]
  have h1 : ρQ * (ρQinv * σ * ρQ * A - A * (ρQinv * σ * ρQ)) * ρQ =
      σ * ρQ * A * ρQ - ρQ * A * ρQinv * σ * ρQ * ρQ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ρQ ρQinv, hInvR, Matrix.one_mul]
  have h2 : ρQ * A * ρQinv * (σ * (ρQ * ρQ) - ρQ * ρQ * σ) =
      ρQ * A * ρQinv * σ * ρQ * ρQ - ρQ * A * ρQ * σ := by
    simp only [Matrix.mul_sub, Matrix.mul_assoc]
    congr 1
    rw [← Matrix.mul_assoc ρQinv ρQ, hInvL, Matrix.one_mul]
  rw [h1, h2]
  simp only [Matrix.mul_assoc]
  abel

/-- **Proposition 6.4(1)** (Exact Third-Term Trace Identity, Eq. 6.7):
For `Y = A(iβ/4) D` with `A = A†`, `ρ_A = 𝒥_β(A)²`, and `B = (ρ^{-1/2} D)(D† ρ^{-1/2})`,
`‖Y‖_HS² - ‖D‖_HS² = Re Tr((ρ_A - ρ_β) B)`. -/
theorem prop_6_4_third_term_identity
    (ρQ ρQinv ρH ρHinv A D : Matrix ι ι ℂ)
    (hρQ : ρQᴴ = ρQ) (hρQinv : ρQinvᴴ = ρQinv)
    (hA : Aᴴ = A)
    (hSq : ρQ * ρQ = ρH) (hSqInv : ρQinv * ρQinv = ρHinv)
    (hInvL : ρQinv * ρQ = 1) (hInvR : ρQ * ρQinv = 1)
    (hHinvL : ρHinv * ρH = 1) (hHinvR : ρH * ρHinv = 1) :
    let Y := (ρQ * A * ρQinv) * D
    let ρA := jBeta ρQ A * jBeta ρQ A
    let ρβ := ρH * ρH
    let B := (ρHinv * D) * (Dᴴ * ρHinv)
    hsNormSq Y - hsNormSq D = (Matrix.trace ((ρA - ρβ) * B)).re := by
  intro Y ρA ρβ B
  unfold hsNormSq hsInner
  have hQinvL : ρHinv * ρQ = ρQinv := by
    rw [← hSqInv, Matrix.mul_assoc, hInvL, Matrix.mul_one]
  have hQinvR : ρQ * ρHinv = ρQinv := by
    rw [← hSqInv, ← Matrix.mul_assoc, hInvR, Matrix.one_mul]
  have hY_tr : Matrix.trace (Yᴴ * Y) = Matrix.trace (ρA * B) := by
    simp only [Y, ρA, B, jBeta]
    have hYadj : (ρQ * A * ρQinv * D)ᴴ = Dᴴ * ρQinv * A * ρQ := by
      simp [Matrix.conjTranspose_mul, hρQ, hρQinv, hA, Matrix.mul_assoc]
    rw [hYadj]
    calc Matrix.trace (Dᴴ * ρQinv * A * ρQ * (ρQ * A * ρQinv * D))
        = Matrix.trace ((Dᴴ * ρHinv) * ((ρQ * A * ρQ * (ρQ * A * ρQ)) * (ρHinv * D))) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc ρHinv ρQ, hQinvL]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc ρQ ρHinv, hQinvR]
      _ = Matrix.trace (((ρQ * A * ρQ * (ρQ * A * ρQ)) * (ρHinv * D)) * (Dᴴ * ρHinv)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace (ρQ * A * ρQ * (ρQ * A * ρQ) * (ρHinv * D * (Dᴴ * ρHinv))) := by
          simp only [Matrix.mul_assoc]
  have hD_tr : Matrix.trace (Dᴴ * D) = Matrix.trace (ρβ * B) := by
    simp only [ρβ, B]
    calc Matrix.trace (Dᴴ * D)
        = Matrix.trace ((Dᴴ * (ρHinv * ρH)) * ((ρH * ρHinv) * D)) := by
          rw [hHinvL, hHinvR, Matrix.mul_one, Matrix.one_mul]
      _ = Matrix.trace ((Dᴴ * ρHinv) * ((ρH * ρH) * (ρHinv * D))) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace (((ρH * ρH) * (ρHinv * D)) * (Dᴴ * ρHinv)) :=
          Matrix.trace_mul_comm _ _
      _ = Matrix.trace (ρH * ρH * (ρHinv * D * (Dᴴ * ρHinv))) := by
          simp only [Matrix.mul_assoc]
  rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, hY_tr, hD_tr]

/-- Exact norm-squared expansion `‖X + Y‖_HS² = ‖X‖_HS² + 2 Re⟨X, Y⟩_HS + ‖Y‖_HS²`. -/
theorem hsNormSq_add (X Y : Matrix ι ι ℂ) :
    hsNormSq (X + Y) = hsNormSq X + 2 * (hsInner X Y).re + hsNormSq Y := by
  unfold hsNormSq hsInner
  have h1 : (X + Y)ᴴ * (X + Y) = Xᴴ * X + Xᴴ * Y + Yᴴ * X + Yᴴ * Y := by
    simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    abel
  rw [h1]
  simp only [Matrix.trace_add, Complex.add_re]
  have hconj : (Matrix.trace (Yᴴ * X)).re = (Matrix.trace (Xᴴ * Y)).re := by
    have htr : Matrix.trace (Yᴴ * X) = star (Matrix.trace (Xᴴ * Y)) := by
      rw [← Matrix.trace_conjTranspose]
      simp [Matrix.conjTranspose_mul]
    rw [htr, Complex.star_def, Complex.conj_re]
  linarith

end ThreeTermDecomposition

section VariationalDecoupling

/-- **Proposition 6.4(2)** (Variational Optimization, Eq. 6.10):
For `S₀ > 0`, `C₀ > 0`, `Λ > 0`, and `N ≥ 4 S₀ / C₀`, choosing `λ = √(S₀/(C₀ N)) Λ ≤ Λ/2`
yields `(1 / λ) (S₀ + C₀ N λ² / Λ²) = (2 √(C₀ S₀) / Λ) √N`. -/
theorem prop_6_4_variational_opt {S₀ C₀ Λ N : ℝ}
    (hS₀ : 0 < S₀) (hC₀ : 0 < C₀) (hΛ : 0 < Λ) (hN : 4 * S₀ / C₀ ≤ N) :
    let lam := Real.sqrt (S₀ / (C₀ * N)) * Λ
    0 < lam ∧ lam ≤ Λ / 2 ∧
    (1 / lam) * (S₀ + C₀ * N * lam ^ 2 / Λ ^ 2) = 2 * Real.sqrt (C₀ * S₀) / Λ * Real.sqrt N := by
  intro lam
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hlam_pos : 0 < lam := by positivity
  have hlam_le : lam ≤ Λ / 2 := by
    simp only [lam]
    have hsq : S₀ / (C₀ * N) ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hmul := mul_le_mul_of_nonneg_left hN hC₀.le
      rw [mul_div_cancel₀ _ hC₀.ne'] at hmul
      linarith
    have hrt : Real.sqrt (S₀ / (C₀ * N)) ≤ 1 / 2 := by
      calc Real.sqrt (S₀ / (C₀ * N)) ≤ Real.sqrt ((1 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
        _ = 1 / 2 := Real.sqrt_sq (by norm_num)
    nlinarith
  have hval : (1 / lam) * (S₀ + C₀ * N * lam ^ 2 / Λ ^ 2) =
      2 * Real.sqrt (C₀ * S₀) / Λ * Real.sqrt N := by
    have hlam2 : lam ^ 2 = S₀ / (C₀ * N) * Λ ^ 2 := by
      simp only [lam, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ S₀ / (C₀ * N))]
    have hterm2 : C₀ * N * lam ^ 2 / Λ ^ 2 = S₀ := by
      rw [hlam2]; field_simp [hC₀.ne', hNpos.ne', hΛ.ne']
    rw [hterm2]
    have hrt : Real.sqrt (S₀ / (C₀ * N)) = Real.sqrt S₀ / (Real.sqrt C₀ * Real.sqrt N) := by
      rw [Real.sqrt_div hS₀.le, Real.sqrt_mul hC₀.le]
    have hprod : Real.sqrt (C₀ * S₀) = Real.sqrt C₀ * Real.sqrt S₀ := Real.sqrt_mul hC₀.le S₀
    simp only [lam]
    rw [hrt, hprod]
    have hsqS : Real.sqrt S₀ * Real.sqrt S₀ = S₀ := Real.mul_self_sqrt hS₀.le
    field_simp [(Real.sqrt_pos.mpr hS₀).ne', (Real.sqrt_pos.mpr hC₀).ne',
      (Real.sqrt_pos.mpr hNpos).ne', hΛ.ne']
    nlinarith [hsqS]
  exact ⟨hlam_pos, hlam_le, hval⟩

/-- **Proposition 6.4(2)** (Cross-Term Cauchy–Schwarz Decoupling, Eq. 6.8):
If `S_β = I + II + III`, `|III| ≤ C₂ √N`, `|II| ≤ 2 √I √(B_avg + III)`, and
`B_avg + |III| ≤ c_B N`, then `S_β ≤ I + (2 √c_B) √(N I) + C₂ √N`. -/
theorem prop_6_4_decoupling_combine {Sβ I II III Bavg C₂ cB N : ℝ}
    (hI : 0 ≤ I) (hN : 0 ≤ N) (hcB : 0 ≤ cB)
    (hdecomp : Sβ = I + II + III)
    (hIII : |III| ≤ C₂ * Real.sqrt N)
    (hII : |II| ≤ 2 * Real.sqrt I * Real.sqrt (Bavg + III))
    (hB : Bavg + |III| ≤ cB * N) :
    Sβ ≤ I + (2 * Real.sqrt cB) * Real.sqrt (N * I) + C₂ * Real.sqrt N := by
  have h1 : Bavg + III ≤ cB * N := by linarith [le_abs_self III]
  have h2 : Real.sqrt (Bavg + III) ≤ Real.sqrt (cB * N) := Real.sqrt_le_sqrt h1
  have hII_le : II ≤ (2 * Real.sqrt cB) * Real.sqrt (N * I) := by
    calc II ≤ |II| := le_abs_self II
      _ ≤ 2 * Real.sqrt I * Real.sqrt (Bavg + III) := hII
      _ ≤ 2 * Real.sqrt I * Real.sqrt (cB * N) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * Real.sqrt I * (Real.sqrt cB * Real.sqrt N) := by rw [Real.sqrt_mul hcB]
      _ = (2 * Real.sqrt cB) * (Real.sqrt N * Real.sqrt I) := by ring
      _ = (2 * Real.sqrt cB) * Real.sqrt (N * I) := by rw [← Real.sqrt_mul hN]
  have hIII_le : III ≤ C₂ * Real.sqrt N := le_trans (le_abs_self III) hIII
  linarith

end VariationalDecoupling

end KrylovChaos
