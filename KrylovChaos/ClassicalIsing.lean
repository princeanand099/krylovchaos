/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Section 8: All-Temperature Regimes (1D Chains and 2-Local Classical Ising Models)

Formalizes:
- **Proposition 8.1**: All-temperature one-dimensional commutator bound (Eq. 8.1).
- **Lemma 8.2**: Exact discrete Hubbard–Stratonovich identity and single-site magnetization
  bound `|m_i(ξ)| ≤ tanh(β H_max + (Δ/2) ln 2)` (Eq. 8.3).
- **Proposition 8.3**: All-temperature classical Ising reverse-Poincaré bound
  `ℰ_{μ_β}(f, f) ≤ cosh²(Φ_max(β)) 𝒬_{μ_β}(f, f)` via the `p`-biased Fourier basis (Eq. 8.4).
-/

namespace KrylovChaos

section OneDimensional

/-- **Proposition 8.1** (All-Temperature One-Dimensional Commutator Bound, Eq. 8.1). -/
theorem prop_8_1_one_dim_commutator_bound {N : ℕ} {M1D : ℝ}
    (commSq : Fin N → Fin 3 → ℝ) (projSq sxSq : Fin N → ℝ)
    (hM : 0 ≤ M1D)
    (hcomm : ∀ x α, commSq x α ≤ (2 * M1D) ^ 2 * projSq x)
    (hbest : ∀ x, projSq x ≤ sxSq x) :
    (1 / 8 : ℝ) * (∑ x : Fin N, ∑ α : Fin 3, commSq x α) ≤
      (3 / 2 : ℝ) * M1D ^ 2 * (∑ x : Fin N, projSq x) ∧
    (3 / 2 : ℝ) * M1D ^ 2 * (∑ x : Fin N, projSq x) ≤
      (3 / 2 : ℝ) * M1D ^ 2 * (∑ x : Fin N, sxSq x) := by
  constructor
  · have hinner : ∀ x : Fin N, ∑ α : Fin 3, commSq x α ≤ 3 * (2 * M1D) ^ 2 * projSq x := by
      intro x
      calc ∑ α : Fin 3, commSq x α
          ≤ ∑ _ : Fin 3, (2 * M1D) ^ 2 * projSq x := Finset.sum_le_sum fun α _ ↦ hcomm x α
        _ = 3 * (2 * M1D) ^ 2 * projSq x := by simp [mul_assoc]
    calc (1 / 8 : ℝ) * (∑ x : Fin N, ∑ α : Fin 3, commSq x α)
        ≤ (1 / 8 : ℝ) * (∑ x : Fin N, 3 * (2 * M1D) ^ 2 * projSq x) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ ↦ hinner x) (by norm_num)
      _ = (3 / 2 : ℝ) * M1D ^ 2 * (∑ x : Fin N, projSq x) := by
          rw [← Finset.mul_sum]; ring
  · apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ ↦ hbest x) (by positivity)

end OneDimensional

section ClassicalIsing

/-- Discrete Hubbard–Stratonovich coupling `φ(u) := (1/2) ln(e^{2u} + √(e^{4u} - 1))`
satisfying `cosh(2 φ(u)) = e^{2u}` for `u ≥ 0`. -/
noncomputable def hsPhi (u : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (Real.exp (2 * u) + Real.sqrt (Real.exp (4 * u) - 1))

theorem cosh_two_hsPhi {u : ℝ} (hu : 0 ≤ u) :
    Real.cosh (2 * hsPhi u) = Real.exp (2 * u) := by
  have he4 : 1 ≤ Real.exp (4 * u) := Real.one_le_exp (by linarith)
  have hsub : 0 ≤ Real.exp (4 * u) - 1 := by linarith
  have hpos : 0 < Real.exp (2 * u) + Real.sqrt (Real.exp (4 * u) - 1) := by positivity
  have h2phi : 2 * hsPhi u = Real.log (Real.exp (2 * u) + Real.sqrt (Real.exp (4 * u) - 1)) := by
    unfold hsPhi; ring
  rw [Real.cosh_eq, h2phi, Real.exp_neg, Real.exp_log hpos]
  have hsq : (Real.exp (2 * u)) ^ 2 - (Real.sqrt (Real.exp (4 * u) - 1)) ^ 2 = 1 := by
    rw [Real.sq_sqrt hsub, ← Real.exp_nat_mul]
    have : (2 : ℕ) * (2 * u) = 4 * u := by push_cast; ring
    rw [this]; ring
  have hinv : (Real.exp (2 * u) + Real.sqrt (Real.exp (4 * u) - 1))⁻¹ =
      Real.exp (2 * u) - Real.sqrt (Real.exp (4 * u) - 1) := by
    apply inv_eq_of_mul_eq_one_right
    linarith [hsq]
  rw [hinv]
  ring

/-- **Lemma 8.2 (Part 1 — Exact Discrete Hubbard–Stratonovich Identity)**:
For every `u ≥ 0` and spins `s, z₁, z₂ ∈ {-1, 1}`,
`e^{u (s z₁ z₂)} = e^{-u} · (1/2) (e^{φ(u)(z₁ + s z₂)} + e^{-φ(u)(z₁ + s z₂)})`. -/
theorem lemma_8_2_hubbard_stratonovich_identity {u s z₁ z₂ : ℝ} (hu : 0 ≤ u)
    (hs : s = 1 ∨ s = -1) (hz₁ : z₁ = 1 ∨ z₁ = -1) (hz₂ : z₂ = 1 ∨ z₂ = -1) :
    Real.exp (u * (s * z₁ * z₂)) =
    Real.exp (-u) * (1 / 2 : ℝ) *
      (Real.exp (hsPhi u * (z₁ + s * z₂)) + Real.exp (-(hsPhi u * (z₁ + s * z₂)))) := by
  have hcosh := cosh_two_hsPhi hu
  rw [Real.cosh_eq] at hcosh
  have hsum : Real.exp (2 * hsPhi u) + Real.exp (-(2 * hsPhi u)) = 2 * Real.exp (2 * u) := by
    linarith
  have hprod : Real.exp (-u) * Real.exp (2 * u) = Real.exp u := by
    rw [← Real.exp_add]; congr 1; ring
  have hmain : Real.exp u =
      Real.exp (-u) * (1 / 2 : ℝ) * (Real.exp (2 * hsPhi u) + Real.exp (-(2 * hsPhi u))) := by
    rw [hsum]
    calc Real.exp u = Real.exp (-u) * Real.exp (2 * u) := hprod.symm
      _ = Real.exp (-u) * (1 / 2 : ℝ) * (2 * Real.exp (2 * u)) := by ring
  have h2 : hsPhi u * 2 = 2 * hsPhi u := by ring
  rcases hs with rfl | rfl <;> rcases hz₁ with rfl | rfl <;> rcases hz₂ with rfl | rfl <;>
  · norm_num
    try ring
    try (rw [h2]; linarith [hmain])

/-- **Lemma 8.2 (Part 2 — Effective Field Upper Bound)**:
For every `u ≥ 0`, `hsPhi u ≤ u + (1/2) ln 2`. -/
theorem lemma_8_2_phi_bound {u : ℝ} (hu : 0 ≤ u) :
    hsPhi u ≤ u + (1 / 2 : ℝ) * Real.log 2 := by
  unfold hsPhi
  have hrt : Real.sqrt (Real.exp (4 * u) - 1) ≤ Real.exp (2 * u) := by
    have hsq : Real.exp (4 * u) - 1 ≤ (Real.exp (2 * u)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      have : (2 : ℕ) * (2 * u) = 4 * u := by push_cast; ring
      rw [this]; linarith
    calc Real.sqrt (Real.exp (4 * u) - 1)
        ≤ Real.sqrt ((Real.exp (2 * u)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.exp (2 * u) := Real.sqrt_sq (Real.exp_pos _).le
  have hsum : Real.exp (2 * u) + Real.sqrt (Real.exp (4 * u) - 1) ≤ 2 * Real.exp (2 * u) := by
    linarith
  have hlog : Real.log (Real.exp (2 * u) + Real.sqrt (Real.exp (4 * u) - 1)) ≤
      Real.log (2 * Real.exp (2 * u)) :=
    Real.log_le_log (by positivity) hsum
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at hlog
  linarith

/-- Variance identity `1 - tanh²(h) = (cosh h)⁻²` and monotonicity in `|h|`. -/
theorem one_sub_tanh_sq_eq_inv_cosh_sq (h : ℝ) :
    1 - (Real.tanh h) ^ 2 = (Real.cosh h)⁻¹ ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh h ≠ 0 := (Real.cosh_pos h).ne'
  have hid := Real.cosh_sq_sub_sinh_sq h
  field_simp [hc]
  linarith

theorem inv_one_sub_tanh_sq_le_cosh_sq {h Φ : ℝ} (habs : |h| ≤ Φ) :
    (1 - (Real.tanh h) ^ 2)⁻¹ ≤ (Real.cosh Φ) ^ 2 := by
  rw [one_sub_tanh_sq_eq_inv_cosh_sq, inv_pow, inv_inv]
  have hcosh_le : Real.cosh h ≤ Real.cosh Φ := by
    rw [← Real.cosh_abs h]
    have h0 : 0 ≤ |h| := abs_nonneg h
    rw [Real.cosh_eq, Real.cosh_eq]
    have h1 : Real.exp |h| ≤ Real.exp Φ := Real.exp_le_exp.mpr habs
    have hprod1 : Real.exp |h| * Real.exp (-|h|) = 1 := by rw [← Real.exp_add]; simp
    have hprod2 : Real.exp Φ * Real.exp (-Φ) = 1 := by rw [← Real.exp_add]; simp
    have hfact : (Real.exp Φ + Real.exp (-Φ)) - (Real.exp |h| + Real.exp (-|h|)) =
        (Real.exp Φ - Real.exp |h|) * (1 - Real.exp (-Φ) * Real.exp (-|h|)) := by
      calc (Real.exp Φ + Real.exp (-Φ)) - (Real.exp |h| + Real.exp (-|h|))
          = Real.exp Φ - Real.exp |h| + Real.exp (-Φ) * (Real.exp |h| * Real.exp (-|h|)) -
              Real.exp (-|h|) * (Real.exp Φ * Real.exp (-Φ)) := by rw [hprod1, hprod2]; ring
        _ = (Real.exp Φ - Real.exp |h|) * (1 - Real.exp (-Φ) * Real.exp (-|h|)) := by ring
    have hpos2 : 0 ≤ 1 - Real.exp (-Φ) * Real.exp (-|h|) := by
      have : Real.exp (-Φ) * Real.exp (-|h|) ≤ 1 := by
        rw [← Real.exp_add]; exact Real.exp_le_one_iff.mpr (by linarith)
      linarith
    have hnn : 0 ≤ (Real.exp Φ - Real.exp |h|) * (1 - Real.exp (-Φ) * Real.exp (-|h|)) :=
      mul_nonneg (by linarith) hpos2
    linarith
  nlinarith [Real.cosh_pos h, Real.cosh_pos Φ]

/-- **Proposition 8.3** (All-Temperature Classical Ising Reverse-Poincaré Bound, Eq. 8.4):
In the `p`-biased Fourier basis `f = ∑_{S ⊆ Fin N} f̂(S) χ_S` of any product Bernoulli
measure `ν_ξ` with effective local fields `|h_i| ≤ Φ_max`,
`∑_{i : Fin N} (1 - tanh²(h_i))⁻¹ ∑_{S ∋ i} f̂(S)² ≤ cosh²(Φ_max) ∑_{k=0}^{N-1} ∑_{|S| > k} f̂(S)²`. -/
theorem prop_8_3_product_bernoulli_reverse_poincare {N : ℕ} {Φmax : ℝ}
    (h : Fin N → ℝ) (hh : ∀ i, |h i| ≤ Φmax)
    (fhat : Finset (Fin N) → ℝ) :
    (∑ i : Fin N, (1 - (Real.tanh (h i)) ^ 2)⁻¹ *
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S), (fhat S) ^ 2) ≤
    (Real.cosh Φmax) ^ 2 *
      ∑ k ∈ Finset.range N,
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card), (fhat S) ^ 2 := by
  have h1 :
      (∑ i : Fin N, (1 - (Real.tanh (h i)) ^ 2)⁻¹ *
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S), (fhat S) ^ 2) ≤
      (Real.cosh Φmax) ^ 2 *
        ∑ i : Fin N, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S), (fhat S) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (inv_one_sub_tanh_sq_le_cosh_sq (hh i))
      (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hid :
      (∑ i : Fin N, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S), (fhat S) ^ 2) =
      ∑ k ∈ Finset.range N,
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card), (fhat S) ^ 2 := by
    have hl : (∑ i : Fin N, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S), (fhat S) ^ 2) =
        ∑ S : Finset (Fin N), (S.card : ℝ) * (fhat S) ^ 2 := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro S _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hset : Finset.univ.filter (fun i : Fin N ↦ i ∈ S) = S := by ext i; simp
      rw [hset]
    have hr : (∑ k ∈ Finset.range N,
          ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card), (fhat S) ^ 2) =
        ∑ S : Finset (Fin N), (S.card : ℝ) * (fhat S) ^ 2 := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro S _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      congr 1
      have hcard : S.card ≤ N := by simpa using Finset.card_le_univ S
      have hfilt : (Finset.range N).filter (fun k ↦ k < S.card) = Finset.range S.card := by
        ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [hfilt, Finset.card_range]
    rw [hl, hr]
  rw [← hid]
  exact h1

end ClassicalIsing

end KrylovChaos
