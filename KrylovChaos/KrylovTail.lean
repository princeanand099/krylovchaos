/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Section 3: Non-Asymptotic Krylov Tail Estimates

Formalizes:
- **Lemma 3.1**: Finite-chain moment generating inequality via the method of characteristics
  along `tanh(θ(t)/4) = tanh(θ₀/4) e^{-2αt}` (Eqs. 3.1–3.4).
- **Theorem 1.1(a)**: Non-asymptotic exponential tail bound (Eq. 1.12), Krylov complexity
  exponential bound (Eq. 1.13), and asymptotic growth rate `lim sup_{t→∞} (1/t) ln K(t) ≤ 2α`,
  for both finite chains and `ℓ²` limits of finite truncations via Fatou's lemma.
-/

namespace KrylovChaos

/-- Characteristic curve `u(t) = tanh(θ₀/4) e^{-2αt}`. -/
noncomputable def charU (α θ₀ t : ℝ) : ℝ :=
  Real.tanh (θ₀ / 4) * Real.exp (-2 * α * t)

/-- Characteristic curve `θ(t) = 2 ln((1 + u(t))/(1 - u(t)))` solving Eq. (3.1). -/
noncomputable def charTheta (α θ₀ t : ℝ) : ℝ :=
  2 * Real.log ((1 + charU α θ₀ t) / (1 - charU α θ₀ t))

/-- Finite-chain moment generating function `G_{Nmax}(θ, t) := ∑_{n=0}^{Nmax} e^{θ n} φ_n(t)²`. -/
noncomputable def finiteMGF (Nmax : ℕ) (φ : ℕ → ℝ → ℝ) (θ t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nmax + 1), Real.exp (θ * (n : ℝ)) * (φ n t) ^ 2

/-- Finite-chain Krylov complexity `K_{Nmax}(t) := ∑_{n=0}^{Nmax} n φ_n(t)²`. -/
noncomputable def finiteKrylovComplexity (Nmax : ℕ) (φ : ℕ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (Nmax + 1), (n : ℝ) * (φ n t) ^ 2

theorem sinh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  rw [Real.sinh_eq]
  have : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (sinh_pos_of_pos hx) (Real.cosh_pos x)

theorem tanh_lt_one (x : ℝ) : Real.tanh x < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_one (Real.cosh_pos x)]
  rw [Real.sinh_eq, Real.cosh_eq]
  have : 0 < Real.exp (-x) := Real.exp_pos (-x)
  linarith

theorem charU_pos {α θ₀ t : ℝ} (hθ₀ : 0 < θ₀) : 0 < charU α θ₀ t := by
  unfold charU
  exact mul_pos (tanh_pos_of_pos (by linarith)) (Real.exp_pos _)

theorem charU_lt_one {α θ₀ t : ℝ} (hα : 0 < α) (hθ₀ : 0 < θ₀) (ht : 0 ≤ t) :
    charU α θ₀ t < 1 := by
  unfold charU
  have h1 : Real.tanh (θ₀ / 4) < 1 := tanh_lt_one (θ₀ / 4)
  have h2 : Real.exp (-2 * α * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h3 : 0 < Real.tanh (θ₀ / 4) := tanh_pos_of_pos (by linarith)
  nlinarith

theorem charTheta_zero {α θ₀ : ℝ} (hθ₀ : 0 < θ₀) : charTheta α θ₀ 0 = θ₀ := by
  unfold charTheta charU
  simp only [mul_zero, Real.exp_zero, mul_one]
  have h1 : (1 + Real.tanh (θ₀ / 4)) / (1 - Real.tanh (θ₀ / 4)) = Real.exp (θ₀ / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have hc : Real.exp (θ₀ / 4) + Real.exp (-(θ₀ / 4)) ≠ 0 := by positivity
    have hpos : Real.exp (-(θ₀ / 4)) ≠ 0 := (Real.exp_pos _).ne'
    have hrel : Real.exp (-(θ₀ / 4)) * Real.exp (θ₀ / 2) = Real.exp (θ₀ / 4) := by
      rw [← Real.exp_add]; congr 1; ring
    field_simp [hc, hpos]
    linarith
  rw [h1, Real.log_exp]
  ring

theorem charTheta_pos {α θ₀ t : ℝ} (hα : 0 < α) (hθ₀ : 0 < θ₀) (ht : 0 ≤ t) :
    0 < charTheta α θ₀ t := by
  unfold charTheta
  have hu0 := charU_pos (α := α) (t := t) hθ₀
  have hu1 := charU_lt_one hα hθ₀ ht
  have hgt : 1 < (1 + charU α θ₀ t) / (1 - charU α θ₀ t) := by
    rw [one_lt_div (by linarith)]
    linarith
  have hlog : 0 < Real.log ((1 + charU α θ₀ t) / (1 - charU α θ₀ t)) := Real.log_pos hgt
  linarith

/-- Characteristic identity (Eq. 3.1): `tanh(θ(t)/4) = tanh(θ₀/4) e^{-2αt}`. -/
theorem tanh_charTheta_div_four {α θ₀ t : ℝ} (hα : 0 < α) (hθ₀ : 0 < θ₀) (ht : 0 ≤ t) :
    Real.tanh (charTheta α θ₀ t / 4) = charU α θ₀ t := by
  set u := charU α θ₀ t
  have hu0 : 0 < u := charU_pos hθ₀
  have hu1 : u < 1 := charU_lt_one hα hθ₀ ht
  have hq : 0 < (1 + u) / (1 - u) := by positivity
  have hexp : Real.exp (charTheta α θ₀ t / 2) = (1 + u) / (1 - u) := by
    unfold charTheta
    rw [show 2 * Real.log ((1 + u) / (1 - u)) / 2 = Real.log ((1 + u) / (1 - u)) by ring]
    exact Real.exp_log hq
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hmul : Real.exp (charTheta α θ₀ t / 4) * Real.exp (charTheta α θ₀ t / 4) =
      Real.exp (charTheta α θ₀ t / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hinv : Real.exp (-(charTheta α θ₀ t / 4)) * Real.exp (charTheta α θ₀ t / 4) = 1 := by
    rw [← Real.exp_add]; simp
  have hp : Real.exp (charTheta α θ₀ t / 4) ≠ 0 := (Real.exp_pos _).ne'
  have hd : Real.exp (charTheta α θ₀ t / 4) + Real.exp (-(charTheta α θ₀ t / 4)) ≠ 0 := by
    positivity
  have hnum : (Real.exp (charTheta α θ₀ t / 4) - Real.exp (-(charTheta α θ₀ t / 4))) *
      Real.exp (charTheta α θ₀ t / 4) = Real.exp (charTheta α θ₀ t / 2) - 1 := by
    nlinarith [hmul, hinv]
  have hden : (Real.exp (charTheta α θ₀ t / 4) + Real.exp (-(charTheta α θ₀ t / 4))) *
      Real.exp (charTheta α θ₀ t / 4) = Real.exp (charTheta α θ₀ t / 2) + 1 := by
    nlinarith [hmul, hinv]
  have hratio : (Real.exp (charTheta α θ₀ t / 4) - Real.exp (-(charTheta α θ₀ t / 4))) /
      (Real.exp (charTheta α θ₀ t / 4) + Real.exp (-(charTheta α θ₀ t / 4))) =
      (Real.exp (charTheta α θ₀ t / 2) - 1) / (Real.exp (charTheta α θ₀ t / 2) + 1) := by
    rw [← hnum, ← hden, mul_div_mul_right _ _ hp]
  rw [show (Real.exp (charTheta α θ₀ t / 4) - Real.exp (-(charTheta α θ₀ t / 4))) / 2 /
      ((Real.exp (charTheta α θ₀ t / 4) + Real.exp (-(charTheta α θ₀ t / 4))) / 2) =
      (Real.exp (charTheta α θ₀ t / 4) - Real.exp (-(charTheta α θ₀ t / 4))) /
      (Real.exp (charTheta α θ₀ t / 4) + Real.exp (-(charTheta α θ₀ t / 4))) by field_simp [hd]]
  rw [hratio, hexp]
  have h1mu : 1 - u ≠ 0 := by linarith
  field_simp [h1mu]
  ring

/-- Characteristic ODE (Eq. 3.4): `dθ/dt = -4α sinh(θ(t)/2)`. -/
theorem hasDerivAt_charTheta {α θ₀ t : ℝ} (hα : 0 < α) (hθ₀ : 0 < θ₀) (ht : 0 ≤ t) :
    HasDerivAt (charTheta α θ₀) (-4 * α * Real.sinh (charTheta α θ₀ t / 2)) t := by
  set u := charU α θ₀ t
  have hu0 : 0 < u := charU_pos hθ₀
  have hu1 : u < 1 := charU_lt_one hα hθ₀ ht
  have h1pu : 0 < 1 + u := by linarith
  have h1mu : 0 < 1 - u := by linarith
  have h1mu2 : 1 - u ^ 2 ≠ 0 := by nlinarith
  have hdu : HasDerivAt (charU α θ₀) (-2 * α * u) t := by
    unfold charU
    have hlin : HasDerivAt (fun s ↦ -2 * α * s) (-2 * α) t := by
      simpa using (hasDerivAt_id' t).const_mul (-2 * α)
    have hexp := hlin.exp
    convert hexp.const_mul (Real.tanh (θ₀ / 4)) using 1
    simp [u, charU]; ring
  have hnum : HasDerivAt (fun s ↦ 1 + charU α θ₀ s) (-2 * α * u) t := by
    simpa using hdu.const_add 1
  have hden : HasDerivAt (fun s ↦ 1 - charU α θ₀ s) (2 * α * u) t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).fun_sub hdu
  have hquot : HasDerivAt (fun s ↦ (1 + charU α θ₀ s) / (1 - charU α θ₀ s))
      (((-2 * α * u) * (1 - u) - (1 + u) * (2 * α * u)) / (1 - u) ^ 2) t :=
    hnum.fun_div hden h1mu.ne'
  have hlog : HasDerivAt (fun s ↦ Real.log ((1 + charU α θ₀ s) / (1 - charU α θ₀ s)))
      ((((-2 * α * u) * (1 - u) - (1 + u) * (2 * α * u)) / (1 - u) ^ 2) /
        ((1 + u) / (1 - u))) t :=
    hquot.log (div_pos h1pu h1mu).ne'
  have h2log := hlog.const_mul 2
  have hsinh : Real.sinh (charTheta α θ₀ t / 2) = 2 * u / (1 - u ^ 2) := by
    have hexp : Real.exp (charTheta α θ₀ t / 2) = (1 + u) / (1 - u) := by
      unfold charTheta
      rw [show 2 * Real.log ((1 + u) / (1 - u)) / 2 = Real.log ((1 + u) / (1 - u)) by ring]
      exact Real.exp_log (div_pos h1pu h1mu)
    have hexp_neg : Real.exp (-(charTheta α θ₀ t / 2)) = (1 - u) / (1 + u) := by
      rw [Real.exp_neg, hexp, inv_div]
    rw [Real.sinh_eq, hexp, hexp_neg]
    field_simp [h1pu.ne', h1mu.ne', h1mu2]
    ring
  have hval : 2 * (((-2 * α * u) * (1 - u) - (1 + u) * (2 * α * u)) / (1 - u) ^ 2 /
      ((1 + u) / (1 - u))) = -4 * α * Real.sinh (charTheta α θ₀ t / 2) := by
    rw [hsinh]
    field_simp [h1pu.ne', h1mu.ne', h1mu2]
    ring
  rw [hval] at h2log
  exact h2log

/-- Unitarity of finite-chain Krylov evolution: `∑_{n=0}^{Nmax} φ_n(t)² = 1` for all `t`. -/
theorem finite_chain_unitarity {Nmax : ℕ} (b : ℕ → ℝ) (φ : ℕ → ℝ → ℝ)
    (hb0 : b 0 = 0) (hbN : b (Nmax + 1) = 0)
    (hode : ∀ n ≤ Nmax, ∀ t, HasDerivAt (φ n) (b n * φ (n - 1) t - b (n + 1) * φ (n + 1) t) t)
    (hinit : ∀ n ≤ Nmax, φ n 0 = if n = 0 then 1 else 0) :
    ∀ t : ℝ, ∑ n ∈ Finset.range (Nmax + 1), (φ n t) ^ 2 = 1 := by
  let S : ℝ → ℝ := fun t ↦ ∑ n ∈ Finset.range (Nmax + 1), (φ n t) ^ 2
  have hderiv : ∀ t : ℝ, HasDerivAt S 0 t := by
    intro t
    have hsum : HasDerivAt S
        (∑ n ∈ Finset.range (Nmax + 1),
          2 * φ n t * (b n * φ (n - 1) t - b (n + 1) * φ (n + 1) t)) t := by
      apply HasDerivAt.fun_sum
      intro n hn
      have hnle : n ≤ Nmax := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hsq : HasDerivAt (fun s ↦ (φ n s) ^ 2)
          (2 * (φ n t) ^ 1 * (b n * φ (n - 1) t - b (n + 1) * φ (n + 1) t)) t :=
        (hode n hnle t).fun_pow 2
      simpa using hsq
    have hzero : ∑ n ∈ Finset.range (Nmax + 1),
        2 * φ n t * (b n * φ (n - 1) t - b (n + 1) * φ (n + 1) t) = 0 := by
      have hterm : ∀ n ∈ Finset.range (Nmax + 1),
          2 * φ n t * (b n * φ (n - 1) t - b (n + 1) * φ (n + 1) t) =
          (2 * b n * φ n t * φ (n - 1) t) - (2 * b (n + 1) * φ (n + 1) t * φ n t) := by
        intro n _; ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
      have hshift : ∑ n ∈ Finset.range (Nmax + 1), 2 * b n * φ n t * φ (n - 1) t =
          ∑ n ∈ Finset.range Nmax, 2 * b (n + 1) * φ (n + 1) t * φ n t := by
        rw [Finset.sum_range_succ']
        simp [hb0]
      have hshift2 : ∑ n ∈ Finset.range (Nmax + 1), 2 * b (n + 1) * φ (n + 1) t * φ n t =
          ∑ n ∈ Finset.range Nmax, 2 * b (n + 1) * φ (n + 1) t * φ n t := by
        rw [Finset.sum_range_succ]
        simp [hbN]
      rw [hshift, hshift2, sub_self]
    rwa [hzero] at hsum
  have hconst : ∀ t : ℝ, S t = S 0 :=
    fun t ↦ is_const_of_deriv_eq_zero (fun s ↦ (hderiv s).differentiableAt)
      (fun s ↦ (hderiv s).deriv) t 0
  intro t
  change S t = 1
  rw [hconst t]
  simp only [S]
  rw [Finset.sum_range_succ']
  have h0 : φ 0 0 = 1 := by simpa using hinit 0 (Nat.zero_le Nmax)
  have hrest : ∀ k ∈ Finset.range Nmax, (φ (k + 1) 0) ^ 2 = 0 := by
    intro k hk
    have hle : k + 1 ≤ Nmax := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    rw [hinit (k + 1) hle]
    simp
  rw [Finset.sum_eq_zero hrest, h0]
  norm_num

/-- **Lemma 3.1** (Finite-Chain Moment Generating Inequality, Eq. 3.2). -/
theorem lemma_3_1_finite_chain_mgf {Nmax : ℕ} {α γ θ₀ : ℝ}
    (b : ℕ → ℝ) (φ : ℕ → ℝ → ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (hb0 : b 0 = 0) (hbN : b (Nmax + 1) = 0)
    (hb_nn : ∀ n, 1 ≤ n → n ≤ Nmax → 0 ≤ b n)
    (hb_lin : ∀ n, 1 ≤ n → n ≤ Nmax → b n ≤ α * (n : ℝ) + γ)
    (hode : ∀ n ≤ Nmax, ∀ t, HasDerivAt (φ n) (b n * φ (n - 1) t - b (n + 1) * φ (n + 1) t) t)
    (hinit : ∀ n ≤ Nmax, φ n 0 = if n = 0 then 1 else 0)
    (t : ℝ) (ht : 0 ≤ t) :
    finiteMGF Nmax φ (charTheta α θ₀ t) t ≤
      Real.exp ((1 / 2 + γ / α) * (θ₀ - charTheta α θ₀ t)) ∧
    Real.exp ((1 / 2 + γ / α) * (θ₀ - charTheta α θ₀ t)) ≤
      Real.exp ((1 / 2 + γ / α) * θ₀) := by
  have hunit := finite_chain_unitarity b φ hb0 hbN hode hinit
  let G : ℝ → ℝ := fun s ↦ finiteMGF Nmax φ (charTheta α θ₀ s) s
  let H : ℝ → ℝ := fun s ↦ Real.log (G s) + (1 / 2 + γ / α) * (charTheta α θ₀ s - θ₀)
  let G' : ℝ → ℝ := fun s ↦
    ∑ n ∈ Finset.range (Nmax + 1),
      ((n : ℝ) * (-4 * α * Real.sinh (charTheta α θ₀ s / 2)) *
          Real.exp (charTheta α θ₀ s * (n : ℝ)) * (φ n s) ^ 2 +
        Real.exp (charTheta α θ₀ s * (n : ℝ)) *
          (2 * φ n s * (b n * φ (n - 1) s - b (n + 1) * φ (n + 1) s)))
  let H' : ℝ → ℝ := fun s ↦
    G' s / G s + (1 / 2 + γ / α) * (-4 * α * Real.sinh (charTheta α θ₀ s / 2))
  have hG_ge_one : ∀ s ≥ 0, 1 ≤ G s := by
    intro s hs
    have hθs := (charTheta_pos hα hθ₀ hs).le
    calc (1 : ℝ) = ∑ n ∈ Finset.range (Nmax + 1), (φ n s) ^ 2 := (hunit s).symm
      _ ≤ ∑ n ∈ Finset.range (Nmax + 1), Real.exp (charTheta α θ₀ s * (n : ℝ)) * (φ n s) ^ 2 := by
        apply Finset.sum_le_sum
        intro n _
        have hexp : 1 ≤ Real.exp (charTheta α θ₀ s * (n : ℝ)) :=
          Real.one_le_exp (mul_nonneg hθs (Nat.cast_nonneg n))
        nlinarith [sq_nonneg (φ n s)]
  have hG_deriv : ∀ s ≥ 0, HasDerivAt G (G' s) s := by
    intro s hs
    apply HasDerivAt.fun_sum
    intro n hn
    have hnle : n ≤ Nmax := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hθd := hasDerivAt_charTheta hα hθ₀ hs
    have hexp : HasDerivAt (fun u ↦ Real.exp (charTheta α θ₀ u * (n : ℝ)))
        (Real.exp (charTheta α θ₀ s * (n : ℝ)) *
          ((-4 * α * Real.sinh (charTheta α θ₀ s / 2)) * (n : ℝ))) s :=
      (hθd.mul_const (n : ℝ)).exp
    have hsq : HasDerivAt (fun u ↦ (φ n u) ^ 2)
        (2 * φ n s * (b n * φ (n - 1) s - b (n + 1) * φ (n + 1) s)) s := by
      simpa using (hode n hnle s).fun_pow 2
    convert hexp.fun_mul hsq using 1
    ring
  have hdiff_ineq : ∀ s ≥ 0, G' s ≤ 2 * (α + 2 * γ) * Real.sinh (charTheta α θ₀ s / 2) * G s := by
    intro s hs
    simp only [G']
    set θ := charTheta α θ₀ s with hθ_def
    have hθpos : 0 < θ := charTheta_pos hα hθ₀ hs
    have hsinh_pos : 0 < Real.sinh (θ / 2) := sinh_pos_of_pos (by linarith)
    rw [Finset.sum_add_distrib]
    have htime_eq :
        ∑ n ∈ Finset.range (Nmax + 1),
          Real.exp (θ * (n : ℝ)) * (2 * φ n s * (b n * φ (n - 1) s - b (n + 1) * φ (n + 1) s)) =
        ∑ k ∈ Finset.range Nmax,
          2 * b (k + 1) * φ (k + 1) s * φ k s *
            (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) - Real.exp (θ * (k : ℝ))) := by
      have hsplit : ∀ n ∈ Finset.range (Nmax + 1),
          Real.exp (θ * (n : ℝ)) * (2 * φ n s * (b n * φ (n - 1) s - b (n + 1) * φ (n + 1) s)) =
          (2 * b n * φ n s * φ (n - 1) s * Real.exp (θ * (n : ℝ))) -
          (2 * b (n + 1) * φ (n + 1) s * φ n s * Real.exp (θ * (n : ℝ))) := by
        intro n _; ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
      have h1 : ∑ n ∈ Finset.range (Nmax + 1),
            2 * b n * φ n s * φ (n - 1) s * Real.exp (θ * (n : ℝ)) =
          ∑ k ∈ Finset.range Nmax,
            2 * b (k + 1) * φ (k + 1) s * φ k s * Real.exp (θ * ((k + 1 : ℕ) : ℝ)) := by
        rw [Finset.sum_range_succ']; simp [hb0]
      have h2 : ∑ n ∈ Finset.range (Nmax + 1),
            2 * b (n + 1) * φ (n + 1) s * φ n s * Real.exp (θ * (n : ℝ)) =
          ∑ k ∈ Finset.range Nmax,
            2 * b (k + 1) * φ (k + 1) s * φ k s * Real.exp (θ * (k : ℝ)) := by
        rw [Finset.sum_range_succ]; simp [hbN]
      rw [h1, h2, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _; ring
    rw [htime_eq]
    have hterm_le : ∀ k ∈ Finset.range Nmax,
        2 * b (k + 1) * φ (k + 1) s * φ k s *
            (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) - Real.exp (θ * (k : ℝ))) ≤
        2 * Real.sinh (θ / 2) * (α * ((k + 1 : ℕ) : ℝ) + γ) *
            (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) s) ^ 2 +
              Real.exp (θ * (k : ℝ)) * (φ k s) ^ 2) := by
      intro k hk
      have hk1 : 1 ≤ k + 1 := Nat.succ_pos k
      have hkN : k + 1 ≤ Nmax := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      have hbk_nn : 0 ≤ b (k + 1) := hb_nn (k + 1) hk1 hkN
      have hbk_le : b (k + 1) ≤ α * ((k + 1 : ℕ) : ℝ) + γ := hb_lin (k + 1) hk1 hkN
      have hexp_diff :
          Real.exp (θ * ((k + 1 : ℕ) : ℝ)) - Real.exp (θ * (k : ℝ)) =
          2 * Real.sinh (θ / 2) * Real.exp (θ * ((k + 1 : ℕ) : ℝ) / 2) *
            Real.exp (θ * (k : ℝ) / 2) := by
        rw [Real.sinh_eq]
        have h1 : Real.exp (θ / 2) * Real.exp (θ * ((k + 1 : ℕ) : ℝ) / 2) *
            Real.exp (θ * (k : ℝ) / 2) = Real.exp (θ * ((k + 1 : ℕ) : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
        have h2 : Real.exp (-(θ / 2)) * Real.exp (θ * ((k + 1 : ℕ) : ℝ) / 2) *
            Real.exp (θ * (k : ℝ) / 2) = Real.exp (θ * (k : ℝ)) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
        linarith
      rw [hexp_diff]
      set u := Real.exp (θ * ((k + 1 : ℕ) : ℝ) / 2) * φ (k + 1) s
      set v := Real.exp (θ * (k : ℝ) / 2) * φ k s
      have hu2 : u ^ 2 = Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) s) ^ 2 := by
        simp only [u, mul_pow, ← Real.exp_nat_mul]; congr 2; ring
      have hv2 : v ^ 2 = Real.exp (θ * (k : ℝ)) * (φ k s) ^ 2 := by
        simp only [v, mul_pow, ← Real.exp_nat_mul]; congr 2; ring
      have hamgm : 2 * u * v ≤ u ^ 2 + v ^ 2 := by nlinarith [sq_nonneg (u - v)]
      have hlhs : 2 * b (k + 1) * φ (k + 1) s * φ k s *
            (2 * Real.sinh (θ / 2) * Real.exp (θ * ((k + 1 : ℕ) : ℝ) / 2) *
              Real.exp (θ * (k : ℝ) / 2)) =
          2 * Real.sinh (θ / 2) * b (k + 1) * (2 * u * v) := by
        simp only [u, v]; ring
      rw [hlhs, ← hu2, ← hv2]
      have hstep1 : 2 * Real.sinh (θ / 2) * b (k + 1) * (2 * u * v) ≤
          2 * Real.sinh (θ / 2) * b (k + 1) * (u ^ 2 + v ^ 2) :=
        mul_le_mul_of_nonneg_left hamgm (by positivity)
      have hstep2 : 2 * Real.sinh (θ / 2) * b (k + 1) * (u ^ 2 + v ^ 2) ≤
          2 * Real.sinh (θ / 2) * (α * ((k + 1 : ℕ) : ℝ) + γ) * (u ^ 2 + v ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbk_le (by positivity))
          (add_nonneg (sq_nonneg u) (sq_nonneg v))
      exact le_trans hstep1 hstep2
    have hsum_le := Finset.sum_le_sum hterm_le
    have hGs_eq : G s = ∑ n ∈ Finset.range (Nmax + 1), Real.exp (θ * (n : ℝ)) * (φ n s) ^ 2 := by
      simp only [G, finiteMGF, ← hθ_def]
    have hsplit_rhs :
        ∑ k ∈ Finset.range Nmax,
          2 * Real.sinh (θ / 2) * (α * ((k + 1 : ℕ) : ℝ) + γ) *
            (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) s) ^ 2 +
              Real.exp (θ * (k : ℝ)) * (φ k s) ^ 2) ≤
        2 * Real.sinh (θ / 2) *
          (2 * α * (∑ n ∈ Finset.range (Nmax + 1),
              (n : ℝ) * Real.exp (θ * (n : ℝ)) * (φ n s) ^ 2) +
            (α + 2 * γ) * G s) := by
      have hfactor :
          ∑ k ∈ Finset.range Nmax,
            2 * Real.sinh (θ / 2) * (α * ((k + 1 : ℕ) : ℝ) + γ) *
              (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) s) ^ 2 +
                Real.exp (θ * (k : ℝ)) * (φ k s) ^ 2) =
          2 * Real.sinh (θ / 2) *
            ((∑ k ∈ Finset.range Nmax,
                (α * ((k + 1 : ℕ) : ℝ) + γ) *
                  Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) s) ^ 2) +
             (∑ k ∈ Finset.range Nmax,
                (α * ((k + 1 : ℕ) : ℝ) + γ) *
                  Real.exp (θ * (k : ℝ)) * (φ k s) ^ 2)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _; ring
      rw [hfactor]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hpart1 :
          ∑ k ∈ Finset.range Nmax,
            (α * ((k + 1 : ℕ) : ℝ) + γ) *
              Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) s) ^ 2 ≤
          α * (∑ n ∈ Finset.range (Nmax + 1),
              (n : ℝ) * Real.exp (θ * (n : ℝ)) * (φ n s) ^ 2) + γ * G s := by
        have hrew : ∀ k ∈ Finset.range Nmax,
            (α * ((k + 1 : ℕ) : ℝ) + γ) *
              Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) s) ^ 2 =
            α * (((k + 1 : ℕ) : ℝ) * Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) s) ^ 2) +
            γ * (Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) s) ^ 2) := by
          intro k _; ring
        rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have ha : ∑ k ∈ Finset.range Nmax,
              ((k + 1 : ℕ) : ℝ) * Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) s) ^ 2 =
            ∑ n ∈ Finset.range (Nmax + 1), (n : ℝ) * Real.exp (θ * (n : ℝ)) * (φ n s) ^ 2 := by
          rw [Finset.sum_range_succ']; simp
        have hg : ∑ k ∈ Finset.range Nmax,
              Real.exp (θ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) s) ^ 2 ≤ G s := by
          rw [hGs_eq, Finset.sum_range_succ']
          have h0nn : 0 ≤ Real.exp (θ * (0 : ℝ)) * (φ 0 s) ^ 2 := by positivity
          simpa using h0nn
        rw [ha]
        nlinarith
      have hpart2 :
          ∑ k ∈ Finset.range Nmax,
            (α * ((k + 1 : ℕ) : ℝ) + γ) * Real.exp (θ * (k : ℝ)) * (φ k s) ^ 2 ≤
          α * (∑ n ∈ Finset.range (Nmax + 1),
              (n : ℝ) * Real.exp (θ * (n : ℝ)) * (φ n s) ^ 2) + (α + γ) * G s := by
        have hrew : ∀ k ∈ Finset.range Nmax,
            (α * ((k + 1 : ℕ) : ℝ) + γ) * Real.exp (θ * (k : ℝ)) * (φ k s) ^ 2 =
            α * ((k : ℝ) * Real.exp (θ * (k : ℝ)) * (φ k s) ^ 2) +
            (α + γ) * (Real.exp (θ * (k : ℝ)) * (φ k s) ^ 2) := by
          intro k _; push_cast; ring
        rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have ha : ∑ k ∈ Finset.range Nmax,
              (k : ℝ) * Real.exp (θ * (k : ℝ)) * (φ k s) ^ 2 ≤
            ∑ n ∈ Finset.range (Nmax + 1), (n : ℝ) * Real.exp (θ * (n : ℝ)) * (φ n s) ^ 2 := by
          rw [Finset.sum_range_succ]
          have hnn : 0 ≤ (Nmax : ℝ) * Real.exp (θ * (Nmax : ℝ)) * (φ Nmax s) ^ 2 := by positivity
          linarith
        have hg : ∑ k ∈ Finset.range Nmax, Real.exp (θ * (k : ℝ)) * (φ k s) ^ 2 ≤ G s := by
          rw [hGs_eq, Finset.sum_range_succ]
          have hnn : 0 ≤ Real.exp (θ * (Nmax : ℝ)) * (φ Nmax s) ^ 2 := by positivity
          linarith
        nlinarith
      linarith
    have hfirst :
        ∑ n ∈ Finset.range (Nmax + 1),
          (n : ℝ) * (-4 * α * Real.sinh (θ / 2)) * Real.exp (θ * (n : ℝ)) * (φ n s) ^ 2 =
        -(4 * α * Real.sinh (θ / 2)) *
          ∑ n ∈ Finset.range (Nmax + 1), (n : ℝ) * Real.exp (θ * (n : ℝ)) * (φ n s) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _; ring
    rw [hfirst]
    linarith
  have hH_deriv : ∀ s ≥ 0, HasDerivAt H (H' s) s := by
    intro s hs
    have hGs : 0 < G s := lt_of_lt_of_le zero_lt_one (hG_ge_one s hs)
    have hd1 := (hG_deriv s hs).log hGs.ne'
    have hd2 := ((hasDerivAt_charTheta hα hθ₀ hs).sub_const θ₀).const_mul (1 / 2 + γ / α)
    exact hd1.fun_add hd2
  have hH'_nonpos : ∀ s ≥ 0, H' s ≤ 0 := by
    intro s hs
    have hGs : 0 < G s := lt_of_lt_of_le zero_lt_one (hG_ge_one s hs)
    have hineq := hdiff_ineq s hs
    have hdiv : G' s / G s ≤ 2 * (α + 2 * γ) * Real.sinh (charTheta α θ₀ s / 2) := by
      rwa [div_le_iff₀ hGs]
    have hcancel :
        2 * (α + 2 * γ) * Real.sinh (charTheta α θ₀ s / 2) +
          (1 / 2 + γ / α) * (-4 * α * Real.sinh (charTheta α θ₀ s / 2)) = 0 := by
      field_simp [hα.ne']
      ring
    simp only [H']; linarith
  have hH0 : H 0 = 0 := by
    have hG0 : G 0 = 1 := by
      simp only [G, finiteMGF, charTheta_zero hθ₀]
      rw [Finset.sum_range_succ']
      have h0 : φ 0 0 = 1 := by simpa using hinit 0 (Nat.zero_le Nmax)
      have hrest : ∀ k ∈ Finset.range Nmax,
          Real.exp (θ₀ * ((k + 1 : ℕ) : ℝ)) * (φ (k + 1) 0) ^ 2 = 0 := by
        intro k hk
        rw [hinit (k + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hk))]
        simp
      rw [Finset.sum_eq_zero hrest, h0]
      simp
    simp only [H, hG0, Real.log_one, charTheta_zero hθ₀, sub_self, mul_zero, add_zero]
  have hHt : H t ≤ 0 := by
    rcases eq_or_lt_of_le ht with rfl | htpos
    · linarith [hH0]
    obtain ⟨c, ⟨hc0, _⟩, hslope⟩ := exists_hasDerivAt_eq_slope H H' htpos
      (fun s hs ↦ (hH_deriv s hs.1).continuousAt.continuousWithinAt)
      (fun s hs ↦ hH_deriv s hs.1.le)
    rw [hH0, sub_zero, sub_zero] at hslope
    have hmul : H t = t * H' c := by
      have := (eq_div_iff htpos.ne').mp hslope
      linarith
    have hc_le := hH'_nonpos c hc0.le
    nlinarith
  have hlog_le : Real.log (G t) ≤ (1 / 2 + γ / α) * (θ₀ - charTheta α θ₀ t) := by
    simp only [H] at hHt
    linarith
  have hGt_pos : 0 < G t := lt_of_lt_of_le zero_lt_one (hG_ge_one t ht)
  refine ⟨?_, ?_⟩
  · calc G t = Real.exp (Real.log (G t)) := (Real.exp_log hGt_pos).symm
      _ ≤ Real.exp ((1 / 2 + γ / α) * (θ₀ - charTheta α θ₀ t)) := Real.exp_le_exp.mpr hlog_le
  · apply Real.exp_le_exp.mpr
    have hθpos := charTheta_pos hα hθ₀ ht
    have hcoeff : 0 < 1 / 2 + γ / α := by positivity
    nlinarith

/-- Lower bound on the characteristic curve: `θ(t) ≥ 4 tanh(θ₀/4) e^{-2αt}`. -/
theorem charTheta_ge_four_tanh {α θ₀ t : ℝ} (hα : 0 < α) (hθ₀ : 0 < θ₀) (ht : 0 ≤ t) :
    4 * Real.tanh (θ₀ / 4) * Real.exp (-2 * α * t) ≤ charTheta α θ₀ t := by
  have hθ_nn : 0 ≤ charTheta α θ₀ t / 4 := (div_pos (charTheta_pos hα hθ₀ ht) (by norm_num)).le
  have h := tanh_le_self_nonneg hθ_nn
  rw [tanh_charTheta_div_four hα hθ₀ ht] at h
  unfold charU at h
  linarith

/-- **Theorem 1.1(a)** (Finite-Chain Exponential Tail Bound, Eq. 1.12). -/
theorem theorem_1_1a_finite_tail {Nmax : ℕ} {α γ θ₀ : ℝ}
    (b : ℕ → ℝ) (φ : ℕ → ℝ → ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (hb0 : b 0 = 0) (hbN : b (Nmax + 1) = 0)
    (hb_nn : ∀ n, 1 ≤ n → n ≤ Nmax → 0 ≤ b n)
    (hb_lin : ∀ n, 1 ≤ n → n ≤ Nmax → b n ≤ α * (n : ℝ) + γ)
    (hode : ∀ n ≤ Nmax, ∀ t, HasDerivAt (φ n) (b n * φ (n - 1) t - b (n + 1) * φ (n + 1) t) t)
    (hinit : ∀ n ≤ Nmax, φ n 0 = if n = 0 then 1 else 0)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ m ∈ (Finset.range (Nmax + 1)).filter (fun m ↦ n ≤ m), (φ m t) ^ 2) ≤
      Real.exp ((1 / 2 + γ / α) * θ₀) *
        Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t)) := by
  have hmgf := lemma_3_1_finite_chain_mgf b φ hα hγ hθ₀ hb0 hbN hb_nn hb_lin hode hinit t ht
  have hG : finiteMGF Nmax φ (charTheta α θ₀ t) t ≤ Real.exp ((1 / 2 + γ / α) * θ₀) :=
    le_trans hmgf.1 hmgf.2
  have hθ_pos := charTheta_pos hα hθ₀ ht
  have hmarkov :
      Real.exp (charTheta α θ₀ t * (n : ℝ)) *
        (∑ m ∈ (Finset.range (Nmax + 1)).filter (fun m ↦ n ≤ m), (φ m t) ^ 2) ≤
      finiteMGF Nmax φ (charTheta α θ₀ t) t := by
    rw [Finset.mul_sum]
    calc ∑ m ∈ (Finset.range (Nmax + 1)).filter (fun m ↦ n ≤ m),
            Real.exp (charTheta α θ₀ t * (n : ℝ)) * (φ m t) ^ 2
        ≤ ∑ m ∈ (Finset.range (Nmax + 1)).filter (fun m ↦ n ≤ m),
            Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ m t) ^ 2 := by
          apply Finset.sum_le_sum
          intro m hm
          have hnm : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr (Finset.mem_filter.mp hm).2
          have hexp := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnm hθ_pos.le)
          exact mul_le_mul_of_nonneg_right hexp (sq_nonneg _)
      _ ≤ finiteMGF Nmax φ (charTheta α θ₀ t) t := by
          unfold finiteMGF
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro m _ _
          positivity
  have hdiv :
      (∑ m ∈ (Finset.range (Nmax + 1)).filter (fun m ↦ n ≤ m), (φ m t) ^ 2) ≤
        finiteMGF Nmax φ (charTheta α θ₀ t) t * Real.exp (-(charTheta α θ₀ t * (n : ℝ))) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), mul_comm]
    exact hmarkov
  have hθ_lb := charTheta_ge_four_tanh hα hθ₀ ht
  have hexp_le :
      Real.exp (-(charTheta α θ₀ t * (n : ℝ))) ≤
        Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hθ_lb (Nat.cast_nonneg n)
    linarith
  calc (∑ m ∈ (Finset.range (Nmax + 1)).filter (fun m ↦ n ≤ m), (φ m t) ^ 2)
      ≤ finiteMGF Nmax φ (charTheta α θ₀ t) t * Real.exp (-(charTheta α θ₀ t * (n : ℝ))) := hdiv
    _ ≤ Real.exp ((1 / 2 + γ / α) * θ₀) *
          Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t)) :=
        mul_le_mul hG hexp_le (Real.exp_pos _).le (Real.exp_pos _).le

/-- **Theorem 1.1(a)** (Finite-Chain Krylov Complexity Bound, Eq. 1.13). -/
theorem theorem_1_1a_finite_complexity {Nmax : ℕ} {α γ θ₀ : ℝ}
    (b : ℕ → ℝ) (φ : ℕ → ℝ → ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (hb0 : b 0 = 0) (hbN : b (Nmax + 1) = 0)
    (hb_nn : ∀ n, 1 ≤ n → n ≤ Nmax → 0 ≤ b n)
    (hb_lin : ∀ n, 1 ≤ n → n ≤ Nmax → b n ≤ α * (n : ℝ) + γ)
    (hode : ∀ n ≤ Nmax, ∀ t, HasDerivAt (φ n) (b n * φ (n - 1) t - b (n + 1) * φ (n + 1) t) t)
    (hinit : ∀ n ≤ Nmax, φ n 0 = if n = 0 then 1 else 0)
    (t : ℝ) (ht : 0 ≤ t) :
    finiteKrylovComplexity Nmax φ t ≤
      (Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))) *
        Real.exp (2 * α * t) := by
  have hmgf := lemma_3_1_finite_chain_mgf b φ hα hγ hθ₀ hb0 hbN hb_nn hb_lin hode hinit t ht
  have hG : finiteMGF Nmax φ (charTheta α θ₀ t) t ≤ Real.exp ((1 / 2 + γ / α) * θ₀) :=
    le_trans hmgf.1 hmgf.2
  have hθ_pos := charTheta_pos hα hθ₀ ht
  have hθ_lb := charTheta_ge_four_tanh hα hθ₀ ht
  have hK_le : finiteKrylovComplexity Nmax φ t ≤
      finiteMGF Nmax φ (charTheta α θ₀ t) t / (Real.exp 1 * charTheta α θ₀ t) := by
    unfold finiteKrylovComplexity finiteMGF
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro n _
    have hxn := le_exp_div_e_mul (Nat.cast_nonneg n) hθ_pos
    calc (n : ℝ) * (φ n t) ^ 2
        ≤ (Real.exp (charTheta α θ₀ t * (n : ℝ)) / (Real.exp 1 * charTheta α θ₀ t)) *
            (φ n t) ^ 2 := mul_le_mul_of_nonneg_right hxn (sq_nonneg _)
      _ = Real.exp (charTheta α θ₀ t * (n : ℝ)) * (φ n t) ^ 2 /
            (Real.exp 1 * charTheta α θ₀ t) := by ring
  have htanh_pos : 0 < Real.tanh (θ₀ / 4) := tanh_pos_of_pos (by linarith)
  have hden_pos : 0 < Real.exp 1 * (4 * Real.tanh (θ₀ / 4) * Real.exp (-2 * α * t)) := by
    positivity
  have hden_le : Real.exp 1 * (4 * Real.tanh (θ₀ / 4) * Real.exp (-2 * α * t)) ≤
      Real.exp 1 * charTheta α θ₀ t :=
    mul_le_mul_of_nonneg_left hθ_lb (Real.exp_pos 1).le
  calc finiteKrylovComplexity Nmax φ t
      ≤ finiteMGF Nmax φ (charTheta α θ₀ t) t / (Real.exp 1 * charTheta α θ₀ t) := hK_le
    _ ≤ Real.exp ((1 / 2 + γ / α) * θ₀) /
          (Real.exp 1 * (4 * Real.tanh (θ₀ / 4) * Real.exp (-2 * α * t))) :=
        div_le_div₀ (Real.exp_pos _).le hG hden_pos hden_le
    _ = (Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))) *
          Real.exp (2 * α * t) := by
        rw [show -2 * α * t = -(2 * α * t) by ring, Real.exp_neg]
        field_simp [htanh_pos.ne', (Real.exp_pos 1).ne', (Real.exp_pos (2 * α * t)).ne']

/-- **Theorem 1.1(a)** (Infinite-Chain Fatou Transfer, Eq. 3.5). -/
theorem theorem_1_1a_infinite_fatou_partial {α γ θ₀ : ℝ}
    (φ : ℕ → ℝ → ℝ) (φN : ℕ → ℕ → ℝ → ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (t : ℝ) (ht : 0 ≤ t)
    (hlim : ∀ m : ℕ, Filter.Tendsto (fun Nmax ↦ (φN Nmax m t) ^ 2)
      Filter.atTop (nhds ((φ m t) ^ 2)))
    (hbound : ∀ Nmax ≥ 1, finiteMGF Nmax (φN Nmax) (charTheta α θ₀ t) t ≤
      Real.exp ((1 / 2 + γ / α) * θ₀)) :
    ∀ M : ℕ, ∑ m ∈ Finset.range M, Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ m t) ^ 2 ≤
      Real.exp ((1 / 2 + γ / α) * θ₀) := by
  intro M
  have htend : Filter.Tendsto
      (fun Nmax ↦ ∑ m ∈ Finset.range M,
        Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φN Nmax m t) ^ 2)
      Filter.atTop
      (nhds (∑ m ∈ Finset.range M, Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ m t) ^ 2)) := by
    apply tendsto_finset_sum
    intro m _
    exact (hlim m).const_mul _
  have hev : ∀ᶠ Nmax in Filter.atTop,
      ∑ m ∈ Finset.range M, Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φN Nmax m t) ^ 2 ≤
        Real.exp ((1 / 2 + γ / α) * θ₀) := by
    filter_upwards [Filter.eventually_ge_atTop (max M 1)] with Nmax hN
    have hMle : M ≤ Nmax + 1 := by omega
    have hsub : Finset.range M ⊆ Finset.range (Nmax + 1) := Finset.range_mono hMle
    calc ∑ m ∈ Finset.range M, Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φN Nmax m t) ^ 2
        ≤ finiteMGF Nmax (φN Nmax) (charTheta α θ₀ t) t := by
          unfold finiteMGF
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro m _ _
          positivity
      _ ≤ Real.exp ((1 / 2 + γ / α) * θ₀) := hbound Nmax (by omega)
  exact le_of_tendsto htend hev

/-- Infinite-chain exponential tail bound (Eq. 1.12) and Krylov complexity bound (Eq. 1.13). -/
theorem theorem_1_1a_infinite_tail_and_complexity {α γ θ₀ : ℝ}
    (φ : ℕ → ℝ → ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀)
    (t : ℝ) (ht : 0 ≤ t)
    (hfatou : ∀ M : ℕ, ∑ m ∈ Finset.range M,
      Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ m t) ^ 2 ≤
      Real.exp ((1 / 2 + γ / α) * θ₀)) :
    (∀ n : ℕ, ∑' m : ℕ, (φ (n + m) t) ^ 2 ≤
      Real.exp ((1 / 2 + γ / α) * θ₀) *
        Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t))) ∧
    (∑' n : ℕ, (n : ℝ) * (φ n t) ^ 2 ≤
      (Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))) *
        Real.exp (2 * α * t)) := by
  have hθ_pos := charTheta_pos hα hθ₀ ht
  have hθ_lb := charTheta_ge_four_tanh hα hθ₀ ht
  have htanh_pos : 0 < Real.tanh (θ₀ / 4) := tanh_pos_of_pos (by linarith)
  have hsumm_G : Summable (fun m : ℕ ↦ Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ m t) ^ 2) :=
    summable_of_sum_range_le (fun m ↦ by positivity) hfatou
  have htsum_G : ∑' m : ℕ, Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ m t) ^ 2 ≤
      Real.exp ((1 / 2 + γ / α) * θ₀) :=
    hsumm_G.tsum_le_of_sum_range_le hfatou
  constructor
  · intro n
    have hle_term : ∀ m : ℕ,
        (φ (n + m) t) ^ 2 ≤
          Real.exp (-(charTheta α θ₀ t * (n : ℝ))) *
            (Real.exp (charTheta α θ₀ t * ((n + m : ℕ) : ℝ)) * (φ (n + m) t) ^ 2) := by
      intro m
      have hexp : 1 ≤ Real.exp (-(charTheta α θ₀ t * (n : ℝ))) *
          Real.exp (charTheta α θ₀ t * ((n + m : ℕ) : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        push_cast
        have : 0 ≤ charTheta α θ₀ t * (m : ℝ) := by positivity
        linarith
      nlinarith [sq_nonneg (φ (n + m) t)]
    have hsumm_shift : Summable (fun m : ℕ ↦
        Real.exp (charTheta α θ₀ t * ((n + m : ℕ) : ℝ)) * (φ (n + m) t) ^ 2) := by
      simpa [add_comm] using (summable_nat_add_iff n).mpr hsumm_G
    have hsumm_tail : Summable (fun m : ℕ ↦ (φ (n + m) t) ^ 2) :=
      Summable.of_nonneg_of_le (fun m ↦ sq_nonneg _) hle_term (hsumm_shift.mul_left _)
    have htsum_shift : ∑' m : ℕ,
        Real.exp (charTheta α θ₀ t * ((n + m : ℕ) : ℝ)) * (φ (n + m) t) ^ 2 ≤
        ∑' m : ℕ, Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ m t) ^ 2 := by
      have hsplit := hsumm_G.sum_add_tsum_nat_add n
      have hinit_nn : 0 ≤ ∑ m ∈ Finset.range n,
          Real.exp (charTheta α θ₀ t * (m : ℝ)) * (φ m t) ^ 2 :=
        Finset.sum_nonneg fun m _ ↦ by positivity
      have hcomm : (fun m : ℕ ↦ Real.exp (charTheta α θ₀ t * ((n + m : ℕ) : ℝ)) * (φ (n + m) t) ^ 2) =
          (fun m : ℕ ↦ Real.exp (charTheta α θ₀ t * ((m + n : ℕ) : ℝ)) * (φ (m + n) t) ^ 2) := by
        ext m; simp [add_comm]
      rw [hcomm]; linarith
    have hexp_le :
        Real.exp (-(charTheta α θ₀ t * (n : ℝ))) ≤
          Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t)) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_right hθ_lb (Nat.cast_nonneg n)
      linarith
    calc ∑' m : ℕ, (φ (n + m) t) ^ 2
        ≤ ∑' m : ℕ, Real.exp (-(charTheta α θ₀ t * (n : ℝ))) *
            (Real.exp (charTheta α θ₀ t * ((n + m : ℕ) : ℝ)) * (φ (n + m) t) ^ 2) :=
          hsumm_tail.tsum_le_tsum hle_term (hsumm_shift.mul_left _)
      _ = Real.exp (-(charTheta α θ₀ t * (n : ℝ))) *
            ∑' m : ℕ, Real.exp (charTheta α θ₀ t * ((n + m : ℕ) : ℝ)) * (φ (n + m) t) ^ 2 :=
          tsum_mul_left
      _ ≤ Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t)) *
            Real.exp ((1 / 2 + γ / α) * θ₀) :=
          mul_le_mul hexp_le (le_trans htsum_shift htsum_G)
            (tsum_nonneg fun m ↦ by positivity) (Real.exp_pos _).le
      _ = Real.exp ((1 / 2 + γ / α) * θ₀) *
            Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t)) := by ring
  · have hterm_K : ∀ n : ℕ,
        (n : ℝ) * (φ n t) ^ 2 ≤
          (1 / (Real.exp 1 * charTheta α θ₀ t)) *
            (Real.exp (charTheta α θ₀ t * (n : ℝ)) * (φ n t) ^ 2) := by
      intro n
      have hxn := le_exp_div_e_mul (Nat.cast_nonneg n) hθ_pos
      calc (n : ℝ) * (φ n t) ^ 2
          ≤ (Real.exp (charTheta α θ₀ t * (n : ℝ)) / (Real.exp 1 * charTheta α θ₀ t)) *
              (φ n t) ^ 2 := mul_le_mul_of_nonneg_right hxn (sq_nonneg _)
        _ = (1 / (Real.exp 1 * charTheta α θ₀ t)) *
              (Real.exp (charTheta α θ₀ t * (n : ℝ)) * (φ n t) ^ 2) := by ring
    have hsumm_K : Summable (fun n : ℕ ↦ (n : ℝ) * (φ n t) ^ 2) :=
      Summable.of_nonneg_of_le (fun n ↦ by positivity) hterm_K (hsumm_G.mul_left _)
    have hden_pos : 0 < Real.exp 1 * (4 * Real.tanh (θ₀ / 4) * Real.exp (-2 * α * t)) := by
      positivity
    have hden_le : Real.exp 1 * (4 * Real.tanh (θ₀ / 4) * Real.exp (-2 * α * t)) ≤
        Real.exp 1 * charTheta α θ₀ t :=
      mul_le_mul_of_nonneg_left hθ_lb (Real.exp_pos 1).le
    calc ∑' n : ℕ, (n : ℝ) * (φ n t) ^ 2
        ≤ ∑' n : ℕ, (1 / (Real.exp 1 * charTheta α θ₀ t)) *
            (Real.exp (charTheta α θ₀ t * (n : ℝ)) * (φ n t) ^ 2) :=
          hsumm_K.tsum_le_tsum hterm_K (hsumm_G.mul_left _)
      _ = (1 / (Real.exp 1 * charTheta α θ₀ t)) *
            ∑' n : ℕ, Real.exp (charTheta α θ₀ t * (n : ℝ)) * (φ n t) ^ 2 := tsum_mul_left
      _ = (∑' n : ℕ, Real.exp (charTheta α θ₀ t * (n : ℝ)) * (φ n t) ^ 2) /
            (Real.exp 1 * charTheta α θ₀ t) := by ring
      _ ≤ Real.exp ((1 / 2 + γ / α) * θ₀) /
            (Real.exp 1 * (4 * Real.tanh (θ₀ / 4) * Real.exp (-2 * α * t))) :=
          div_le_div₀ (Real.exp_pos _).le htsum_G hden_pos hden_le
      _ = (Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))) *
            Real.exp (2 * α * t) := by
          rw [show -2 * α * t = -(2 * α * t) by ring, Real.exp_neg]
          field_simp [htanh_pos.ne', (Real.exp_pos 1).ne', (Real.exp_pos (2 * α * t)).ne']

/-- Asymptotic growth rate bound from Eq. (1.13). -/
theorem theorem_1_1a_log_rate_bound {C α : ℝ} {K : ℝ → ℝ}
    (hC : 0 < C) (hKpos : ∀ t > 0, 0 < K t)
    (hK : ∀ t > 0, K t ≤ C * Real.exp (2 * α * t))
    (t : ℝ) (ht : 0 < t) :
    Real.log (K t) / t ≤ 2 * α + Real.log C / t := by
  have h1 : Real.log (K t) ≤ Real.log (C * Real.exp (2 * α * t)) :=
    Real.log_le_log (hKpos t ht) (hK t ht)
  rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
  have hdiv := div_le_div_of_nonneg_right h1 ht.le
  have hrew : (Real.log C + 2 * α * t) / t = 2 * α + Real.log C / t := by
    field_simp [ht.ne']; ring
  linarith

end KrylovChaos
