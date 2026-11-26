/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import KrylovChaos

/-!
# Verified Solution for `KrylovChaos` (`comparator` Solution)

Discharges all 25 locked headline theorems in `Challenge.lean` directly from `KrylovChaos`,
completely verified against Mathlib `v4.35.0` with zero external literature hypotheses.
-/

open ChallengeDefs Matrix

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
        Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t)) :=
  KrylovChaos.theorem_1_1a_finite_tail b φ hα hγ hθ₀ hb0 hbN hb_nn hb_lin hode hinit n t ht

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
        Real.exp (2 * α * t) :=
  KrylovChaos.theorem_1_1a_finite_complexity b φ hα hγ hθ₀ hb0 hbN hb_nn hb_lin hode hinit t ht

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
        Real.exp (2 * α * t)) :=
  KrylovChaos.theorem_1_1a_infinite_tail_and_complexity φ hα hγ hθ₀ t ht hfatou

theorem prop_4_1_krylov_filtration {E : Type*} [AddCommGroup E] [Module ℂ E]
    {N r s₀ : ℕ} (hr : 1 ≤ r)
    (V : ℕ → Submodule ℂ E) (hV_mono : Monotone V)
    (L : E →ₗ[ℂ] E) (hL : ∀ s x, x ∈ V s → L x ∈ V (min N (s + (r - 1))))
    (O : ℕ → E) (hO0 : O 0 ∈ V (min N s₀))
    (hstep : ∀ n, ∃ a b : ℂ, O (n + 1) = a • L (O n) + (if n = 0 then 0 else b • O (n - 1))) :
    ∀ n : ℕ, O n ∈ V (min N (s₀ + (r - 1) * n)) :=
  KrylovChaos.prop_4_1_krylov_filtration V hV_mono L hL O hO0 hstep

theorem theorem_1_1b_static_reduction
    {α lamL δ C₀ C₁ C₂ : ℝ} {r s₀ : ℕ}
    (hr : 1 ≤ r) (hα : 0 < α) (hlam : 0 < lamL) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hH1 : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        let tN := ((1 - ε) / lamL) * Real.log (N : ℝ)
        let MN := (1 / Real.tanh 1) * Real.exp (2 * α * tN) * Real.log (N : ℝ) + 1
        let sN := (s₀ : ℝ) + ((r : ℝ) - 1) * MN
        c * (N : ℝ) ^ (1 - ε) ≤
          C₁ * sN + C₂ * (N : ℝ) ^ δ * sN ^ (1 - δ) +
          2 * C₀ * (N : ℝ)⁻¹ + C₀ ^ 2 * (N : ℝ) ^ (-3 : ℝ)) :
    lamL ≤ 2 * α :=
  KrylovChaos.theorem_1_1b_static_reduction hr hα hlam hδ0 hδ1 hC₀ hC₁ hC₂ hH1

theorem prop_4_3_product_state_static_bound {N s : ℕ} {mmax : ℝ}
    (m : Fin N → ℝ) (hm_le : ∀ x, |m x| ≤ mmax) (hmmax : mmax < 1)
    (c : (Fin N → Fin 4) → ℂ)
    (hsupp : ∀ a, s < stringWeight a → c a = 0)
    (hnorm : ∑ a : Fin N → Fin 4, ‖c a‖ ^ 2 = 1) :
    (∑ x : Fin N, ∑ a : Fin N → Fin 4, ∑ b : Fin N → Fin 4,
      if ∀ y : Fin N, y ≠ x → a y = b y then
        (star (c a) * c b).re * singleSiteM (m x) (a x) (b x)
      else 0) ≤
    (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ)) :=
  KrylovChaos.prop_4_3_product_state_static_bound m hm_le hmmax c hsupp hnorm

theorem theorem_1_2a_laplace_identity {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (WabsSq : ι → ι → ℝ) (Z β κ' : ℝ) :
    Z⁻¹ * ∑ a : ι, ∑ b : ι,
      Real.exp (-(β / 2) * (E a + E b)) * WabsSq a b * Real.exp ((β / 2 + κ') * (E a - E b)) =
    Z⁻¹ * ∑ a : ι, ∑ b : ι,
      Real.exp (-β * E b) * Real.exp (κ' * (E a - E b)) * WabsSq a b :=
  KrylovChaos.theorem_1_2a_laplace_identity E WabsSq Z β κ'

theorem theorem_1_2a_even_exp_moment {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (w : ι → ι → ℝ) (τ : ℝ)
    (hw_nn : ∀ a b, 0 ≤ w a b) (hw_sym : ∀ a b, w a b = w b a) :
    (∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * |E a - E b|)) ≤
    2 * (∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * (E a - E b))) :=
  KrylovChaos.theorem_1_2a_even_exp_moment E w τ hw_nn hw_sym

theorem theorem_1_2b_lanczos_rate_bound {N₀ : ℕ} {W₀ α₁ rW : ℝ}
    (μ : ℕ → ℝ) (hW₀ : 0 < W₀) (hα₁ : 0 < α₁) (hrW : 0 < rW)
    (hlower : ∀ n > N₀,
      (2 * W₀ / Real.pi) * ((2 * n - 2 * N₀).factorial : ℝ) *
        (2 * α₁ / Real.pi) ^ (2 * n - 2 * N₀) ≤ μ n)
    (hupper : ∀ δ > 0, ∀ᶠ n : ℕ in Filter.atTop,
      (μ n / ((2 * n).factorial : ℝ)) ^ ((1 : ℝ) / (2 * (n : ℝ))) ≤ 1 / rW + δ) :
    2 * α₁ ≤ Real.pi / rW :=
  KrylovChaos.theorem_1_2b_lanczos_rate_bound μ hW₀ hα₁ hrW hlower hupper

theorem theorem_1_2b_rate_chain {α β κ rW : ℝ}
    (hβ : 0 < β) (hκ : 0 < κ) (hrW : β / 2 + κ ≤ rW)
    (hbound : 2 * α ≤ Real.pi / rW) :
    2 * α ≤ 2 * Real.pi / (β + 2 * κ) ∧ 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β :=
  KrylovChaos.theorem_1_2b_rate_chain hβ hκ hrW hbound

theorem theorem_1_2c_otoc_dominance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B V : Matrix ι ι ℂ) (hV : Vᴴ = V) (vNormSq : ℝ)
    (hV_bound : ∀ x : ι → ℂ,
      (∑ i : ι, ∑ j : ι, star (x i) * (V * V) i j * x j).re ≤
        vNormSq * ∑ i : ι, ‖x i‖ ^ 2) :
    ‖Matrix.trace ((B * V) * (B * V))‖ ≤ (Matrix.trace (Bᴴ * B * (V * V))).re ∧
    (Matrix.trace (Bᴴ * B * (V * V))).re ≤ vNormSq * hsNormSq B :=
  KrylovChaos.theorem_1_2c_otoc_dominance B V hV vNormSq hV_bound

theorem prop_6_4_decoupling_combine {Sβ I II III Bavg C₂ cB N : ℝ}
    (hI : 0 ≤ I) (hN : 0 ≤ N) (hcB : 0 ≤ cB)
    (hdecomp : Sβ = I + II + III)
    (hIII : |III| ≤ C₂ * Real.sqrt N)
    (hII : |II| ≤ 2 * Real.sqrt I * Real.sqrt (Bavg + III))
    (hB : Bavg + |III| ≤ cB * N) :
    Sβ ≤ I + (2 * Real.sqrt cB) * Real.sqrt (N * I) + C₂ * Real.sqrt N :=
  KrylovChaos.prop_6_4_decoupling_combine hI hN hcB hdecomp hIII hII hB

theorem theorem_1_3a_reverse_poincare {N : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s)
    (sxSq projProdSq filtBetaSq : ι → Fin N → ℝ)
    (qTilde : ℝ)
    (hlower : qTilde ≤ ∑ x : Fin N, ∑ s : ι, w s * sxSq s x)
    (hcond : ∀ s x, sxSq s x ≤ 9 * projProdSq s x)
    (hfilt : ∀ s, (∑ x : Fin N, projProdSq s x) ≤ ∑ k : Fin N, filtBetaSq s k) :
    qTilde ≤ (∑ x : Fin N, ∑ s : ι, w s * sxSq s x) ∧
    (∑ x : Fin N, ∑ s : ι, w s * sxSq s x) ≤
      9 * (∑ k : Fin N, ∑ s : ι, w s * filtBetaSq s k) :=
  KrylovChaos.theorem_1_3a_reverse_poincare w hw sxSq projProdSq filtBetaSq qTilde hlower hcond hfilt

theorem theorem_1_3b_constants {r : ℕ} {β Jsite : ℝ}
    (hr : 2 ≤ r) (hJ : 0 < Jsite) (hβ0 : 0 ≤ β) (hβ : β ≤ betaWC r Jsite) :
    (3 / 2 : ℝ) * (1 - β / (4 * invLocalityScale r Jsite))⁻¹ ^ 2 * 9 < 54 ∧
    2 * β * (3 : ℝ) ^ (r - 1) * Real.exp 1 * (r : ℝ) * Jsite ≤ 1 / 2 ∧
    (3 / 8 : ℝ) * (24 : ℝ) ^ 2 = 216 := by
  simpa only [ChallengeDefs.invLocalityScale, KrylovChaos.invLocalityScale] using
    KrylovChaos.theorem_1_3b_constants hr hJ hβ0
      (by simpa only [ChallengeDefs.betaWC, KrylovChaos.betaWC] using hβ)

theorem theorem_1_3c_mss_lyapunov_bound {α lamL A B C : ℝ}
    (hα : 0 < α) (hlam : 0 < lamL) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hH : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        c * (N : ℝ) ^ (1 - ε) ≤
          A * (N : ℝ) ^ ((2 * α / lamL) * (1 - ε)) +
          B * Real.sqrt ((N : ℝ) * (N : ℝ) ^ ((2 * α / lamL) * (1 - ε))) +
          C * Real.sqrt (N : ℝ)) :
    lamL ≤ 2 * α :=
  KrylovChaos.theorem_1_3c_mss_lyapunov_bound hα hlam hA hB hC hH

theorem lemma_8_2_hubbard_stratonovich_identity {u s z₁ z₂ : ℝ} (hu : 0 ≤ u)
    (hs : s = 1 ∨ s = -1) (hz₁ : z₁ = 1 ∨ z₁ = -1) (hz₂ : z₂ = 1 ∨ z₂ = -1) :
    Real.exp (u * (s * z₁ * z₂)) =
    Real.exp (-u) * (1 / 2 : ℝ) *
      (Real.exp (hsPhi u * (z₁ + s * z₂)) + Real.exp (-(hsPhi u * (z₁ + s * z₂)))) :=
  KrylovChaos.lemma_8_2_hubbard_stratonovich_identity hu hs hz₁ hz₂

theorem prop_8_3_product_bernoulli_reverse_poincare {N : ℕ} {Φmax : ℝ}
    (h : Fin N → ℝ) (hh : ∀ i, |h i| ≤ Φmax)
    (fhat : Finset (Fin N) → ℝ) :
    (∑ i : Fin N, (1 - (Real.tanh (h i)) ^ 2)⁻¹ *
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S), (fhat S) ^ 2) ≤
    (Real.cosh Φmax) ^ 2 *
      ∑ k ∈ Finset.range N,
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card), (fhat S) ^ 2 :=
  KrylovChaos.prop_8_3_product_bernoulli_reverse_poincare h hh fhat

theorem prop_9_1_no_linear_lower_bound {C' σ : ℝ} (b : ℕ → ℝ)
    (hC' : 0 < C') (hσ : 0 < σ) (hb_pos : ∀ (k : ℕ), 1 ≤ k → 0 < b k)
    (hprod : ∀ (n : ℕ), 1 ≤ n → ∏ k ∈ Finset.Icc 1 n, (b k) ^ 2 ≤
      C' * ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n) :
    ¬ (∃ α > 0, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ (k : ℕ), N₀ ≤ k → α * (k : ℝ) ≤ b k) :=
  KrylovChaos.prop_9_1_no_linear_lower_bound b hC' hσ hb_pos hprod

theorem lemma_B_1_neumann_tail_sum {d : ℕ} {EB : ℝ} (hd : 1 ≤ d) (hEB : 2 < EB) :
    Real.sqrt 2 * (∑' m : ℕ, (2 : ℝ) ^ (d - 1 + m) / EB ^ (d - 1 + m + 1)) =
    (Real.sqrt 2 / (EB - 2)) * (2 / EB) ^ (d - 1) :=
  KrylovChaos.lemma_B_1_neumann_tail_sum hd hEB

theorem carleman_deficiency_zero {s : ℝ} (hs : s ≠ 0)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hb_pos : ∀ n ≥ 1, 0 < b n)
    (hcarl : ¬ Summable (fun n : ℕ ↦ 1 / b (n + 1)))
    (u : ℕ → ℂ) (hu_l2 : Summable (fun n : ℕ ↦ ‖u n‖ ^ 2))
    (heig : ∀ n : ℕ, (b n : ℂ) * u (n - 1) + (b (n + 1) : ℂ) * u (n + 1) =
      (s : ℂ) * Complex.I * u n) :
    ∀ n : ℕ, u n = 0 :=
  KrylovChaos.carleman_deficiency_zero hs b hb0 hb_pos hcarl u hu_l2 heig

theorem kotecky_preiss_convergence {Γ : Type*} [DecidableEq Γ]
    (incompat : Γ → Γ → Prop) [DecidableRel incompat]
    (hrefl : ∀ γ, incompat γ γ)
    (hsym : ∀ γ₁ γ₂, incompat γ₁ γ₂ → incompat γ₂ γ₁)
    (w : Γ → ℂ) (a : Γ → ℝ) (Λ₀ : Finset Γ)
    (hkp : ∀ γ ∈ Λ₀,
      ∑ γ' ∈ Λ₀.filter (fun γ' ↦ incompat γ γ'), kpActivity w a γ' ≤ a γ) :
    ∀ Λ ⊆ Λ₀,
      polymerZ incompat w Λ ≠ 0 ∧
      ∀ γ ∈ Λ,
        ‖polymerZ incompat w Λ / polymerZ incompat w (Λ.erase γ) - 1‖ ≤
          kpActivity w a γ / (1 + kpActivity w a γ) ∧
        ‖polymerZ incompat w (Λ.erase γ) / polymerZ incompat w Λ‖ ≤
          1 + kpActivity w a γ :=
  KrylovChaos.kotecky_preiss_convergence incompat hrefl hsym w a Λ₀ hkp

theorem vitali_power_series_convergence {z₀ : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (c : ℕ → ℕ → ℂ) (cLim : ℕ → ℂ)
    (hbound : ∀ N k, ‖c N k‖ ≤ M / R ^ k)
    (hlim : ∀ k, Filter.Tendsto (fun N ↦ c N k) Filter.atTop (nhds (cLim k))) :
    (∀ k, ‖cLim k‖ ≤ M / R ^ k) ∧
    (∀ z ∈ Metric.ball z₀ R, Summable (fun k : ℕ ↦ cLim k * (z - z₀) ^ k)) ∧
    (∀ r : ℝ, 0 ≤ r → r < R → ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ z ∈ Metric.closedBall z₀ r,
        ‖(∑' k : ℕ, c N k * (z - z₀) ^ k) - (∑' k : ℕ, cLim k * (z - z₀) ^ k)‖ < ε) :=
  KrylovChaos.vitali_power_series_convergence hR hM c cLim hbound hlim

theorem araki_1d_entire_expansional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (a : ℕ → E) (ha : ∀ m : ℕ, ‖a m‖ ≤ C₀ * C₁ ^ m) (τ : ℂ) :
    Summable (fun m : ℕ ↦ (τ ^ m / (m.factorial : ℂ)) • a m) ∧
    ‖∑' m : ℕ, (τ ^ m / (m.factorial : ℂ)) • a m‖ ≤ C₀ * Real.exp (C₁ * ‖τ‖) :=
  KrylovChaos.araki_1d_entire_expansional hC₀ hC₁ a ha τ
