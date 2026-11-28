/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import ChallengeDefs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Locked Headline Theorem Statements for `KrylovChaos` (`comparator` Challenge)

Contains the 33 locked headline theorem signatures corresponding to
*Finite-Temperature Bounds on Operator Growth and Quantum Chaos* (Prince Anand, 2026),
covering the infinite-chain Theorem 1.1(a), concrete `QubitOp N` and `Measure ℝ`
Theorems 1.2(a)–(c), concrete high-temperature Theorem 1.3(a) Eq. (1.20),
1D all-temperature Proposition 8.1, active-edge Classical Ising Proposition 8.3 Eq. (8.4),
`D × D` double-well Lemma B.1 and Proposition 9.1(3) Eq. (9.3), and the 4 ground-up
literature theorems (Carleman, Kotecký–Preiss, Vitali/Montel, Araki 1D).
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
        Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t)) := by
  sorry

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
  sorry

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
  sorry

theorem theorem_1_1a_infinite_chain_complete (b : ℕ → ℝ) {α γ : ℝ}
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (hb0 : b 0 = 0)
    (hb_nn : ∀ n, 1 ≤ n → 0 ≤ b n)
    (hb_lin : ∀ n, 1 ≤ n → b n ≤ α * (n : ℝ) + γ) :
    ∃ φ : ℕ → ℝ → ℝ,
      ((∀ m, φ m 0 = if m = 0 then 1 else 0) ∧
       (∀ m, Continuous (φ m)) ∧
       (∀ m t, HasDerivAt (φ m) (b m * φ (m - 1) t - b (m + 1) * φ (m + 1) t) t) ∧
       (∀ t : ℝ, Summable (fun m : ℕ ↦ (φ m t) ^ 2) ∧ ∑' m : ℕ, (φ m t) ^ 2 = 1)) ∧
      (∀ (ψ : ℕ → ℝ → ℝ) (T C : ℝ), 0 ≤ T → 0 ≤ C →
        (∀ m s, HasDerivAt (ψ m) (b m * ψ (m - 1) s - b (m + 1) * ψ (m + 1) s) s) →
        (∀ m, ψ m 0 = if m = 0 then 1 else 0) →
        (∀ s ∈ Set.Icc 0 T, Summable (fun m ↦ (ψ m s) ^ 2) ∧ ∑' m, (ψ m s) ^ 2 ≤ C) →
        ∀ t ∈ Set.Icc 0 T, ∀ m : ℕ, ψ m t = φ m t) ∧
      (∀ θ₀ : ℝ, 0 < θ₀ → ∀ t ≥ 0,
        (∀ n : ℕ, ∑' m : ℕ, (φ (n + m) t) ^ 2 ≤
          Real.exp ((1 / 2 + γ / α) * θ₀) *
            Real.exp (-4 * Real.tanh (θ₀ / 4) * (n : ℝ) * Real.exp (-2 * α * t))) ∧
        (∑' m : ℕ, (m : ℝ) * (φ m t) ^ 2 ≤
          (Real.exp ((1 / 2 + γ / α) * θ₀) / (4 * Real.exp 1 * Real.tanh (θ₀ / 4))) *
            Real.exp (2 * α * t))) ∧
      Filter.limsup (fun t : ℝ ↦ Real.log (∑' m : ℕ, (m : ℝ) * (φ m t) ^ 2) / t) Filter.atTop ≤ 2 * α := by
  sorry

theorem prop_4_1_krylov_filtration {E : Type*} [AddCommGroup E] [Module ℂ E]
    {N r s₀ : ℕ} (hr : 1 ≤ r)
    (V : ℕ → Submodule ℂ E) (hV_mono : Monotone V)
    (L : E →ₗ[ℂ] E) (hL : ∀ s x, x ∈ V s → L x ∈ V (min N (s + (r - 1))))
    (O : ℕ → E) (hO0 : O 0 ∈ V (min N s₀))
    (hstep : ∀ n, ∃ a b : ℂ, O (n + 1) = a • L (O n) + (if n = 0 then 0 else b • O (n - 1))) :
    ∀ n : ℕ, O n ∈ V (min N (s₀ + (r - 1) * n)) := by
  sorry

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
    lamL ≤ 2 * α := by
  sorry

theorem prop_4_3_product_state_static_bound {N s : ℕ} {mmax : ℝ}
    (m : Fin N → ℝ) (hm_le : ∀ x, |m x| ≤ mmax) (hmmax : mmax < 1)
    (c : (Fin N → Fin 4) → ℂ)
    (hsupp : ∀ a, s < stringWeight a → c a = 0)
    (hnorm : ∑ a : Fin N → Fin 4, ‖c a‖ ^ 2 = 1) :
    (∑ x : Fin N, ∑ a : Fin N → Fin 4, ∑ b : Fin N → Fin 4,
      if ∀ y : Fin N, y ≠ x → a y = b y then
        (star (c a) * c b).re * singleSiteM (m x) (a x) (b x)
      else 0) ≤
    (s : ℝ) + mmax * Real.sqrt ((N : ℝ) * (s : ℝ)) := by
  sorry

theorem theorem_1_2a_laplace_identity {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (WabsSq : ι → ι → ℝ) (Z β κ' : ℝ) :
    Z⁻¹ * ∑ a : ι, ∑ b : ι,
      Real.exp (-(β / 2) * (E a + E b)) * WabsSq a b * Real.exp ((β / 2 + κ') * (E a - E b)) =
    Z⁻¹ * ∑ a : ι, ∑ b : ι,
      Real.exp (-β * E b) * Real.exp (κ' * (E a - E b)) * WabsSq a b := by
  sorry

theorem theorem_1_2a_even_exp_moment {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (w : ι → ι → ℝ) (τ : ℝ)
    (hw_nn : ∀ a b, 0 ≤ w a b) (hw_sym : ∀ a b, w a b = w b a) :
    (∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * |E a - E b|)) ≤
    2 * (∑ a : ι, ∑ b : ι, w a b * Real.exp (τ * (E a - E b))) := by
  sorry

theorem theorem_1_2b_lanczos_rate_bound {N₀ : ℕ} {W₀ α₁ rW : ℝ}
    (μ : ℕ → ℝ) (hW₀ : 0 < W₀) (hα₁ : 0 < α₁) (hrW : 0 < rW)
    (hlower : ∀ n > N₀,
      (2 * W₀ / Real.pi) * ((2 * n - 2 * N₀).factorial : ℝ) *
        (2 * α₁ / Real.pi) ^ (2 * n - 2 * N₀) ≤ μ n)
    (hupper : ∀ δ > 0, ∀ᶠ n : ℕ in Filter.atTop,
      (μ n / ((2 * n).factorial : ℝ)) ^ ((1 : ℝ) / (2 * (n : ℝ))) ≤ 1 / rW + δ) :
    2 * α₁ ≤ Real.pi / rW := by
  sorry

theorem theorem_1_2b_rate_chain {α β κ rW : ℝ}
    (hβ : 0 < β) (hκ : 0 < κ) (hrW : β / 2 + κ ≤ rW)
    (hbound : 2 * α ≤ Real.pi / rW) :
    2 * α ≤ 2 * Real.pi / (β + 2 * κ) ∧ 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β := by
  sorry

theorem theorem_1_2c_otoc_dominance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B V : Matrix ι ι ℂ) (hV : Vᴴ = V) (vNormSq : ℝ)
    (hV_bound : ∀ x : ι → ℂ,
      (∑ i : ι, ∑ j : ι, star (x i) * (V * V) i j * x j).re ≤
        vNormSq * ∑ i : ι, ‖x i‖ ^ 2) :
    ‖Matrix.trace ((B * V) * (B * V))‖ ≤ (Matrix.trace (Bᴴ * B * (V * V))).re ∧
    (Matrix.trace (Bᴴ * B * (V * V))).re ≤ vNormSq * hsNormSq B := by
  sorry

theorem prop_6_4_decoupling_combine {Sβ I II III Bavg C₂ cB N : ℝ}
    (hI : 0 ≤ I) (hN : 0 ≤ N) (hcB : 0 ≤ cB)
    (hdecomp : Sβ = I + II + III)
    (hIII : |III| ≤ C₂ * Real.sqrt N)
    (hII : |II| ≤ 2 * Real.sqrt I * Real.sqrt (Bavg + III))
    (hB : Bavg + |III| ≤ cB * N) :
    Sβ ≤ I + (2 * Real.sqrt cB) * Real.sqrt (N * I) + C₂ * Real.sqrt N := by
  sorry

theorem theorem_1_3a_reverse_poincare {N : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ s, 0 ≤ w s)
    (sxSq projProdSq filtBetaSq : ι → Fin N → ℝ)
    (qTilde : ℝ)
    (hlower : qTilde ≤ ∑ x : Fin N, ∑ s : ι, w s * sxSq s x)
    (hcond : ∀ s x, sxSq s x ≤ 9 * projProdSq s x)
    (hfilt : ∀ s, (∑ x : Fin N, projProdSq s x) ≤ ∑ k : Fin N, filtBetaSq s k) :
    qTilde ≤ (∑ x : Fin N, ∑ s : ι, w s * sxSq s x) ∧
    (∑ x : Fin N, ∑ s : ι, w s * sxSq s x) ≤
      9 * (∑ k : Fin N, ∑ s : ι, w s * filtBetaSq s k) := by
  sorry

theorem theorem_1_3b_constants {r : ℕ} {β Jsite : ℝ}
    (hr : 2 ≤ r) (hJ : 0 < Jsite) (hβ0 : 0 ≤ β) (hβ : β ≤ betaWC r Jsite) :
    (3 / 2 : ℝ) * (1 - β / (4 * invLocalityScale r Jsite))⁻¹ ^ 2 * 9 < 54 ∧
    2 * β * (3 : ℝ) ^ (r - 1) * Real.exp 1 * (r : ℝ) * Jsite ≤ 1 / 2 ∧
    (3 / 8 : ℝ) * (24 : ℝ) ^ 2 = 216 := by
  sorry

theorem theorem_1_3c_mss_lyapunov_bound {α lamL A B C : ℝ}
    (hα : 0 < α) (hlam : 0 < lamL) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hH : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        c * (N : ℝ) ^ (1 - ε) ≤
          A * (N : ℝ) ^ ((2 * α / lamL) * (1 - ε)) +
          B * Real.sqrt ((N : ℝ) * (N : ℝ) ^ ((2 * α / lamL) * (1 - ε))) +
          C * Real.sqrt (N : ℝ)) :
    lamL ≤ 2 * α := by
  sorry

theorem lemma_8_2_hubbard_stratonovich_identity {u s z₁ z₂ : ℝ} (hu : 0 ≤ u)
    (hs : s = 1 ∨ s = -1) (hz₁ : z₁ = 1 ∨ z₁ = -1) (hz₂ : z₂ = 1 ∨ z₂ = -1) :
    Real.exp (u * (s * z₁ * z₂)) =
    Real.exp (-u) * (1 / 2 : ℝ) *
      (Real.exp (hsPhi u * (z₁ + s * z₂)) + Real.exp (-(hsPhi u * (z₁ + s * z₂)))) := by
  sorry

theorem prop_8_3_product_bernoulli_reverse_poincare {N : ℕ} {Φmax : ℝ}
    (h : Fin N → ℝ) (hh : ∀ i, |h i| ≤ Φmax)
    (fhat : Finset (Fin N) → ℝ) :
    (∑ i : Fin N, (1 - (Real.tanh (h i)) ^ 2)⁻¹ *
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ i ∈ S), (fhat S) ^ 2) ≤
    (Real.cosh Φmax) ^ 2 *
      ∑ k ∈ Finset.range N,
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin N) ↦ k < S.card), (fhat S) ^ 2 := by
  sorry

theorem prop_9_1_no_linear_lower_bound {C' σ : ℝ} (b : ℕ → ℝ)
    (hC' : 0 < C') (hσ : 0 < σ) (hb_pos : ∀ (k : ℕ), 1 ≤ k → 0 < b k)
    (hprod : ∀ (n : ℕ), 1 ≤ n → ∏ k ∈ Finset.Icc 1 n, (b k) ^ 2 ≤
      C' * ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n) :
    ¬ (∃ α > 0, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ (k : ℕ), N₀ ≤ k → α * (k : ℝ) ≤ b k) := by
  sorry

theorem lemma_B_1_neumann_tail_sum {d : ℕ} {EB : ℝ} (hd : 1 ≤ d) (hEB : 2 < EB) :
    Real.sqrt 2 * (∑' m : ℕ, (2 : ℝ) ^ (d - 1 + m) / EB ^ (d - 1 + m + 1)) =
    (Real.sqrt 2 / (EB - 2)) * (2 / EB) ^ (d - 1) := by
  sorry

theorem lemma_B_1_bulk_eigenvalues_in_band {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    let hL := doubleWellTridiag_isHermitian D E_B
    (∀ k : Fin D, hL.eigenvalues k ≤ E_B + 2) ∧
    (Finset.univ.filter (fun k : Fin D ↦ hL.eigenvalues k < E_B - 2)).card ≤ 2 ∧
    D - 2 ≤ (Finset.univ.filter (fun k : Fin D ↦ E_B - 2 ≤ hL.eigenvalues k ∧
      hL.eigenvalues k ≤ E_B + 2)).card := by
  sorry

theorem carleman_deficiency_zero {s : ℝ} (hs : s ≠ 0)
    (b : ℕ → ℝ) (hb0 : b 0 = 0) (hb_pos : ∀ n ≥ 1, 0 < b n)
    (hcarl : ¬ Summable (fun n : ℕ ↦ 1 / b (n + 1)))
    (u : ℕ → ℂ) (hu_l2 : Summable (fun n : ℕ ↦ ‖u n‖ ^ 2))
    (heig : ∀ n : ℕ, (b n : ℂ) * u (n - 1) + (b (n + 1) : ℂ) * u (n + 1) =
      (s : ℂ) * Complex.I * u n) :
    ∀ n : ℕ, u n = 0 := by
  sorry

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
          1 + kpActivity w a γ := by
  sorry

theorem vitali_power_series_convergence {z₀ : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (c : ℕ → ℕ → ℂ) (cLim : ℕ → ℂ)
    (hbound : ∀ N k, ‖c N k‖ ≤ M / R ^ k)
    (hlim : ∀ k, Filter.Tendsto (fun N ↦ c N k) Filter.atTop (nhds (cLim k))) :
    (∀ k, ‖cLim k‖ ≤ M / R ^ k) ∧
    (∀ z ∈ Metric.ball z₀ R, Summable (fun k : ℕ ↦ cLim k * (z - z₀) ^ k)) ∧
    (∀ r : ℝ, 0 ≤ r → r < R → ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ z ∈ Metric.closedBall z₀ r,
        ‖(∑' k : ℕ, c N k * (z - z₀) ^ k) - (∑' k : ℕ, cLim k * (z - z₀) ^ k)‖ < ε) := by
  sorry

theorem araki_1d_entire_expansional {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (a : ℕ → E) (ha : ∀ m : ℕ, ‖a m‖ ≤ C₀ * C₁ ^ m) (τ : ℂ) :
    Summable (fun m : ℕ ↦ (τ ^ m / (m.factorial : ℂ)) • a m) ∧
    ‖∑' m : ℕ, (τ ^ m / (m.factorial : ℂ)) • a m‖ ≤ C₀ * Real.exp (C₁ * ‖τ‖) := by
  sorry

theorem theorem_1_2a_concrete_family_holoStrip {r sW : ℕ} (hr : 2 ≤ r)
    {Jsite β C_W : ℝ} (hJ : 0 < Jsite) (hβ : 0 ≤ β) (hCW : 0 ≤ C_W)
    (E : (N : ℕ) → Finset (Finset (Fin N)))
    (hcard : ∀ N, ∀ X ∈ E N, X.card ≤ r)
    (h : (N : ℕ) → Finset (Fin N) → QubitOp N)
    (hsupp : ∀ N X, h N X ∈ supportedOn X)
    (hH : ∀ N, (∑ X ∈ E N, h N X).IsHermitian)
    (hsite : ∀ N, ∀ x : Fin N, ∑ X ∈ (E N).filter (fun X ↦ x ∈ X), opNorm (h N X) ≤ Jsite)
    (U₀ : (N : ℕ) → Finset (Fin N)) (hU₀ : ∀ N, (U₀ N).card ≤ sW)
    (W : (N : ℕ) → QubitOp N) (hWherm : ∀ N, (W N).IsHermitian)
    (hW : ∀ N, W N ∈ supportedOn (U₀ N)) (hW_norm : ∀ N, opNorm (W N) ≤ C_W)
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ]
    (hweak : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Filter.Tendsto (fun N ↦ ∫ ω, f ω ∂(concreteWightmanSpectralMeasure (hH N) β (W N)))
        Filter.atTop (nhds (∫ ω, f ω ∂μ))) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    (∀ κ' : ℝ, 0 ≤ κ' → κ' < κ →
      MeasureTheory.Integrable (fun ω : ℝ ↦ Real.cosh ((β / 2 + κ') * ω)) μ ∧
      ∫ ω : ℝ, Real.cosh ((β / 2 + κ') * ω) ∂μ ≤
        2 * C_W ^ 2 * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ)))) ∧
    ((β / 2 + κ : ℝ) : EReal) ≤ holoStripHalfWidth μ := by
  sorry

theorem theorem_1_2b_from_holoStripHalfWidth_ereal (μ : MeasureTheory.Measure ℝ) (b : ℕ → ℝ)
    {β κ : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hrW_lb : ((β / 2 + κ : ℝ) : EReal) ≤ holoStripHalfWidth μ)
    (hr₀ : ∃ r₀ : ℝ, 0 < r₀ ∧ MeasureTheory.Integrable (fun ω : ℝ ↦ Real.cosh (r₀ * ω)) μ)
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hmom_eq : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ) :
    let L : ℝ := 2 * Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop
    ((L : EReal) ≤ piDivEReal (holoStripHalfWidth μ)) ∧
    (piDivEReal (holoStripHalfWidth μ) ≤ ((2 * Real.pi / (β + 2 * κ) : ℝ) : EReal)) ∧
    (((2 * Real.pi / (β + 2 * κ) : ℝ) : EReal) < ((2 * Real.pi / β : ℝ) : EReal)) := by
  sorry

theorem theorem_1_2b_from_holoStripHalfWidth_finite (μ : MeasureTheory.Measure ℝ) (b : ℕ → ℝ)
    {β κ r_W : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (hrW_eq : holoStripHalfWidth μ = (r_W : EReal))
    (hrW_lb : β / 2 + κ ≤ r_W)
    (hr₀ : ∃ r₀ : ℝ, 0 < r₀ ∧ MeasureTheory.Integrable (fun ω : ℝ ↦ Real.cosh (r₀ * ω)) μ)
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hmom_eq : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ) :
    2 * Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ Real.pi / r_W ∧
    Real.pi / r_W ≤ 2 * Real.pi / (β + 2 * κ) ∧
    2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β := by
  sorry

theorem theorem_1_2c_thermo_limit_otoc_strip_three_way {r sW sV : ℕ} (hr : 2 ≤ r)
    {Jsite β C_W C_V : ℝ} (hJ : 0 < Jsite) (hβ : 0 ≤ β) (hCW : 0 ≤ C_W) (hCV : 0 ≤ C_V)
    (E : (N : ℕ) → Finset (Finset (Fin N)))
    (hcard : ∀ N, ∀ X ∈ E N, X.card ≤ r)
    (h : (N : ℕ) → Finset (Fin N) → QubitOp N)
    (hsupp : ∀ N X, h N X ∈ supportedOn X)
    (hH : ∀ N, (∑ X ∈ E N, h N X).IsHermitian)
    (hsite : ∀ N, ∀ x : Fin N, ∑ X ∈ (E N).filter (fun X ↦ x ∈ X), opNorm (h N X) ≤ Jsite)
    (U_W U_V : (N : ℕ) → Finset (Fin N))
    (hUW : ∀ N, (U_W N).card ≤ sW) (hUV : ∀ N, (U_V N).card ≤ sV)
    (W V : (N : ℕ) → QubitOp N)
    (hWherm : ∀ N, (W N).IsHermitian) (hVherm : ∀ N, (V N).IsHermitian)
    (hW : ∀ N, W N ∈ supportedOn (U_W N)) (hV : ∀ N, V N ∈ supportedOn (U_V N))
    (hW_norm : ∀ N, opNorm (W N) ≤ C_W) (hV_norm : ∀ N, opNorm (V N) ≤ C_V)
    (F_real : ℝ → ℂ)
    (hreal_lim : ∀ t : ℝ, Filter.Tendsto (fun N ↦ concreteOTOC (hH N) β (W N) (V N) (t : ℂ))
      Filter.atTop (nhds (F_real t))) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    let S : ℝ := β / 4 + κ / 2
    ∃ F : ℂ → ℂ,
      DifferentiableOn ℂ F {z : ℂ | |z.im| < S} ∧
      (∀ t : ℝ, F (t : ℂ) = F_real t) ∧
      TendstoLocallyUniformlyOn (fun N z ↦ concreteOTOC (hH N) β (W N) (V N) z) F Filter.atTop
        {z : ℂ | |z.im| < S} ∧
      (∀ (t τ : ℝ), |τ| < S →
        ‖F ((t : ℂ) + Complex.I * (τ : ℂ))‖ ≤
          min (C_V ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (W N) τ 0) Filter.atTop)
            (min (C_W ^ 2 * Filter.liminf (fun N ↦ concreteWightmanNormAtShift (hH N) β (V N) (-τ) 0) Filter.atTop)
              (Filter.liminf (fun N ↦ concreteTimeOrderedT (hH N) β (W N) (V N) t τ) Filter.atTop))) := by
  sorry

theorem theorem_1_3a_high_temp_eq_1_20 {N r : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {Jsite β : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    (hβ0 : 0 ≤ β) (hβ : β ≤ highTempBetaWC r Jsite)
    (A : QubitOp N) :
    (concreteGibbsWightmanInner hH β A (concreteQuantumGlauberGen hH β A)).re ≤
      ∑ x : Fin N, concreteGibbsWightmanNormSq hH β (siteSizeOp x A) ∧
    ∑ x : Fin N, concreteGibbsWightmanNormSq hH β (siteSizeOp x A) ≤
      9 * (concreteGibbsWightmanInner hH β A (concreteWightmanQ hH β A)).re := by
  sorry

theorem prop_8_1_araki_1d_independent_r_R {N r R : ℕ}
    (E : Finset (Finset (Fin N)))
    (hne : ∀ X ∈ E, X.Nonempty)
    (_hcard : ∀ X ∈ E, X.card ≤ r)
    (hdiam : ∀ X ∈ E, ∀ x ∈ X, ∀ y ∈ X, |(x.val : ℤ) - (y.val : ℤ)| ≤ (R : ℤ))
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ y : Fin N, ∑ X ∈ E.filter (fun X ↦ y ∈ X), opNorm (h X) ≤ J)
    (β : ℝ) (A : QubitOp N) :
    concreteOtocCW hH β A ≤ (3 / 2 : ℝ) * (araki1DM β (R + 1) J) ^ 2 *
      (concreteGibbsWightmanInner hH β A (concreteQuantumGlauberGen hH β A)).re ∧
    (concreteGibbsWightmanInner hH β A (concreteQuantumGlauberGen hH β A)).re ≤
      ∑ x : Fin N, concreteGibbsWightmanNormSq hH β (siteSizeOp x A) ∧
    (∀ C_RP : ℝ,
      (concreteGibbsWightmanInner hH β A (concreteQuantumGlauberGen hH β A)).re ≤
        C_RP * (concreteGibbsWightmanInner hH β A (concreteWightmanQ hH β A)).re →
      concreteOtocCW hH β A ≤ (3 / 2 : ℝ) * (araki1DM β (R + 1) J) ^ 2 * C_RP *
        (concreteGibbsWightmanInner hH β A (concreteWightmanQ hH β A)).re) := by
  sorry

theorem prop_8_3_ising_explicit_eq_8_4_cosh {N Δ : ℕ} {β H_max : ℝ} (hβ : 0 ≤ β) (hHmax : 0 ≤ H_max)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ)
    (hdeg : ∀ i : Fin N,
      (∑ e : IsingEdge N,
        if J e.1.1 e.1.2 ≠ 0 then
          ((if e.1.1 = i then (1 : ℝ) else 0) + (if e.1.2 = i then (1 : ℝ) else 0))
        else 0) ≤ (Δ : ℝ))
    (hloc : ∀ i : Fin N,
      |hfield i| +
        ∑ e : IsingEdge N,
          ((if e.1.1 = i then |J e.1.1 e.1.2| else 0) + (if e.1.2 = i then |J e.1.1 e.1.2| else 0)) ≤ H_max)
    (f : SpinConfig N → ℝ) :
    glauberDirichlet (isingGibbsMeasure β J hfield) f ≤
      (Real.cosh (β * H_max + ((Δ : ℝ) / 2) * Real.log 2)) ^ 2 *
        degreeFiltrationQ (isingGibbsMeasure β J hfield) f := by
  sorry

theorem prop_9_1_part3_doubleWell_end_to_end_eq_9_3 {D : ℕ} (hD : 4 ≤ D) :
    ∃ (Ep Em : ℝ → ℝ) (φp φm : ℝ → (Fin D → ℝ)),
      (∀ E_B : ℝ, 2 < E_B →
        doubleWellTridiag D E_B *ᵥ φp E_B = Ep E_B • φp E_B ∧
        doubleWellTridiag D E_B *ᵥ φm E_B = Em E_B • φm E_B ∧
        parityMat D *ᵥ φp E_B = φp E_B ∧
        parityMat D *ᵥ φm E_B = -(φm E_B) ∧
        (∑ j : Fin D, φp E_B j ^ 2 = 1) ∧
        (∑ j : Fin D, φm E_B j ^ 2 = 1) ∧
        0 < φp E_B ⟨0, by omega⟩ ∧
        0 < φm E_B ⟨0, by omega⟩ ∧
        -(1 / (E_B - 2)) ≤ Ep E_B ∧ Ep E_B ≤ 0 ∧
        -(1 / (E_B - 2)) ≤ Em E_B ∧ Em E_B ≤ 0 ∧
        Ep E_B ≠ Em E_B) ∧
      (let ψ0 : ℝ → Fin D → ℂ := fun E_B j ↦
          (((φp E_B j + φm E_B j) / Real.sqrt 2 : ℝ) : ℂ)
       let tStar : ℝ → ℝ := fun E_B ↦ Real.pi / |Em E_B - Ep E_B|
       let ψT : ℝ → Fin D → ℂ := fun E_B j ↦
          (Complex.exp (-Complex.I * (Ep E_B : ℂ) * (tStar E_B : ℂ)) * (φp E_B j : ℂ) +
           Complex.exp (-Complex.I * (Em E_B : ℂ) * (tStar E_B : ℂ)) * (φm E_B j : ℂ)) /
            (Real.sqrt 2 : ℂ)
       let K_fn : ℝ → ℝ := fun E_B ↦ Real.sin ((Em E_B - Ep E_B) * tStar E_B / 2) ^ 2
       let Qexp : (Fin D → ℂ) → ℝ := fun ψ ↦ ∑ j : Fin D, (j.val : ℝ) * ‖ψ j‖ ^ 2
       let Q2exp : (Fin D → ℂ) → ℝ := fun ψ ↦ ∑ j : Fin D, (j.val : ℝ) ^ 2 * ‖ψ j‖ ^ 2
       let σ0_fn : ℝ → ℝ := fun E_B ↦ Real.sqrt (Q2exp (ψ0 E_B) - Qexp (ψ0 E_B) ^ 2)
       let ΔQ_fn : ℝ → ℝ := fun E_B ↦ Qexp (ψT E_B) - Qexp (ψ0 E_B)
       (∀ E_B : ℝ, 2 < E_B → K_fn E_B = 1) ∧
       Filter.Tendsto σ0_fn Filter.atTop (nhds 0) ∧
       Filter.Tendsto ΔQ_fn Filter.atTop (nhds ((D : ℝ) - 1)) ∧
       Filter.Tendsto (fun E_B : ℝ ↦ ΔQ_fn E_B / (K_fn E_B + σ0_fn E_B * Real.sqrt (K_fn E_B)))
         Filter.atTop (nhds ((D : ℝ) - 1))) := by
  sorry
