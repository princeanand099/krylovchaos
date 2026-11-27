/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.EntropicDecoupling
import KrylovChaos.HighTempParams
import KrylovChaos.Theorem11bConcrete
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Unconditional High-Temperature Chaos Bound (Eq. 1.24 & Theorem 1.3(c))

Establishes Eq. (1.24) and the unconditional family-level Theorem 1.3(c) on `QubitOp N`
without assuming Hypothesis (H2), strictly on top of Mathlib `v4.35.0`:
1. `supportedOn_le_filtrationSubmodule`: any operator supported on `U` with `U.card ≤ s`
   lies in `filtrationSubmodule N s`.
2. `theorem_1_3c_eq_1_24_concrete`: for any `r`-local Hermitian qubit Hamiltonian
   `H = ∑ Z ∈ E, h Z` (`r ≥ 2`, site strength `≤ Jsite`), `β ∈ [0, highTempBetaWC r Jsite]`,
   and `s₀`-local Hermitian observable `O` (`‖O‖_{β,W} = 1`, `opNorm O ≤ C_O`), for all
   sufficiently large `N` (explicitly `(bgDecouplingC2 r s₀ C_O) ^ 2 ≤ N`) and all `t : ℝ`:
   `mssThermalSize G (heisenbergEvol hH t O) ≤
     216 * ((r - 1) * concreteKrylovComplexity hH β O t + s₀) +
     (24 * √3) * √(N * ((r - 1) * concreteKrylovComplexity hH β O t + s₀)) +
     bgDecouplingC2 r s₀ C_O * √N`.
3. `theorem_1_3c_unconditional_family`: family-level Theorem 1.3(c) with NO `(H2)` hypothesis.
   From uniform `(r, Jsite)`, `β ∈ (0, highTempBetaWC r Jsite]`, `s₀`-local Hermitian `O_N`
   (`‖O_N‖_{β,W} = 1`, `opNorm (O_N N) ≤ C_O`), and uniform linear Lanczos domination
   `b_{n,T,N}^{(W)} ≤ α n + γ` with `2 α ≤ 2π / (β + 2κ)` (`κ > 0`), proves BOTH:
   - `λ_{L,T}^{(W)} ≤ 2 α ≤ 2π / (β + 2κ) < 2π / β`, and
   - `λ_{L,T}^{(MSS)} ≤ 2 α ≤ 2π / (β + 2κ) < 2π / β`.
-/

namespace KrylovChaos

open Filter Topology

section FiltrationSupportBridge

/-- Any operator supported on `U : Finset (Fin N)` with `U.card ≤ s` belongs to
`filtrationSubmodule N s`. -/
lemma supportedOn_le_filtrationSubmodule {N s : ℕ} {U : Finset (Fin N)} (hU : U.card ≤ s) :
    supportedOn U ≤ filtrationSubmodule N s := by
  unfold supportedOn filtrationSubmodule
  refine Submodule.span_mono ?_
  rintro A ⟨a, ha, rfl⟩
  refine ⟨a, ?_, rfl⟩
  unfold pauliWeight
  refine le_trans (Finset.card_le_card ?_) hU
  intro x hx
  exact ha x (Finset.mem_filter.mp hx).2

/-- An `r`-local Hamiltonian `∑ Z ∈ E, h Z` belongs to `filtrationSubmodule N r`. -/
lemma localHamiltonian_mem_filtrationSubmodule {N r : ℕ}
    (E : Finset (Finset (Fin N))) (hcard : ∀ Z ∈ E, Z.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ Z, h Z ∈ supportedOn Z) :
    (∑ Z ∈ E, h Z) ∈ filtrationSubmodule N r :=
  Submodule.sum_mem _ fun Z hZ ↦ supportedOn_le_filtrationSubmodule (hcard Z hZ) (hsupp Z)

end FiltrationSupportBridge

section Eq124AndTheorem13c

/-- **Eq. (1.24) (Concrete High-Temperature Thermal Size–Krylov Complexity Bound on `QubitOp N`)**:
For any `N ≥ 1`, `r`-local Hermitian qubit Hamiltonian `H = ∑ Z ∈ E, h Z` (`r ≥ 2`, site strength
`≤ Jsite`), `β ∈ [0, highTempBetaWC r Jsite]`, and `s₀`-local Hermitian observable `O`
(`O ∈ supportedOn U₀`, `U₀.card ≤ s₀`, `gibbsWightmanNormSq G O = 1`, `opNorm O ≤ C_O`, `1 ≤ C_O`):
1. For ALL `N ≥ 1` and ALL `t : ℝ`, letting `K := (r - 1) * K_β^W(t) + s₀` and
   `C₂ := bgDecouplingC2 r s₀ C_O`:
   `mssThermalSize G (O(t)) ≤ 216 * K + (24 * √(3 * (1 + C₂))) * √(N * K) + C₂ * √N`.
2. For ALL `N` with `C₂ ^ 2 ≤ N` (sufficiently large `N`) and ALL `t : ℝ`:
   `mssThermalSize G (O(t)) ≤ 216 * K + (24 * √3) * √(N * K) + C₂ * √N`. -/
theorem theorem_1_3c_eq_1_24_concrete {N r s₀ : ℕ}
    (hN : 1 ≤ N) (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hE_ne : ∀ Z ∈ E, Z.Nonempty) (hE_card : ∀ Z ∈ E, Z.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hh_supp : ∀ Z, h Z ∈ supportedOn Z)
    (hH : (∑ Z ∈ E, h Z).IsHermitian)
    {Jsite : ℝ} (hJ : 0 < Jsite)
    (hH_site : ∀ x : Fin N, ∑ Z ∈ E.filter (fun Z ↦ x ∈ Z), opNorm (h Z) ≤ Jsite)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ highTempBetaWC r Jsite)
    {U₀ : Finset (Fin N)} (hU₀ : U₀.card ≤ s₀)
    {O : QubitOp N} (hO : O.IsHermitian) (hO_supp : O ∈ supportedOn U₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    {C_O : ℝ} (hCO_ge1 : 1 ≤ C_O) (hCO : opNorm O ≤ C_O) (t : ℝ) :
    let G := concreteGibbsData hH β
    let K := ((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity hH β O t + (s₀ : ℝ)
    let C₂ := bgDecouplingC2 r s₀ C_O
    mssThermalSize G (heisenbergEvol hH (t : ℂ) O) ≤
      216 * K + 24 * Real.sqrt (3 * (1 + C₂)) * Real.sqrt ((N : ℝ) * K) + C₂ * Real.sqrt (N : ℝ) ∧
    (C₂ ^ 2 ≤ (N : ℝ) →
      mssThermalSize G (heisenbergEvol hH (t : ℂ) O) ≤
        216 * K + (24 * Real.sqrt 3) * Real.sqrt ((N : ℝ) * K) + C₂ * Real.sqrt (N : ℝ)) := by
  intro G K C₂
  have hHf : (∑ Z ∈ E, h Z) ∈ filtrationSubmodule N r :=
    localHamiltonian_mem_filtrationSubmodule E hE_card h hh_supp
  have hOf : O ∈ filtrationSubmodule N s₀ :=
    supportedOn_le_filtrationSubmodule hU₀ hO_supp
  have h13b := (theorem_1_3b_high_temp hr E hE_ne hE_card h hh_supp hH hJ hH_site hβ0 hβ hO hHf hOf hOnorm t).2
  have h64 := (prop_6_4_part2_unconditional hN hr E hE_ne hE_card h hh_supp hH hJ hH_site hβ0 hβ hU₀ hO_supp hOnorm hCO_ge1 hCO t).2.2
  have hK_nn : 0 ≤ K := by
    dsimp only [K]
    have hK0 : 0 ≤ concreteKrylovComplexity hH β O t := by
      unfold concreteKrylovComplexity
      exact Finset.sum_nonneg fun n _ ↦ mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
    positivity
  have hC₂_nn : 0 ≤ C₂ := by
    dsimp only [C₂, bgDecouplingC2]
    have h1 : (1 : ℝ) ≤ C_O * (2 : ℝ) ^ (s₀ + 1) := by
      calc (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ C_O * (2 : ℝ) ^ (s₀ + 1) := mul_le_mul hCO_ge1 (one_le_pow₀ (by norm_num)) (by norm_num) (by positivity)
    have hlog : 0 ≤ Real.log (C_O * (2 : ℝ) ^ (s₀ + 1)) := Real.log_nonneg h1
    positivity
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrtN_le_N : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    calc Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = (N : ℝ) := Real.sqrt_sq hN_nn
  have hsqrt216 : Real.sqrt (216 * K) = 6 * Real.sqrt 6 * Real.sqrt K := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 216), show (216 : ℝ) = 6 ^ 2 * 6 by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hcross_gen : 2 * Real.sqrt (otocI hH β (heisenbergEvol hH (t : ℂ) O)) *
      Real.sqrt ((N : ℝ) + C₂ * Real.sqrt (N : ℝ)) ≤
      24 * Real.sqrt (3 * (1 + C₂)) * Real.sqrt ((N : ℝ) * K) := by
    have h1 : Real.sqrt (otocI hH β (heisenbergEvol hH (t : ℂ) O)) ≤ Real.sqrt (216 * K) :=
      Real.sqrt_le_sqrt h13b
    have h2 : Real.sqrt ((N : ℝ) + C₂ * Real.sqrt (N : ℝ)) ≤ Real.sqrt ((1 + C₂) * (N : ℝ)) := by
      apply Real.sqrt_le_sqrt; nlinarith
    have hmul : 2 * Real.sqrt (otocI hH β (heisenbergEvol hH (t : ℂ) O)) *
        Real.sqrt ((N : ℝ) + C₂ * Real.sqrt (N : ℝ)) ≤
        2 * Real.sqrt (216 * K) * Real.sqrt ((1 + C₂) * (N : ℝ)) := by
      have hnn1 : 0 ≤ Real.sqrt (otocI hH β (heisenbergEvol hH (t : ℂ) O)) := Real.sqrt_nonneg _
      have hnn2 : 0 ≤ Real.sqrt ((N : ℝ) + C₂ * Real.sqrt (N : ℝ)) := Real.sqrt_nonneg _
      have hnn3 : 0 ≤ Real.sqrt (216 * K) := Real.sqrt_nonneg _
      have hnn4 : 0 ≤ Real.sqrt ((1 + C₂) * (N : ℝ)) := Real.sqrt_nonneg _
      nlinarith [mul_le_mul h1 h2 hnn2 hnn3]
    refine le_trans hmul ?_
    rw [show 2 * Real.sqrt (216 * K) * Real.sqrt ((1 + C₂) * (N : ℝ)) =
        2 * (Real.sqrt (216 * K) * Real.sqrt ((1 + C₂) * (N : ℝ))) by ring,
      ← Real.sqrt_mul (by positivity : 0 ≤ 216 * K)]
    have h216_le : 216 * K * ((1 + C₂) * (N : ℝ)) ≤ (12 ^ 2 * (3 * (1 + C₂))) * ((N : ℝ) * K) := by
      have hnn : 0 ≤ (1 + C₂) * ((N : ℝ) * K) := by positivity
      nlinarith
    calc 2 * Real.sqrt (216 * K * ((1 + C₂) * (N : ℝ)))
        ≤ 2 * Real.sqrt ((12 ^ 2 * (3 * (1 + C₂))) * ((N : ℝ) * K)) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h216_le) (by norm_num)
      _ = 2 * (12 * Real.sqrt (3 * (1 + C₂)) * Real.sqrt ((N : ℝ) * K)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      _ = 24 * Real.sqrt (3 * (1 + C₂)) * Real.sqrt ((N : ℝ) * K) := by ring
  refine ⟨by linarith [h64, h13b, hcross_gen], fun hN_big ↦ ?_⟩
  have hC₂_sqrtN : C₂ * Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    have hle : C₂ ≤ Real.sqrt (N : ℝ) := by
      calc C₂ = Real.sqrt (C₂ ^ 2) := (Real.sqrt_sq hC₂_nn).symm
        _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hN_big
    calc C₂ * Real.sqrt (N : ℝ) ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _)
      _ = (N : ℝ) := Real.mul_self_sqrt hN_nn
  have hcross_big : 2 * Real.sqrt (otocI hH β (heisenbergEvol hH (t : ℂ) O)) *
      Real.sqrt ((N : ℝ) + C₂ * Real.sqrt (N : ℝ)) ≤
      (24 * Real.sqrt 3) * Real.sqrt ((N : ℝ) * K) := by
    have h1 : Real.sqrt (otocI hH β (heisenbergEvol hH (t : ℂ) O)) ≤ Real.sqrt (216 * K) :=
      Real.sqrt_le_sqrt h13b
    have h2 : Real.sqrt ((N : ℝ) + C₂ * Real.sqrt (N : ℝ)) ≤ Real.sqrt (2 * (N : ℝ)) := by
      apply Real.sqrt_le_sqrt; linarith
    have hmul : 2 * Real.sqrt (otocI hH β (heisenbergEvol hH (t : ℂ) O)) *
        Real.sqrt ((N : ℝ) + C₂ * Real.sqrt (N : ℝ)) ≤
        2 * Real.sqrt (216 * K) * Real.sqrt (2 * (N : ℝ)) := by
      have hnn2 : 0 ≤ Real.sqrt ((N : ℝ) + C₂ * Real.sqrt (N : ℝ)) := Real.sqrt_nonneg _
      have hnn3 : 0 ≤ Real.sqrt (216 * K) := Real.sqrt_nonneg _
      nlinarith [mul_le_mul h1 h2 hnn2 hnn3]
    refine le_trans hmul ?_
    rw [show 2 * Real.sqrt (216 * K) * Real.sqrt (2 * (N : ℝ)) =
        2 * (Real.sqrt (216 * K) * Real.sqrt (2 * (N : ℝ))) by ring,
      ← Real.sqrt_mul (by positivity : 0 ≤ 216 * K),
      show 216 * K * (2 * (N : ℝ)) = (12 ^ 2 * 3) * ((N : ℝ) * K) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    ring_nf; exact le_rfl
  linarith [h64, h13b, hcross_big]

/-- Helper: if `c > 0` and `δ₁, δ₂, δ₃ > 0`, then for sufficiently large `N : ℕ`,
`A * N^(-δ₁) + B * N^(-δ₂) + C * N^(-δ₃) < c`. -/
private lemma eventually_three_rpow_neg_lt {c A B C δ₁ δ₂ δ₃ : ℝ}
    (hc : 0 < c) (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      A * (N : ℝ) ^ (-δ₁) + B * (N : ℝ) ^ (-δ₂) + C * (N : ℝ) ^ (-δ₃) < c := by
  have ht1 : Tendsto (fun N : ℕ ↦ A * (N : ℝ) ^ (-δ₁)) atTop (nhds 0) := by
    simpa [mul_zero] using ((tendsto_rpow_neg_atTop hδ₁).comp tendsto_natCast_atTop_atTop).const_mul A
  have ht2 : Tendsto (fun N : ℕ ↦ B * (N : ℝ) ^ (-δ₂)) atTop (nhds 0) := by
    simpa [mul_zero] using ((tendsto_rpow_neg_atTop hδ₂).comp tendsto_natCast_atTop_atTop).const_mul B
  have ht3 : Tendsto (fun N : ℕ ↦ C * (N : ℝ) ^ (-δ₃)) atTop (nhds 0) := by
    simpa [mul_zero] using ((tendsto_rpow_neg_atTop hδ₃).comp tendsto_natCast_atTop_atTop).const_mul C
  have hsum : Tendsto (fun N : ℕ ↦ A * (N : ℝ) ^ (-δ₁) + B * (N : ℝ) ^ (-δ₂) + C * (N : ℝ) ^ (-δ₃))
      atTop (nhds 0) := by
    simpa [add_zero] using (ht1.add ht2).add ht3
  have hev := (tendsto_order.mp hsum).2 c hc
  exact eventually_atTop.mp hev

/-- **Theorem 1.3(c) (Unconditional High-Temperature Chaos Bound — Zero `(H2)` Hypothesis)**:
For any uniform family of `r`-local Hermitian qubit Hamiltonians `H_N = ∑ Z ∈ E_N, h_N Z`
(`r ≥ 2`, uniform site strength `≤ Jsite`), inverse temperature `β ∈ (0, highTempBetaWC r Jsite]`,
`s₀`-local Hermitian observables `O_N` (`‖O_N‖_{β,W} = 1`, `opNorm (O_N N) ≤ C_O`), and uniform
linear Lanczos domination `b_{n,T,N}^{(W)} ≤ α n + γ` with `2 α ≤ 2π / (β + 2κ)` (`κ > 0`):
1. Any Wightman scrambling rate `lamW > 0` satisfying `(H1_W)` obeys
   `lamW ≤ 2 * α ≤ 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β`.
2. Any MSS thermal-size scrambling rate `lamMSS > 0` satisfying `(H1)` obeys
   `lamMSS ≤ 2 * α ≤ 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β`. -/
theorem theorem_1_3c_unconditional_family {r s₀ : ℕ} (hr : 2 ≤ r)
    {Jsite β κ α γ C_O lamW lamMSS : ℝ}
    (hJ : 0 < Jsite) (hβ0 : 0 < β) (hβ : β ≤ highTempBetaWC r Jsite)
    (hκ : 0 < κ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (hα_kms : 2 * α ≤ 2 * Real.pi / (β + 2 * κ))
    (hCO_ge1 : 1 ≤ C_O) (hlamW : 0 < lamW) (hlamMSS : 0 < lamMSS)
    (E : (N : ℕ) → Finset (Finset (Fin N)))
    (hE_ne : ∀ N, ∀ Z ∈ E N, Z.Nonempty)
    (hE_card : ∀ N, ∀ Z ∈ E N, Z.card ≤ r)
    (h : (N : ℕ) → Finset (Fin N) → QubitOp N)
    (hh_supp : ∀ N Z, h N Z ∈ supportedOn Z)
    (hH : ∀ N, (∑ Z ∈ E N, h N Z).IsHermitian)
    (hH_site : ∀ N, ∀ x : Fin N, ∑ Z ∈ (E N).filter (fun Z ↦ x ∈ Z), opNorm (h N Z) ≤ Jsite)
    (U₀ : (N : ℕ) → Finset (Fin N)) (hU₀ : ∀ N, (U₀ N).card ≤ s₀)
    (O : (N : ℕ) → QubitOp N)
    (hO : ∀ N, (O N).IsHermitian)
    (hO_supp : ∀ N, O N ∈ supportedOn (U₀ N))
    (hOnorm : ∀ N, gibbsWightmanNormSq (concreteGibbsData (hH N) β) (O N) = 1)
    (hCO : ∀ N, opNorm (O N) ≤ C_O)
    (hb_lin : ∀ N n, 1 ≤ n → n ≤ 4 ^ N - 1 →
      lanczosCoeff (concreteGibbsData (hH N) β) (∑ Z ∈ E N, h N Z) (O N) n ≤ α * (n : ℝ) + γ)
    (hH1_W : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        let tN := ((1 - ε) / lamW) * Real.log (N : ℝ)
        c * (N : ℝ) ^ (1 - ε) ≤
          otocCW (concreteGibbsData (hH N) β) (heisenbergEvol (hH N) (tN : ℂ) (O N)))
    (hH1_MSS : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        let tN := ((1 - ε) / lamMSS) * Real.log (N : ℝ)
        c * (N : ℝ) ^ (1 - ε) ≤
          mssThermalSize (concreteGibbsData (hH N) β) (heisenbergEvol (hH N) (tN : ℂ) (O N))) :
    (lamW ≤ 2 * α ∧ 2 * α ≤ 2 * Real.pi / (β + 2 * κ) ∧ 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β) ∧
    (lamMSS ≤ 2 * α ∧ 2 * α ≤ 2 * Real.pi / (β + 2 * κ) ∧ 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β) := by
  have hstrict : 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β :=
    div_lt_div_of_pos_left (by positivity) hβ0 (by linarith)
  set C_K : ℝ := Real.exp ((1 / 2 + γ / α) * 1) / (4 * Real.exp 1 * Real.tanh (1 / 4))
  have hCK_pos : 0 < C_K := by
    dsimp only [C_K]
    have htanh : 0 < Real.tanh (1 / 4) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _)
    positivity
  have hlamW_le : lamW ≤ 2 * α := by
    by_contra hgt; push Not at hgt
    set θ : ℝ := 2 * α / lamW
    have hθ_lt : θ < 1 := (div_lt_one hlamW).mpr hgt
    have hθ_pos : 0 < θ := div_pos (by positivity) hlamW
    set ε₀ : ℝ := min (1 / 2) ((1 - θ) / 2)
    have hε₀ : 0 < ε₀ := lt_min (by norm_num) (by linarith)
    rcases hH1_W ε₀ hε₀ with ⟨ε, ⟨hε_pos, hε_lt⟩, c, hc_pos, N₁, hN₁⟩
    have hε_half : ε < 1 / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have h1mε_pos : 0 < 1 - ε := by linarith
    set δ₁ : ℝ := (1 - θ) * (1 - ε)
    have hδ₁ : 0 < δ₁ := mul_pos (by linarith) h1mε_pos
    rcases eventually_three_rpow_neg_lt hc_pos hδ₁ h1mε_pos h1mε_pos
      (A := 54 * ((r - 1 : ℕ) : ℝ) * C_K) (B := 54 * (s₀ : ℝ)) (C := 0) with ⟨N₂, hN₂⟩
    set N := max (max N₁ N₂) 2
    have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
    have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
    have hN_ge2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_max_right (max N₁ N₂) 2)
    have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlog_pos : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
    set tN : ℝ := ((1 - ε) / lamW) * Real.log (N : ℝ)
    have htN_nn : 0 ≤ tN := by dsimp only [tN]; positivity
    have hlow := hN₁ N hN1
    have h13b := (theorem_1_3b_high_temp hr (E N) (hE_ne N) (hE_card N) (h N) (hh_supp N)
      (hH N) hJ (hH_site N) hβ0.le hβ (hO N)
      (localHamiltonian_mem_filtrationSubmodule (E N) (hE_card N) (h N) (hh_supp N))
      (supportedOn_le_filtrationSubmodule (hU₀ N) (hO_supp N)) (hOnorm N) tN).1
    have hK := theorem_1_1a_concrete_qubit_complexity (hH N) (hO N) β (hOnorm N) hα hγ one_pos
      (hb_lin N) tN htN_nn
    have hexp_eq : Real.exp (2 * α * tN) = (N : ℝ) ^ (θ * (1 - ε)) := by
      dsimp only [tN, θ]
      rw [show 2 * α * ((1 - ε) / lamW * Real.log (N : ℝ)) = Real.log (N : ℝ) * (2 * α / lamW * (1 - ε)) by ring,
        ← Real.rpow_def_of_pos hN_pos]
    rw [hexp_eq] at hK
    have hup : otocCW (concreteGibbsData (hH N) β) (heisenbergEvol (hH N) (tN : ℂ) (O N)) ≤
        54 * ((r - 1 : ℕ) : ℝ) * C_K * (N : ℝ) ^ (θ * (1 - ε)) + 54 * (s₀ : ℝ) := by
      have hr1 : 0 ≤ ((r - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hdiv_pos : 0 < (N : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos hN_pos _
    have hdiv := div_le_div_of_nonneg_right (le_trans hlow hup) hdiv_pos.le
    rw [mul_div_cancel_right₀ c hdiv_pos.ne', add_div] at hdiv
    have hr1_eq : (N : ℝ) ^ (θ * (1 - ε)) / (N : ℝ) ^ (1 - ε) = (N : ℝ) ^ (-δ₁) := by
      rw [← Real.rpow_sub hN_pos]; congr 1; dsimp only [δ₁]; ring
    have hr2_eq : (54 * (s₀ : ℝ)) / (N : ℝ) ^ (1 - ε) = 54 * (s₀ : ℝ) * (N : ℝ) ^ (-(1 - ε)) := by
      rw [Real.rpow_neg hN_pos.le, div_eq_mul_inv]
    rw [mul_div_assoc, hr1_eq, hr2_eq] at hdiv
    have hlt := hN₂ N hN2
    linarith
  have hlamMSS_le : lamMSS ≤ 2 * α := by
    by_contra hgt; push Not at hgt
    set θ : ℝ := 2 * α / lamMSS
    have hθ_lt : θ < 1 := (div_lt_one hlamMSS).mpr hgt
    have hθ_pos : 0 < θ := div_pos (by positivity) hlamMSS
    set ε₀ : ℝ := min (1 / 4) ((1 - θ) / 4)
    have hε₀ : 0 < ε₀ := lt_min (by norm_num) (by linarith)
    rcases hH1_MSS ε₀ hε₀ with ⟨ε, ⟨hε_pos, hε_lt⟩, c, hc_pos, N₁, hN₁⟩
    have hε_q : ε < 1 / 4 := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_t : ε < (1 - θ) / 4 := lt_of_lt_of_le hε_lt (min_le_right _ _)
    have h1mε_pos : 0 < 1 - ε := by linarith
    set δ₁ : ℝ := (1 - θ) * (1 - ε)
    set δ₂ : ℝ := (1 - ε) - (1 + θ * (1 - ε)) / 2
    set δ₃ : ℝ := (1 - ε) - 1 / 2
    have hδ₁ : 0 < δ₁ := mul_pos (by linarith) h1mε_pos
    have hδ₂ : 0 < δ₂ := by dsimp only [δ₂]; nlinarith
    have hδ₃ : 0 < δ₃ := by dsimp only [δ₃]; linarith
    set C₂ : ℝ := bgDecouplingC2 r s₀ C_O
    set A_K : ℝ := ((r - 1 : ℕ) : ℝ) * C_K + (s₀ : ℝ)
    have hAK_pos : 0 < A_K := by
      dsimp only [A_K]
      have hr1 : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
      positivity
    rcases eventually_three_rpow_neg_lt hc_pos hδ₁ hδ₂ hδ₃
      (A := 216 * A_K) (B := 24 * Real.sqrt (3 * (1 + C₂)) * Real.sqrt A_K) (C := C₂) with ⟨N₂, hN₂⟩
    set N := max (max N₁ N₂) 2
    have hN1 : N₁ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
    have hN2 : N₂ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
    have hN_ge1 : 1 ≤ N := le_trans (by omega : 1 ≤ 2) (le_max_right _ _)
    have hN_ge2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (le_max_right (max N₁ N₂) 2)
    have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
    have hlog_pos : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
    set tN : ℝ := ((1 - ε) / lamMSS) * Real.log (N : ℝ)
    have htN_nn : 0 ≤ tN := by dsimp only [tN]; positivity
    have hlow := hN₁ N hN1
    have h124 := (theorem_1_3c_eq_1_24_concrete hN_ge1 hr (E N) (hE_ne N) (hE_card N) (h N)
      (hh_supp N) (hH N) hJ (hH_site N) hβ0.le hβ (hU₀ N) (hO N) (hO_supp N)
      (hOnorm N) hCO_ge1 (hCO N) tN).1
    have hK := theorem_1_1a_concrete_qubit_complexity (hH N) (hO N) β (hOnorm N) hα hγ one_pos
      (hb_lin N) tN htN_nn
    have hexp_eq : Real.exp (2 * α * tN) = (N : ℝ) ^ (θ * (1 - ε)) := by
      dsimp only [tN, θ]
      rw [show 2 * α * ((1 - ε) / lamMSS * Real.log (N : ℝ)) = Real.log (N : ℝ) * (2 * α / lamMSS * (1 - ε)) by ring,
        ← Real.rpow_def_of_pos hN_pos]
    rw [hexp_eq] at hK
    have hN_pow_ge1 : (1 : ℝ) ≤ (N : ℝ) ^ (θ * (1 - ε)) :=
      Real.one_le_rpow (by linarith) (by positivity)
    have hK_tot : ((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity (hH N) β (O N) tN + (s₀ : ℝ) ≤
        A_K * (N : ℝ) ^ (θ * (1 - ε)) := by
      dsimp only [A_K]
      have hr1 : 0 ≤ ((r - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      have hs0 : 0 ≤ (s₀ : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hsqrt_NK : Real.sqrt ((N : ℝ) * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity (hH N) β (O N) tN + (s₀ : ℝ))) ≤
        Real.sqrt A_K * (N : ℝ) ^ ((1 + θ * (1 - ε)) / 2) := by
      have h1 : (N : ℝ) * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity (hH N) β (O N) tN + (s₀ : ℝ)) ≤
          A_K * (N : ℝ) ^ (1 + θ * (1 - ε)) := by
        rw [Real.rpow_add hN_pos, Real.rpow_one]
        have := mul_le_mul_of_nonneg_left hK_tot hN_pos.le
        linarith
      calc Real.sqrt ((N : ℝ) * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity (hH N) β (O N) tN + (s₀ : ℝ)))
          ≤ Real.sqrt (A_K * (N : ℝ) ^ (1 + θ * (1 - ε))) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt A_K * Real.sqrt ((N : ℝ) ^ (1 + θ * (1 - ε))) := Real.sqrt_mul hAK_pos.le _
        _ = Real.sqrt A_K * (N : ℝ) ^ ((1 + θ * (1 - ε)) / 2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN_pos.le]; ring_nf
    have hsqrt_N : Real.sqrt (N : ℝ) = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (N : ℝ)
    have hup : mssThermalSize (concreteGibbsData (hH N) β) (heisenbergEvol (hH N) (tN : ℂ) (O N)) ≤
        216 * A_K * (N : ℝ) ^ (θ * (1 - ε)) +
        24 * Real.sqrt (3 * (1 + C₂)) * Real.sqrt A_K * (N : ℝ) ^ ((1 + θ * (1 - ε)) / 2) +
        C₂ * (N : ℝ) ^ ((1 : ℝ) / 2) := by
      have hC₂_nn : 0 ≤ C₂ := by
        dsimp only [C₂, bgDecouplingC2]
        have h1 : (1 : ℝ) ≤ C_O * (2 : ℝ) ^ (s₀ + 1) := by
          calc (1 : ℝ) = 1 * 1 := by norm_num
            _ ≤ C_O * (2 : ℝ) ^ (s₀ + 1) := mul_le_mul hCO_ge1 (one_le_pow₀ (by norm_num)) (by norm_num) (by positivity)
        have hlog : 0 ≤ Real.log (C_O * (2 : ℝ) ^ (s₀ + 1)) := Real.log_nonneg h1
        positivity
      have hterm2 : 24 * Real.sqrt (3 * (1 + C₂)) *
          Real.sqrt ((N : ℝ) * (((r - 1 : ℕ) : ℝ) * concreteKrylovComplexity (hH N) β (O N) tN + (s₀ : ℝ))) ≤
          24 * Real.sqrt (3 * (1 + C₂)) * Real.sqrt A_K * (N : ℝ) ^ ((1 + θ * (1 - ε)) / 2) := by
        calc _ ≤ 24 * Real.sqrt (3 * (1 + C₂)) * (Real.sqrt A_K * (N : ℝ) ^ ((1 + θ * (1 - ε)) / 2)) :=
              mul_le_mul_of_nonneg_left hsqrt_NK (by positivity)
          _ = _ := by ring
      rw [hsqrt_N] at h124
      linarith
    have hdiv_pos : 0 < (N : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos hN_pos _
    have hdiv := div_le_div_of_nonneg_right (le_trans hlow hup) hdiv_pos.le
    rw [mul_div_cancel_right₀ c hdiv_pos.ne', add_div, add_div] at hdiv
    have hr1 : (N : ℝ) ^ (θ * (1 - ε)) / (N : ℝ) ^ (1 - ε) = (N : ℝ) ^ (-δ₁) := by
      rw [← Real.rpow_sub hN_pos]; congr 1; dsimp only [δ₁]; ring
    have hr2 : (N : ℝ) ^ ((1 + θ * (1 - ε)) / 2) / (N : ℝ) ^ (1 - ε) = (N : ℝ) ^ (-δ₂) := by
      rw [← Real.rpow_sub hN_pos]; congr 1; dsimp only [δ₂]; ring
    have hr3 : (N : ℝ) ^ ((1 : ℝ) / 2) / (N : ℝ) ^ (1 - ε) = (N : ℝ) ^ (-δ₃) := by
      rw [← Real.rpow_sub hN_pos]; congr 1; dsimp only [δ₃]; ring
    rw [mul_div_assoc, mul_div_assoc, mul_div_assoc, hr1, hr2, hr3] at hdiv
    have hlt := hN₂ N hN2
    linarith
  exact ⟨⟨hlamW_le, hα_kms, hstrict⟩, ⟨hlamMSS_le, hα_kms, hstrict⟩⟩

end Eq124AndTheorem13c

end KrylovChaos
