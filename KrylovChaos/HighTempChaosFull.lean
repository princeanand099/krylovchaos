/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.HighTempChaosBound
import KrylovChaos.Milestone2SpectralAndVitali
import Mathlib.Tactic

/-!
# Theorem 1.3(c): End-to-End High-Temperature Chaos Bound with KMS Rate Discharged via Theorem 1.2(a)–(b)

Wires Theorem 1.2(a)–(b) (`theorem_1_2a_thermo_limit_eq_1_15_and_rW`,
`wightmanStripHalfWidth_ge_beta_half_add_kappa`, `theorem_1_2b_from_strip_measure`) directly
into `theorem_1_3c_unconditional_family`, automatically discharging the KMS rate inequality
`2 * α ≤ 2 * π / (β + 2 * κ)` from the thermodynamic-limit Wightman spectral measure `μ` and
Lanczos sequence `b_inf` with `b_inf n / n → α` and `κ = (2 * (r - 1) * Jsite)⁻¹`.
-/

namespace KrylovChaos

open Matrix MeasureTheory Filter Topology

section HighTempChaosWithKMSDischarge

/-- Discharges `2 * α ≤ 2 * π / (β + 2 * κ)` directly from weak convergence of finite-volume
Wightman spectral measures `μ_N → μ`, uniform strip cosh bounds for all `κ' ∈ [0, κ)`, and
a thermodynamic-limit Lanczos sequence `b_inf` with `b_inf n / n → α` matching the even moments of `μ`. -/
theorem kms_rate_bound_from_thermo_limit_spectral_measure
    (μ_N : ℕ → Measure ℝ) (μ : Measure ℝ)
    [∀ N, IsFiniteMeasure (μ_N N)] [IsFiniteMeasure μ]
    (hweak : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun N ↦ ∫ ω, f ω ∂(μ_N N)) atTop (nhds (∫ ω, f ω ∂μ)))
    {β κ α : ℝ} (hβ0 : 0 < β) (hκ : 0 < κ)
    (hunif : ∀ κ' : ℝ, 0 ≤ κ' → κ' < κ →
      ∃ M > 0, ∀ N, Integrable (fun ω : ℝ ↦ Real.cosh ((β / 2 + κ') * ω)) (μ_N N) ∧
        ∫ ω : ℝ, Real.cosh ((β / 2 + κ') * ω) ∂(μ_N N) ≤ M)
    (b_inf : ℕ → ℝ) (hb_pos : ∀ h ≥ 1, 0 < b_inf h)
    (hb_lim : Tendsto (fun n : ℕ ↦ b_inf n / (n : ℝ)) atTop (nhds α))
    (hmom_eq : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b_inf) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ) :
    2 * α ≤ 2 * Real.pi / (β + 2 * κ) := by
  have hle_all : ∀ κ' : ℝ, 0 ≤ κ' → κ' < κ → 2 * α ≤ 2 * Real.pi / (β + 2 * κ') := by
    intro κ' hκ'_nn hκ'_lt
    rcases hunif κ' hκ'_nn hκ'_lt with ⟨M, hM_pos, hM_unif⟩
    have hr_pos : 0 < β / 2 + κ' := by linarith
    rcases theorem_1_2a_thermo_limit_eq_1_15_and_rW μ_N μ hweak hr_pos hM_pos.le hM_unif with
      ⟨hcosh_int, hcosh_le, _, _⟩
    have h12b := theorem_1_2b_from_strip_measure μ b_inf hr_pos hM_pos hcosh_int hcosh_le hb_pos hmom_eq
    rw [hb_lim.liminf_eq] at h12b
    have hrew : Real.pi / (β / 2 + κ') = 2 * Real.pi / (β + 2 * κ') := by
      have hne1 : β / 2 + κ' ≠ 0 := hr_pos.ne'
      have hne2 : β + 2 * κ' ≠ 0 := by linarith
      field_simp [hne1, hne2]
    rwa [hrew] at h12b
  -- Take `κ' = κ - 1 / (m + 2)` as `m → ∞` using continuity of `κ' ↦ 2 * π / (β + 2 * κ')`.
  let seq : ℕ → ℝ := fun m ↦ κ - κ / ((m : ℝ) + 2)
  have hseq_tend : Tendsto seq atTop (nhds κ) := by
    have hdiv : Tendsto (fun m : ℕ ↦ κ / ((m : ℝ) + 2)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa [seq] using tendsto_const_nhds.sub hdiv
  have hcont : ContinuousAt (fun x : ℝ ↦ 2 * Real.pi / (β + 2 * x)) κ :=
    continuousAt_const.div (continuousAt_const.add (continuousAt_const.mul continuousAt_id))
      (by linarith)
  have hfn_tend : Tendsto (fun m : ℕ ↦ 2 * Real.pi / (β + 2 * seq m)) atTop
      (nhds (2 * Real.pi / (β + 2 * κ))) := hcont.tendsto.comp hseq_tend
  refine ge_of_tendsto hfn_tend ?_
  filter_upwards with m
  have hm2 : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have hseq_nn : 0 ≤ seq m := by
    dsimp only [seq]
    have hle : κ / ((m : ℝ) + 2) ≤ κ := div_le_self hκ.le (by linarith)
    linarith
  have hseq_lt : seq m < κ := by
    dsimp only [seq]
    have hpos : 0 < κ / ((m : ℝ) + 2) := div_pos hκ (by linarith)
    linarith
  exact hle_all (seq m) hseq_nn hseq_lt

/-- **Theorem 1.3(c) (Full Family-Level High-Temperature Chaos Bound with KMS Rate Discharged)**:
Combines Theorem 1.2(a)–(b) (`kms_rate_bound_from_thermo_limit_spectral_measure`) with
`theorem_1_3c_unconditional_family`, taking NEITHER Hypothesis (H2) NOR `hα_kms`:
with `κ = (2 * ((r : ℝ) - 1) * Jsite)⁻¹`, proves:
1. `lamW ≤ 2 * α ≤ 2 * π / (β + 2 * κ) < 2 * π / β`,
2. `lamMSS ≤ 2 * α ≤ 2 * π / (β + 2 * κ) < 2 * π / β`,
and (when the cosh-integrability set is bounded above) `β / 2 + κ ≤ wightmanStripHalfWidth μ`. -/
theorem theorem_1_3c_full_with_kms_discharge {r s₀ : ℕ} (hr : 2 ≤ r)
    {Jsite β α γ C_O lamW lamMSS : ℝ}
    (hJ : 0 < Jsite) (hβ0 : 0 < β) (hβ : β ≤ highTempBetaWC r Jsite)
    (hα : 0 < α) (hγ : 0 ≤ γ)
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
    -- Thermodynamic-limit Wightman spectral measure and Lanczos sequence (Theorem 1.2(a)–(b) inputs)
    (μ_N : ℕ → Measure ℝ) (μ : Measure ℝ)
    [∀ N, IsFiniteMeasure (μ_N N)] [IsFiniteMeasure μ]
    (hweak : ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun N ↦ ∫ ω, f ω ∂(μ_N N)) atTop (nhds (∫ ω, f ω ∂μ)))
    (hunif : ∀ κ' : ℝ, 0 ≤ κ' → κ' < (2 * ((r : ℝ) - 1) * Jsite)⁻¹ →
      ∃ M > 0, ∀ N, Integrable (fun ω : ℝ ↦ Real.cosh ((β / 2 + κ') * ω)) (μ_N N) ∧
        ∫ ω : ℝ, Real.cosh ((β / 2 + κ') * ω) ∂(μ_N N) ≤ M)
    (b_inf : ℕ → ℝ) (hb_pos : ∀ h ≥ 1, 0 < b_inf h)
    (hb_lim : Tendsto (fun n : ℕ ↦ b_inf n / (n : ℝ)) atTop (nhds α))
    (hmom_eq : ∀ n : ℕ,
      ((jacobiMat (2 * n + 1) b_inf) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ)
    -- Scrambling hypotheses (H1_W) and (H1)
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
    let κ : ℝ := (2 * ((r : ℝ) - 1) * Jsite)⁻¹
    (lamW ≤ 2 * α ∧ 2 * α ≤ 2 * Real.pi / (β + 2 * κ) ∧ 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β) ∧
    (lamMSS ≤ 2 * α ∧ 2 * α ≤ 2 * Real.pi / (β + 2 * κ) ∧ 2 * Real.pi / (β + 2 * κ) < 2 * Real.pi / β) ∧
    (BddAbove { s : ℝ | 0 ≤ s ∧ Integrable (fun ω : ℝ ↦ Real.cosh (s * ω)) μ } →
      β / 2 + κ ≤ wightmanStripHalfWidth μ) := by
  intro κ
  have hr1 : (1 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hα_kms : 2 * α ≤ 2 * Real.pi / (β + 2 * κ) :=
    kms_rate_bound_from_thermo_limit_spectral_measure μ_N μ hweak hβ0 hκ hunif b_inf hb_pos hb_lim hmom_eq
  have hmain := theorem_1_3c_unconditional_family hr hJ hβ0 hβ hκ hα hγ hα_kms hCO_ge1
    hlamW hlamMSS E hE_ne hE_card h hh_supp hH hH_site U₀ hU₀ O hO hO_supp hOnorm hCO
    hb_lin hH1_W hH1_MSS
  refine ⟨hmain.1, hmain.2, fun hbdd ↦ ?_⟩
  refine wightmanStripHalfWidth_ge_beta_half_add_kappa μ hβ0.le hκ hbdd fun κ' hκ'_nn hκ'_lt ↦ ?_
  rcases hunif κ' hκ'_nn hκ'_lt with ⟨M, hM_pos, hM_unif⟩
  exact (theorem_1_2a_thermo_limit_eq_1_15_and_rW μ_N μ hweak (by linarith) hM_pos.le hM_unif).1

end HighTempChaosWithKMSDischarge

end KrylovChaos
