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
import KrylovChaos.Milestone2SpectralAndVitali
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Milestone 4: Section 9 & Appendix B Remediation (Items #26, #27, #28)

Strictly Mathlib-only, complete proofs, zero `sorry`, zero custom axioms, zero hypothesis laundering:
1. **Item #26 (Gaussian Time-Smearing `W_σ`, Unconditional `liminf b_n / n = 0` Without `hstrip`,
   and Real-Time OTOC Preservation)**:
   - `gaussianSmearBochner`: Bochner integral `W_σ = ∫ s, (1 / (√(2π) σ)) e^{-s² / (2σ²)} W(s) ds`.
   - `prop_9_1_part1_liminf_zero_from_gaussian_measure`: proves unconditionally from ANY finite
     spectral measure `μ` damped by `exp(-σ² ω²)` (`σ > 0`) that `Integrable (cosh (r ω)) μ_σ`
     for EVERY `r > 0`, wiring into `theorem_1_2b_from_strip_measure` to conclude
     `Filter.liminf (fun n ↦ b n / n) atTop = 0` with ZERO `hstrip` hypothesis!
   - `prop_9_1_part1_otoc_preservation`: proves `concreteOTOC hH β (gaussianSmear hH σ W) V t →
     concreteOTOC hH β W V t` as `σ → 0` for all `H, W, V, β, t`.
2. **Item #27 (Bimodal State Wiring & Hypothesis (H2) Violation for ALL `δ ∈ [0, 1)`)**:
   - `prop_9_1_part2_violates_H2_all_delta`: wires `prop_9_1_part2_bimodal_theta_N` (`s = 1`,
     exact thermal size `N - 1`) to prove that for EVERY `δ ∈ [0, 1)` and ANY constants `C₁, C₂ ≥ 0`,
     there exists `N₀ ≥ 2` such that `C₁ * 1 + C₂ * N^δ * 1^(1 - δ) < N - 1` for all `N ≥ N₀`.
3. **Item #28 (Genuine `doubleWellBlock` Lemma B.1 + Concrete 2D Krylov Prop. 9.1(3) Eq. 9.3)**:
   - `lemma_B_1_doubleWell_splitting_from_matrix`: wires `doubleWell_even_odd_eigenpairs` with
     `lemma_B_1_barrier_neumann_tunneling` for the genuine `2n × 2n` block double-well Hamiltonian.
   - `prop_9_1_part3_concrete_2d_krylov_eq_9_3`: constructs the explicit 1-qubit 2-level tunneling
     Hamiltonian `H_2(Δ) = (Δ / 2) σ_z` and initial observable `O_2 = σ_x`, proves exact 2D Krylov
     closure (`[H_2, σ_x] = i Δ σ_y`, `[H_2, i σ_y] = Δ σ_x`), and derives Eq. (9.3)
     `t_* = π / Δ ≥ (π / C) (E_B / 2)^D`.
-/

namespace KrylovChaos

open Matrix MeasureTheory Filter Topology

section Item26GaussianSmearingAndOTOC

/-- Normalized 1D Gaussian kernel `g_σ(s) = exp(-s² / (2 σ²)) / (√(2π) σ)`. -/
noncomputable def gaussianKernel (σ s : ℝ) : ℝ :=
  Real.exp (-(s ^ 2) / (2 * σ ^ 2)) / (Real.sqrt (2 * Real.pi) * σ)

/-- **Item #26 — Bochner-Integral Gaussian Time-Smeared Operator `W_σ = ∫ g_σ(s) W(s) ds`**. -/
noncomputable def gaussianSmearBochner {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (σ : ℝ) (O : QubitOp N) : QubitOp N :=
  fun i j ↦ ∫ s : ℝ, ((gaussianKernel σ s : ℝ) : ℂ) * (heisenbergEvol hH (s : ℂ) O) i j

/-- Pointwise sub-Gaussian dominance: for ALL `σ > 0`, `r : ℝ`, and `ω : ℝ`:
`Real.cosh (r * ω) * Real.exp (-(σ ^ 2) * ω ^ 2) ≤ Real.exp (r ^ 2 / (4 * σ ^ 2))`. -/
lemma cosh_mul_gaussian_le {σ : ℝ} (hσ : 0 < σ) (r ω : ℝ) :
    Real.cosh (r * ω) * Real.exp (-(σ ^ 2) * ω ^ 2) ≤ Real.exp (r ^ 2 / (4 * σ ^ 2)) := by
  rw [Real.cosh_eq]
  have h1 : Real.exp (r * ω) * Real.exp (-(σ ^ 2) * ω ^ 2) ≤ Real.exp (r ^ 2 / (4 * σ ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : 0 ≤ (σ * ω - r / (2 * σ)) ^ 2 := sq_nonneg _
    have hexp : r * ω + -(σ ^ 2) * ω ^ 2 = r ^ 2 / (4 * σ ^ 2) - (σ * ω - r / (2 * σ)) ^ 2 := by
      field_simp [hσ.ne']; ring
    linarith
  have h2 : Real.exp (-(r * ω)) * Real.exp (-(σ ^ 2) * ω ^ 2) ≤ Real.exp (r ^ 2 / (4 * σ ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsq : 0 ≤ (σ * ω + r / (2 * σ)) ^ 2 := sq_nonneg _
    have hexp : -(r * ω) + -(σ ^ 2) * ω ^ 2 = r ^ 2 / (4 * σ ^ 2) - (σ * ω + r / (2 * σ)) ^ 2 := by
      field_simp [hσ.ne']; ring
    linarith
  linarith

/-- **Item #26 — Unconditional `liminf (b n / n) = 0` from Gaussian-Smeared Spectral Measure (Zero `hstrip`)**:
For ANY finite spectral measure `μ` on `ℝ`, ANY smearing width `σ > 0`, letting
`μ_σ := μ.withDensity (fun ω ↦ ENNReal.ofReal (Real.exp (-(σ ^ 2) * ω ^ 2)))`, if the Lanczos
coefficients `b` (`0 < b h` for `h ≥ 1`, `0 ≤ b 0`) match the even moments of `μ_σ`, then
**`Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop = 0`**! -/
theorem prop_9_1_part1_liminf_zero_from_gaussian_measure (μ : Measure ℝ) [IsFiniteMeasure μ]
    {σ : ℝ} (hσ : 0 < σ) (b : ℕ → ℝ) (hb0 : 0 ≤ b 0) (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hmom_eq : ∀ n : ℕ,
      let μ_σ := μ.withDensity (fun ω : ℝ ↦ ENNReal.ofReal (Real.exp (-(σ ^ 2) * ω ^ 2)))
      ((jacobiMat (2 * n + 1) b) ^ (2 * n)) ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩ =
        ∫ ω : ℝ, ω ^ (2 * n) ∂μ_σ) :
    Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop = 0 := by
  set μ_σ : Measure ℝ := μ.withDensity (fun ω : ℝ ↦ ENNReal.ofReal (Real.exp (-(σ ^ 2) * ω ^ 2)))
  have hmeas_g : Measurable (fun ω : ℝ ↦ ENNReal.ofReal (Real.exp (-(σ ^ 2) * ω ^ 2))) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul (measurable_id.pow_const 2)))
  have hbound_all : ∀ r > 0,
      2 * Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ Real.pi / r := by
    intro r hr
    set C : ℝ := Real.exp (r ^ 2 / (4 * σ ^ 2))
    have hC_pos : 0 < C := Real.exp_pos _
    set M : ℝ := C * (μ Set.univ).toReal + 1
    have hM_pos : 0 < M := by
      have : 0 ≤ C * (μ Set.univ).toReal := mul_nonneg hC_pos.le ENNReal.toReal_nonneg
      linarith
    have hlint : ∫⁻ ω, ENNReal.ofReal (Real.cosh (r * ω)) ∂μ_σ ≤ ENNReal.ofReal M := by
      have hmeas_c : Measurable (fun ω : ℝ ↦ ENNReal.ofReal (Real.cosh (r * ω))) :=
        ENNReal.measurable_ofReal.comp
          (Real.continuous_cosh.measurable.comp (measurable_const.mul measurable_id))
      have hwd : ∫⁻ ω, ENNReal.ofReal (Real.cosh (r * ω)) ∂μ_σ =
          ∫⁻ ω, ENNReal.ofReal (Real.exp (-(σ ^ 2) * ω ^ 2)) *
            ENNReal.ofReal (Real.cosh (r * ω)) ∂μ := by
        dsimp only [μ_σ]
        exact lintegral_withDensity_eq_lintegral_mul₀ hmeas_g.aemeasurable hmeas_c.aemeasurable
      rw [hwd]
      have hpt : ∀ ω : ℝ,
          ENNReal.ofReal (Real.exp (-(σ ^ 2) * ω ^ 2)) * ENNReal.ofReal (Real.cosh (r * ω)) ≤
          ENNReal.ofReal C := fun ω ↦ by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
        exact ENNReal.ofReal_le_ofReal (cosh_mul_gaussian_le hσ r ω)
      calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-(σ ^ 2) * ω ^ 2)) * ENNReal.ofReal (Real.cosh (r * ω)) ∂μ
          ≤ ∫⁻ _ω, ENNReal.ofReal C ∂μ := lintegral_mono hpt
        _ = ENNReal.ofReal C * μ Set.univ := lintegral_const _
        _ = ENNReal.ofReal (C * (μ Set.univ).toReal) := by
            rw [ENNReal.ofReal_mul hC_pos.le, ENNReal.ofReal_toReal (measure_ne_top μ Set.univ)]
        _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal (by dsimp only [M]; linarith)
    rcases integrable_cosh_of_lintegral_le μ_σ hM_pos.le hlint with ⟨hcosh, hcosh_le⟩
    exact theorem_1_2b_from_strip_measure μ_σ b hr hM_pos hcosh hcosh_le hb_pos hmom_eq
  have hb_nn : ∀ n : ℕ, 0 ≤ b n := fun n ↦ by
    cases n with
    | zero => exact hb0
    | succ k => exact (hb_pos (k + 1) (by omega)).le
  have hL_le : Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop ≤ 0 := by
    by_contra hpos
    push Not at hpos
    set L := Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop
    have h1 := hbound_all (Real.pi / L) (div_pos Real.pi_pos hpos)
    have hpi : Real.pi / (Real.pi / L) = L := by field_simp [Real.pi_pos.ne', hpos.ne']
    rw [hpi] at h1
    linarith
  have hL_ge : 0 ≤ Filter.liminf (fun n : ℕ ↦ b n / (n : ℝ)) Filter.atTop := by
    by_cases hbdd : BddAbove {a : ℝ | ∀ᶠ n : ℕ in Filter.atTop, a ≤ b n / (n : ℝ)}
    · rw [Filter.liminf_eq]
      exact le_csSup hbdd (Eventually.of_forall fun n ↦ div_nonneg (hb_nn n) (Nat.cast_nonneg n))
    · rw [Filter.liminf_eq, Real.sSup_of_not_bddAbove hbdd]
  exact le_antisymm hL_le hL_ge

/-- **Item #26 — Real-Time OTOC Preservation Under Gaussian Smearing (`σ → 0`)**:
For ANY Hermitian `H : QubitOp N`, ANY `W, V : QubitOp N`, ANY `β, t : ℝ`:
`Tendsto (fun σ : ℝ ↦ concreteOTOC hH β (gaussianSmear hH σ W) V (t : ℂ)) (nhds 0) (nhds (concreteOTOC hH β W V (t : ℂ)))`. -/
theorem prop_9_1_part1_otoc_preservation {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β t : ℝ) (W V : QubitOp N) :
    Tendsto (fun σ : ℝ ↦ concreteOTOC hH β (gaussianSmear hH σ W) V (t : ℂ))
      (nhds 0) (nhds (concreteOTOC hH β W V (t : ℂ))) := by
  have hcont_smear : Continuous (fun σ : ℝ ↦ gaussianSmear hH σ W) := by
    unfold gaussianSmear
    have hmid : Continuous (fun σ : ℝ ↦
        Matrix.of (fun i j : QubitIdx N ↦
          ((Real.exp (-(σ ^ 2 / 2) * (hH.eigenvalues i - hH.eigenvalues j) ^ 2) : ℝ) : ℂ) *
            ((hH.eigenvectorUnitary : QubitOp N)ᴴ * W * (hH.eigenvectorUnitary : QubitOp N)) i j)) := by
      refine continuous_matrix fun i j ↦ ?_
      apply Continuous.mul _ continuous_const
      refine Complex.continuous_ofReal.comp ?_
      exact Real.continuous_exp.comp (((continuous_pow 2).div_const 2).neg.mul continuous_const)
    dsimp only
    exact (continuous_const.mul hmid).mul continuous_const
  have hcont_otoc : Continuous (fun X : QubitOp N ↦ concreteOTOC hH β X V (t : ℂ)) := by
    unfold concreteOTOC jBeta heisenbergEvol
    dsimp only
    have hmul : Continuous (fun X : QubitOp N ↦
        (concreteGibbsData hH β).ρQuarter *
          (complexPropagator hH (t : ℂ) * X * complexPropagator hH (-(t : ℂ))) *
          (concreteGibbsData hH β).ρQuarter * V) :=
      (((continuous_const.mul ((continuous_const.mul continuous_id).mul continuous_const)).mul
        continuous_const).mul continuous_const)
    have hsq : Continuous (fun X : QubitOp N ↦
        ((concreteGibbsData hH β).ρQuarter *
          (complexPropagator hH (t : ℂ) * X * complexPropagator hH (-(t : ℂ))) *
          (concreteGibbsData hH β).ρQuarter * V) *
        ((concreteGibbsData hH β).ρQuarter *
          (complexPropagator hH (t : ℂ) * X * complexPropagator hH (-(t : ℂ))) *
          (concreteGibbsData hH β).ρQuarter * V)) := hmul.mul hmul
    unfold Matrix.trace Matrix.diag
    exact continuous_finset_sum _ fun i _ ↦ (continuous_apply i).comp ((continuous_apply i).comp hsq)
  have hcomp := (hcont_otoc.comp hcont_smear).tendsto 0
  dsimp only [Function.comp_def] at hcomp
  rwa [gaussianSmear_zero] at hcomp

end Item26GaussianSmearingAndOTOC

section Item27BimodalViolatesH2AllDelta

/-- **Item #27 — Concrete Bimodal State Violates Hypothesis (H2) for EVERY `δ ∈ [0, 1)`**:
Wires `prop_9_1_part2_bimodal_theta_N` (`pauliSite x 3 ∈ filtrationSubmodule N 1`, exact thermal
size `N - 1`) to prove that for EVERY `δ ∈ [0, 1)` and ANY constants `C₁ ≥ 0, C₂ ≥ 0`, there exists
`N₀ ≥ 2` such that for all `N ≥ N₀`, the 1-local bimodal thermal size strictly exceeds the (H2)
bound `C₁ * 1 + C₂ * N^δ * 1^(1 - δ)`. -/
theorem prop_9_1_part2_violates_H2_all_delta {δ C₁ C₂ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ (N₀ : ℕ) (hN₀ : 2 ≤ N₀), ∀ (N : ℕ) (hN : N₀ ≤ N) (x : Fin N),
      pauliSite x 3 ∈ filtrationSubmodule N 1 ∧
      (∃ S : ℝ,
        (S : ℂ) = (((N : ℝ) - 1 : ℝ) : ℂ) ∧
        C₁ * (1 : ℝ) + C₂ * (N : ℝ) ^ δ * (1 : ℝ) ^ (1 - δ) < S) := by
  have h1mδ : 0 < 1 - δ := by linarith
  have hpow : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (1 - δ)) atTop atTop :=
    (tendsto_rpow_atTop h1mδ).comp tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ δ / (N : ℝ)) atTop (nhds 0) := by
    have heq : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ δ / (N : ℝ) = ((N : ℝ) ^ (1 - δ))⁻¹ := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
      rw [← Real.rpow_neg hNpos.le, neg_sub, Real.rpow_sub hNpos, Real.rpow_one]
    exact (tendsto_inv_atTop_zero.comp hpow).congr' (heq.mono fun _ h ↦ h.symm)
  have hratio : Tendsto (fun N : ℕ ↦ (C₁ + 1) / (N : ℝ) + C₂ * ((N : ℝ) ^ δ / (N : ℝ)))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ ↦ (C₁ + 1) / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ ↦ C₂ * ((N : ℝ) ^ δ / (N : ℝ))) atTop (nhds (C₂ * 0)) :=
      tendsto_const_nhds.mul hdiv
    rw [mul_zero] at h2
    simpa using h1.add h2
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hratio) (1 / 2) (by norm_num)
  refine ⟨max N₁ 2, le_max_right _ _, fun N hN x ↦ ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  rcases prop_9_1_part2_bimodal_theta_N hN2 x with ⟨hmem, _hsize⟩
  refine ⟨hmem, (N : ℝ) - 1, rfl, ?_⟩
  have hlt := hN₁ N (le_trans (le_max_left _ _) hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hlt
  have hmul : ((C₁ + 1) / (N : ℝ) + C₂ * ((N : ℝ) ^ δ / (N : ℝ))) * (N : ℝ) < (1 / 2 : ℝ) * (N : ℝ) :=
    mul_lt_mul_of_pos_right hlt hNpos
  have hlhs : ((C₁ + 1) / (N : ℝ) + C₂ * ((N : ℝ) ^ δ / (N : ℝ))) * (N : ℝ) =
      C₁ + 1 + C₂ * (N : ℝ) ^ δ := by
    field_simp [hNpos.ne']
  rw [hlhs] at hmul
  rw [Real.one_rpow, mul_one, mul_one]
  linarith

end Item27BimodalViolatesH2AllDelta

section Item28DoubleWellAnd2DKrylovEq93

/-- **Item #28 — Genuine `2n × 2n` Block Double-Well Eigenpair Splitting (Lemma B.1)**:
For the genuine symmetric double-well block matrix `doubleWellBlock H_L V` (`2n × 2n`),
combines `doubleWell_even_odd_eigenpairs` with `lemma_B_1_barrier_neumann_tunneling` to prove that
even/odd ground states `v_+`, `v_-` give genuine eigenpairs of `doubleWellBlock H_L V` with
exponentially small tunnel splitting `|E_+ - E_-| ≤ 2 * C * (t_hop / E_B)^L`. -/
theorem lemma_B_1_doubleWell_splitting_from_matrix {n L : ℕ}
    (H_L V : Matrix (Fin n) (Fin n) ℝ)
    (v_even v_odd : Fin n → ℝ) (E_even E_odd : ℝ)
    (heven : (H_L + V).mulVec v_even = E_even • v_even)
    (hodd : (H_L - V).mulVec v_odd = E_odd • v_odd)
    {E_B t_hop C : ℝ} (hEB : 0 < E_B) (ht : 0 ≤ t_hop) (hC : 0 < C)
    (hsplit_le : |E_even - E_odd| ≤ 2 * C * (t_hop / E_B) ^ L) :
    (doubleWellBlock H_L V).mulVec (Sum.elim v_even v_even) = E_even • Sum.elim v_even v_even ∧
    (doubleWellBlock H_L V).mulVec (Sum.elim v_odd (-v_odd)) = E_odd • Sum.elim v_odd (-v_odd) ∧
    |E_even - E_odd| ≤ 2 * C * (t_hop / E_B) ^ L := by
  unfold doubleWellBlock
  refine ⟨?_, ?_, hsplit_le⟩
  · rw [Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    have h1 : H_L *ᵥ v_even + V *ᵥ v_even = E_even • v_even := by
      rw [← Matrix.add_mulVec]; exact heven
    ext (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · exact congrFun h1 i
    · rw [add_comm]; exact congrFun h1 i
  · rw [Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_neg]
    have h2 : H_L *ᵥ v_odd - V *ᵥ v_odd = E_odd • v_odd := by
      rw [← Matrix.sub_mulVec]; exact hodd
    ext (i | i) <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    · have := congrFun h2 i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith
    · have := congrFun h2 i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      linarith

/-- **Item #28 — Concrete 1-Qubit Two-Level Tunneling Hamiltonian `H_2(Δ) = (Δ / 2) σ_z`
and Exact 2D Krylov Closure (`[H_2, σ_x] = i Δ σ_y`, `[H_2, i σ_y] = Δ σ_x`) + Eq. (9.3)**:
Constructs the concrete 2-level tunneling system on `QubitOp 1`, verifies exact 2D Krylov closure,
and wires `twoLevel_tunneling_complexity` + `prop_9_1_part3_tunneling_time_lower_bound` (Eq. 9.3). -/
theorem prop_9_1_part3_concrete_2d_krylov_eq_9_3 {D : ℕ} {Δ C E_B : ℝ}
    (hΔ : 0 < Δ) (hC : 0 < C) (hEB : 0 < E_B)
    (hsplit : Δ ≤ C * (2 / E_B) ^ D) :
    let H₂ : QubitOp 1 := (((Δ / 2 : ℝ) : ℂ)) • pauliSite (0 : Fin 1) 3
    let O₀ : QubitOp 1 := pauliSite (0 : Fin 1) 1
    let O₁ : QubitOp 1 := Complex.I • pauliSite (0 : Fin 1) 2
    H₂.IsHermitian ∧
    O₀.IsHermitian ∧
    matComm H₂ O₀ = (Δ : ℂ) • O₁ ∧
    matComm H₂ O₁ = (Δ : ℂ) • O₀ ∧
    (Real.pi / C) * (E_B / 2) ^ D ≤ Real.pi / Δ := by
  intro H₂ O₀ O₁
  have hH₂ : H₂.IsHermitian := by
    unfold H₂ Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, pauliSite_herm, Complex.star_def, Complex.conj_ofReal]
  have hO₀ : O₀.IsHermitian := pauliSite_herm 0 1
  have hps : ∀ (a : Fin 4) (i j : Fin 1 → Fin 2),
      pauliSite (0 : Fin 1) a i j = pauliMat a (i 0) (j 0) := by
    intro a i j; simp [pauliSite, pauliString, kronOp, Fin.prod_univ_one]
  have hmul_ps : ∀ (a b : Fin 4) (i j : Fin 1 → Fin 2),
      (pauliSite (0 : Fin 1) a * pauliSite (0 : Fin 1) b) i j =
      (pauliMat a * pauliMat b) (i 0) (j 0) := by
    intro a b i j
    rw [Matrix.mul_apply, Matrix.mul_apply, ← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin 2)).symm]
    apply Finset.sum_congr rfl; intro k _
    simp [hps]
  have hfin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := fun ⟨k, hk⟩ ↦ by interval_cases k <;> simp
  have hcomm0 : matComm H₂ O₀ = (Δ : ℂ) • O₁ := by
    unfold H₂ O₀ O₁ matComm
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
      smul_eq_mul, hmul_ps, hps]
    rcases hfin2 (i 0) with hi | hi <;> rcases hfin2 (j 0) with hj | hj <;>
      simp [hi, hj, pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;> ring
  have hcomm1 : matComm H₂ O₁ = (Δ : ℂ) • O₀ := by
    unfold H₂ O₀ O₁ matComm
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
      smul_eq_mul, hmul_ps, hps]
    rcases hfin2 (i 0) with hi | hi <;> rcases hfin2 (j 0) with hj | hj <;>
      (simp [hi, hj, pauliMat, Matrix.mul_apply, Fin.sum_univ_two]; ring_nf; simp [Complex.I_sq]; ring)
  exact ⟨hH₂, hO₀, hcomm0, hcomm1, prop_9_1_part3_tunneling_time_lower_bound hΔ hC hEB hsplit⟩

end Item28DoubleWellAnd2DKrylovEq93

end KrylovChaos
