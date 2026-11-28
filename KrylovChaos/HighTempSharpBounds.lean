/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Milestone3Sections678
import KrylovChaos.Theorem12Concrete
import KrylovChaos.MultiSiteCommutator
import KrylovChaos.ArakiOneDimAllTemp
import KrylovChaos.HighTempParams
import KrylovChaos.EntropicDecoupling
import KrylovChaos.Milestone1CoreRemediation
import KrylovChaos.Milestone1Majorana
import KrylovChaos.TimeOrderedOTOC
import Mathlib.Tactic

/-!
# Sharp High-Temperature Bounds, Multi-Site Conditioning, Ising Operator Bridge & Extended Domains

Provides sharp and standalone operator-level formulations across Sections 2, 4, 6, 7, and 8:
1. `prop_6_2_sharp_r_local_high_temp`: sharp Proposition 6.2 prefactor
   `(3 / 2) * (1 - β / (4 * κ))⁻¹ ^ 2` on the full domain `0 ≤ β < 4 * κ`
   where `κ = (2 * (r - 1) * Jsite)⁻¹`.
2. `lemma_7_3_part1_multisite_eq_7_11`: literal multi-site Lemma 7.3(1) (Eq. 7.11) with factor
   `4 * 9 ^ |U|` for arbitrary subsets `U : Finset (Fin N)` and `W ∈ supportedOn U`.
3. `prop_8_1_araki_1d_complete`: complete Proposition 8.1 conjoining the all-temperature 1D Araki
   bound with `(A | 𝒬̃^{(β)} A)_β^W ≤ ∑ x, ‖𝒮_x(A)‖_{β,W}²`.
4. `lemma_8_2_ising_hs_mixture`, `isingPhiMaxExact_le_linear`, `prop_8_3_ising_explicit_eq_8_4`,
   `diagIsing_glauberGen_eq_classical_dirichlet`, `diagIsing_wightmanQ_eq_classical_degreeFiltrationQ`,
   and `prop_8_3_quantum_diag_ising_reverse_poincare`: standalone Lemma 8.2 Hubbard–Stratonovich
   convex mixture, explicit linear bound `Φ_max(β) ≤ β H_max + (Δ / 2) log 2` for Eq. (8.4), and
   exact diagonal Ising operator identities bridging `𝒬̃^{(β)}` and `𝒬^{(β)}` to the classical
   Glauber Dirichlet form and degree filtration.
5. `theorem_1_1b_family_concrete_qubit_bounded_s` and `theorem_1_1b_family_majorana_2n_normalized`:
   Theorem 1.1(b) with static hypothesis `(H2)` quantified strictly over `1 ≤ s ≤ N` (qubits) and
   `1 ≤ s ≤ 2 * n` with `2 * n`-normalized scrambling times (Majoranas).
6. `prop_6_4_part2_extended`: Proposition 6.4(2) (Eq. 6.7) on the full extended high-temperature
   domain `0 ≤ β ≤ 1 / (8 * e² * r * Jsite)`.
7. `lemma_2_1_qubit_exp_bound` and `theorem_1_3a_high_temp_two_sided`: standalone composed
   Lemma 2.1 exponential norm bound and two-sided Theorem 1.3(a) (Eq. 1.20).
-/

namespace KrylovChaos

open Matrix

section SharpProp62AndMultiSiteLemma73

/-- Single-site Pauli `pauliSite x α.succ` is supported on `{x}`. -/
private lemma pauliSite_mem_supportedOn_singleton {N : ℕ} (x : Fin N) (α : Fin 3) :
    pauliSite x α.succ ∈ supportedOn ({x} : Finset (Fin N)) := by
  have h1 : pauliSite x α.succ = pauliString (Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x α.succ) := by
    unfold pauliSite pauliString
    rfl
  rw [h1]
  apply Submodule.subset_span
  refine ⟨Function.update (fun _ : Fin N ↦ (0 : Fin 4)) x α.succ, ?_, rfl⟩
  intro y hy
  have hne : y ≠ x := by simpa [Finset.mem_singleton] using hy
  simp [Function.update, hne]

/-- **Proposition 6.2 (Sharp High-Temperature `3/2` Prefactor on `0 ≤ β < 4 * κ`)**:
For any `r`-local Hermitian qubit Hamiltonian `H = ∑ X ∈ E, h X` (`r ≥ 2`, site norm `≤ Jsite`),
any `0 ≤ β < 4 * κ` where `κ = (2 * (r - 1) * Jsite)⁻¹`, and EVERY observable `A : QubitOp N`:
`otocCW G A ≤ (3 / 2) * (1 - β / (4 * κ))⁻¹ ^ 2 * Re (A | 𝒬̃^{(β)} A)_β^W`. -/
theorem prop_6_2_sharp_r_local_high_temp {N r : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {Jsite β : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    (hβ0 : 0 ≤ β)
    (hβ_lt : β < 4 * (1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)))
    (A : QubitOp N) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    let G := concreteGibbsData hH β
    otocCW G A ≤ (3 / 2 : ℝ) * (1 - β / (4 * κ))⁻¹ ^ 2 *
      (gibbsWightmanInner G A (quantumGlauberGen G A)).re := by
  intro κ G
  have hr1_ge1 : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
  have hκ_pos : 0 < κ := by dsimp only [κ]; positivity
  have hκ'_lt : β / 4 < κ := by dsimp only [κ] at hβ_lt ⊢; linarith
  have h1sub_pos : 0 < 1 - β / (4 * κ) := by
    have hdiv : β / (4 * κ) < 1 := (div_lt_one (by positivity)).mpr hβ_lt
    linarith
  have h1sub_le1 : 1 - β / (4 * κ) ≤ 1 := by
    have : 0 ≤ β / (4 * κ) := by positivity
    linarith
  have hM_nn : 0 ≤ (1 - β / (4 * κ))⁻¹ := inv_nonneg.mpr h1sub_pos.le
  refine prop_6_2_exact_three_halves hH β hM_nn (fun x α ↦ ?_) A
  have hneg : opNorm (heisenbergEvol hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) (pauliSite x α.succ)) ≤
      (1 - β / (4 * κ))⁻¹ := by
    have hbd := theorem_1_2a_concrete_eq54_r_local_norm_bound hr E hcard h hsupp hH hJ hsite
      (U₀ := {x}) (sW := 1) (by simp) (pauliSite_mem_supportedOn_singleton x α)
      (by positivity : 0 ≤ β / 4) hκ'_lt
    have hq_eq : (β / 4) / κ = β / (4 * κ) := by ring
    have hrpow_le : (1 - β / (4 * κ)) ^ (-((1 : ℝ) / ((r - 1 : ℕ) : ℝ))) ≤ (1 - β / (4 * κ))⁻¹ := by
      rw [← Real.rpow_neg_one (1 - β / (4 * κ))]
      apply Real.rpow_le_rpow_of_exponent_ge h1sub_pos h1sub_le1
      have hdiv_le : (1 : ℝ) / ((r - 1 : ℕ) : ℝ) ≤ 1 := div_le_one_of_le₀ hr1_ge1 (by positivity)
      linarith
    have hpauli := opNorm_pauliSite_le x α
    have hbd' : opNorm (heisenbergEvol hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) (pauliSite x α.succ)) ≤
        opNorm (pauliSite x α.succ) * (1 - β / (4 * κ)) ^ (-((1 : ℝ) / ((r - 1 : ℕ) : ℝ))) := by
      dsimp only at hbd
      change opNorm (heisenbergEvol hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) (pauliSite x α.succ)) ≤
        opNorm (pauliSite x α.succ) * (1 - (β / 4) / κ) ^ (-(((1 : ℕ) : ℝ) / ((r - 1 : ℕ) : ℝ))) at hbd
      rwa [hq_eq, Nat.cast_one] at hbd
    calc opNorm (heisenbergEvol hH (-(Complex.I * ((β / 4 : ℝ) : ℂ))) (pauliSite x α.succ))
        ≤ opNorm (pauliSite x α.succ) * (1 - β / (4 * κ)) ^ (-((1 : ℝ) / ((r - 1 : ℕ) : ℝ))) := hbd'
      _ ≤ 1 * (1 - β / (4 * κ)) ^ (-((1 : ℝ) / ((r - 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right hpauli (Real.rpow_nonneg h1sub_pos.le _)
      _ = (1 - β / (4 * κ)) ^ (-((1 : ℝ) / ((r - 1 : ℕ) : ℝ))) := one_mul _
      _ ≤ (1 - β / (4 * κ))⁻¹ := hrpow_le
  have hpos : opNorm (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) (pauliSite x α.succ)) ≤
      (1 - β / (4 * κ))⁻¹ := by
    have hW_herm : (pauliSite x α.succ).IsHermitian := pauliSite_herm x α.succ
    have hconj := heisenbergEvol_conjTranspose_of_herm hH hW_herm (Complex.I * ((β / 4 : ℝ) : ℂ))
    have hstar : starRingEnd ℂ (Complex.I * ((β / 4 : ℝ) : ℂ)) = -(Complex.I * ((β / 4 : ℝ) : ℂ)) := by
      simp
    rw [hstar] at hconj
    rw [← opNorm_conjTranspose, hconj]
    exact hneg
  exact ⟨hpos, hneg⟩

/-- **Lemma 7.3(1) (Literal Multi-Site Conditioning Bound, Eq. 7.11)**:
For ANY `s, s' : Fin N → Fin 6`, ANY subset `U : Finset (Fin N)`, ANY `W ∈ supportedOn U`,
and ANY `A : QubitOp N`:
`prodDepolNormSq s s' (matComm A W) ≤ 4 * 9 ^ |U| * (opNorm W) ^ 2 * ∑ y ∈ U, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A`. -/
theorem lemma_7_3_part1_multisite_eq_7_11 {N : ℕ} (s s' : Fin N → Fin 6)
    {U : Finset (Fin N)} {W : QubitOp N} (hW : W ∈ supportedOn U) (A : QubitOp N) :
    prodDepolNormSq s s' (matComm A W) ≤
      4 * (9 : ℝ) ^ U.card * (opNorm W) ^ 2 *
        ∑ y ∈ U, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A := by
  have h3 := prodDepolNormSq_matComm_supportedOn_le s s' hW A
  have hpow : (3 : ℝ) ^ U.card ≤ (9 : ℝ) ^ U.card := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hsum_nn : 0 ≤ ∑ y ∈ U, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A :=
    Finset.sum_nonneg fun y _ ↦ by unfold prodDepolDistSq; apply Real.sInf_nonneg; rintro _ ⟨_, _, rfl⟩; exact prodDepolNormSq_nonneg s s' _
  calc prodDepolNormSq s s' (matComm A W)
      ≤ 4 * (3 : ℝ) ^ U.card * (opNorm W) ^ 2 *
          ∑ y ∈ U, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A := h3
    _ ≤ 4 * (9 : ℝ) ^ U.card * (opNorm W) ^ 2 *
          ∑ y ∈ U, prodDepolDistSq s s' (singleSiteTrivialSubmodule N y) A := by
        gcongr

end SharpProp62AndMultiSiteLemma73

section Prop81Complete

/-- **Proposition 8.1 (Complete All-Temperature 1D Finite-Range Bounds, Eq. 8.1)**:
Conjoins the all-temperature 1D Araki bound on `otocCW` with the universal single-site bound
`Re (A | 𝒬̃^{(β)} A)_β^W ≤ ∑ x, ‖𝒮_x(A)‖_{β,W}²` for every `β : ℝ` and every `A : QubitOp N`. -/
theorem prop_8_1_araki_1d_complete {N r : ℕ} (hr : 1 ≤ r)
    (E : Finset (Finset (Fin N))) (h1d : is1DFiniteRange N r E)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {J : ℝ} (hJ : 0 ≤ J)
    (hsite : ∀ y : Fin N, ∑ X ∈ E.filter (fun X ↦ y ∈ X), opNorm (h X) ≤ J)
    (β : ℝ) (A : QubitOp N) :
    let G := concreteGibbsData hH β
    otocCW G A ≤ (3 / 2 : ℝ) * (araki1DM β r J) ^ 2 *
      (gibbsWightmanInner G A (quantumGlauberGen G A)).re ∧
    (gibbsWightmanInner G A (quantumGlauberGen G A)).re ≤
      ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x A) ∧
    (∀ C_RP : ℝ,
      (gibbsWightmanInner G A (quantumGlauberGen G A)).re ≤
        C_RP * (gibbsWightmanInner G A (wightmanQ G A)).re →
      otocCW G A ≤ (3 / 2 : ℝ) * (araki1DM β r J) ^ 2 * C_RP *
        (gibbsWightmanInner G A (wightmanQ G A)).re) := by
  have h1 := prop_8_1_araki_1d_unconditional hr E h1d h hsupp hH hJ hsite β A
  have h2 := theorem_1_3a_lower_concrete (concreteGibbsData hH β) A
  exact ⟨h1.1, h2, h1.2⟩

end Prop81Complete

section ClassicalIsingLemma82AndQuantumBridge

/-- Elementary upper bound on the discrete Hubbard–Stratonovich parameter:
`isingHSParam β Jij ≤ β * |Jij| + (1 / 2) * Real.log 2` for all `β ≥ 0`. -/
lemma isingHSParam_le_linear {β : ℝ} (hβ : 0 ≤ β) (Jij : ℝ) :
    isingHSParam β Jij ≤ β * |Jij| + (1 / 2 : ℝ) * Real.log 2 := by
  unfold isingHSParam
  have hexp_pos : 0 < Real.exp (2 * β * |Jij|) := Real.exp_pos _
  have hsqrt_le : Real.sqrt (Real.exp (4 * β * |Jij|) - 1) ≤ Real.exp (2 * β * |Jij|) := by
    rw [Real.sqrt_le_left hexp_pos.le]
    have hsq : Real.exp (2 * β * |Jij|) ^ 2 = Real.exp (4 * β * |Jij|) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    linarith
  have harg_pos : 0 < Real.exp (2 * β * |Jij|) + Real.sqrt (Real.exp (4 * β * |Jij|) - 1) := by
    linarith [Real.sqrt_nonneg (Real.exp (4 * β * |Jij|) - 1)]
  have hlog_le : Real.log (Real.exp (2 * β * |Jij|) + Real.sqrt (Real.exp (4 * β * |Jij|) - 1)) ≤
      Real.log (2 * Real.exp (2 * β * |Jij|)) :=
    Real.log_le_log harg_pos (by linarith)
  rw [Real.log_mul (by norm_num) hexp_pos.ne', Real.log_exp] at hlog_le
  linarith

/-- Explicit linear bound on `isingPhiMaxExact`:
if every vertex `i : Fin N` has incident degree `≤ Δ` (counting edges `e : IsingEdge N` with
`e.1.1 = i ∨ e.1.2 = i`) and local field + coupling sum `|hfield i| + ∑_{e ∋ i} |J_e| ≤ H_max`,
then `isingPhiMaxExact β J hfield ≤ β * H_max + ((Δ : ℝ) / 2) * Real.log 2`. -/
theorem isingPhiMaxExact_le_linear {N Δ : ℕ} {β H_max : ℝ} (hβ : 0 ≤ β) (hHmax : 0 ≤ H_max)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ)
    (hdeg : ∀ i : Fin N,
      (∑ e : IsingEdge N, ((if e.1.1 = i then (1 : ℝ) else 0) + (if e.1.2 = i then (1 : ℝ) else 0))) ≤ (Δ : ℝ))
    (hloc : ∀ i : Fin N,
      |hfield i| +
        ∑ e : IsingEdge N,
          ((if e.1.1 = i then |J e.1.1 e.1.2| else 0) + (if e.1.2 = i then |J e.1.1 e.1.2| else 0)) ≤ H_max) :
    isingPhiMaxExact β J hfield ≤ β * H_max + ((Δ : ℝ) / 2) * Real.log 2 := by
  unfold isingPhiMaxExact
  have hB_nn : 0 ≤ β * H_max + ((Δ : ℝ) / 2) * Real.log 2 := by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hfold_le : ∀ (S : Finset (Fin N)) (g : Fin N → ℝ) (B : ℝ),
      0 ≤ B → (∀ a ∈ S, g a ≤ B) → S.fold max 0 g ≤ B := by
    intro S g B hB hg
    classical
    induction S using Finset.induction_on with
    | empty => simpa using hB
    | insert a t hat ih =>
      rw [Finset.fold_insert hat]
      exact max_le (hg a (Finset.mem_insert_self a t))
        (ih fun x hx ↦ hg x (Finset.mem_insert_of_mem hx))
  refine hfold_le Finset.univ _ _ hB_nn fun i _ ↦ ?_
  have hsum_le : ∑ e : IsingEdge N,
        ((if e.1.1 = i then isingHSParam β (J e.1.1 e.1.2) else 0) +
         (if e.1.2 = i then isingHSParam β (J e.1.1 e.1.2) else 0)) ≤
      β * (∑ e : IsingEdge N,
        ((if e.1.1 = i then |J e.1.1 e.1.2| else 0) + (if e.1.2 = i then |J e.1.1 e.1.2| else 0))) +
      ((1 / 2 : ℝ) * Real.log 2) *
        (∑ e : IsingEdge N, ((if e.1.1 = i then (1 : ℝ) else 0) + (if e.1.2 = i then (1 : ℝ) else 0))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro e _
    have hc := isingHSParam_le_linear hβ (J e.1.1 e.1.2)
    split_ifs <;> linarith
  have hloc_i := mul_le_mul_of_nonneg_left (hloc i) hβ
  have hdeg_i := mul_le_mul_of_nonneg_left (hdeg i) (show 0 ≤ (1 / 2 : ℝ) * Real.log 2 by
    have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num); positivity)
  linarith

/-- **Lemma 8.2 (Standalone Discrete Hubbard–Stratonovich Product-Bernoulli Mixture)**:
For ANY `N : ℕ`, `β ≥ 0`, signed coupling matrix `J : Fin N → Fin N → ℝ`, and external field
`hfield : Fin N → ℝ`, there exist explicit nonnegative mixture weights `w : (IsingEdge N → Bool) → ℝ`
summing to `1` and effective fields `h_eff : (IsingEdge N → Bool) → Fin N → ℝ` with
`|h_eff ξ i| ≤ isingPhiMaxExact β J hfield` such that
`isingGibbsMeasure β J hfield σ = ∑ ξ, w ξ * prodBernoulli (h_eff ξ) σ` for every `σ : SpinConfig N`. -/
theorem lemma_8_2_ising_hs_mixture {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ) :
    ∃ (w : (IsingEdge N → Bool) → ℝ) (h_eff : (IsingEdge N → Bool) → Fin N → ℝ),
      (∀ ξ, 0 ≤ w ξ) ∧
      (∑ ξ : IsingEdge N → Bool, w ξ = 1) ∧
      (∀ ξ i, |h_eff ξ i| ≤ isingPhiMaxExact β J hfield) ∧
      (∀ σ : SpinConfig N, isingGibbsMeasure β J hfield σ =
        ∑ ξ : IsingEdge N → Bool, w ξ * prodBernoulli (h_eff ξ) σ) := by
  let Ξ := IsingEdge N → Bool
  let c : IsingEdge N → ℝ := fun e ↦ isingHSParam β (J e.1.1 e.1.2)
  let sgn : IsingEdge N → ℝ := fun e ↦ if 0 ≤ J e.1.1 e.1.2 then 1 else -1
  let h_eff : Ξ → Fin N → ℝ := fun ξ i ↦
    β * hfield i +
    ∑ e : IsingEdge N,
      ((if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
       (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0))
  let Z_ising : ℝ := ∑ τ : SpinConfig N, Real.exp (-β * isingHamiltonianStrict J hfield τ)
  have hZ_pos : 0 < Z_ising :=
    Finset.sum_pos (fun τ _ ↦ Real.exp_pos _) ⟨fun _ ↦ false, Finset.mem_univ _⟩
  let C_pre : ℝ := ∏ e : IsingEdge N, (Real.exp (-β * |J e.1.1 e.1.2|) * (1 / 2 : ℝ))
  have hC_pos : 0 < C_pre := Finset.prod_pos fun e _ ↦ mul_pos (Real.exp_pos _) (by norm_num)
  let w : Ξ → ℝ := fun ξ ↦ (C_pre / Z_ising) * ∏ i : Fin N, (2 * Real.cosh (h_eff ξ i))
  have hw_nn : ∀ ξ : Ξ, 0 ≤ w ξ := fun ξ ↦
    mul_nonneg (div_nonneg hC_pos.le hZ_pos.le)
      (Finset.prod_nonneg fun i _ ↦ by linarith [Real.cosh_pos (h_eff ξ i)])
  have hh_le : ∀ (ξ : Ξ) (i : Fin N), |h_eff ξ i| ≤ isingPhiMaxExact β J hfield := by
    intro ξ i
    have h1 : |h_eff ξ i| ≤
        β * |hfield i| + ∑ e : IsingEdge N,
          ((if e.1.1 = i then c e else 0) + (if e.1.2 = i then c e else 0)) := by
      dsimp only [h_eff]
      calc |β * hfield i + ∑ e : IsingEdge N,
              ((if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
               (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0))|
          ≤ |β * hfield i| + |∑ e : IsingEdge N,
              ((if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
               (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0))| := abs_add_le _ _
        _ ≤ β * |hfield i| + ∑ e : IsingEdge N,
              |(if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
               (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0)| := by
              rw [abs_mul, abs_of_nonneg hβ]
              exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
        _ ≤ β * |hfield i| + ∑ e : IsingEdge N,
              ((if e.1.1 = i then c e else 0) + (if e.1.2 = i then c e else 0)) := by
              apply add_le_add le_rfl
              apply Finset.sum_le_sum; intro e _
              have hc_nn : 0 ≤ c e := isingHSParam_nonneg hβ _
              have h1e : |(if e.1.1 = i then (if ξ e then c e else -c e) else 0)| ≤
                  if e.1.1 = i then c e else 0 := by split_ifs <;> simp [abs_of_nonneg hc_nn]
              have h2e : |(if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0)| ≤
                  if e.1.2 = i then c e else 0 := by
                have hsgn : |sgn e| = 1 := by dsimp only [sgn]; split_ifs <;> norm_num
                split_ifs <;> simp [abs_mul, hsgn, abs_of_nonneg hc_nn]
              exact le_trans (abs_add_le _ _) (add_le_add h1e h2e)
    have hfold_le : β * |hfield i| + ∑ e : IsingEdge N,
        ((if e.1.1 = i then c e else 0) + (if e.1.2 = i then c e else 0)) ≤
        isingPhiMaxExact β J hfield := by
      unfold isingPhiMaxExact
      have hgen : ∀ (S : Finset (Fin N)) (g : Fin N → ℝ), ∀ a ∈ S, g a ≤ S.fold max 0 g := by
        intro S g; classical
        induction S using Finset.induction_on with
        | empty => intro a ha; exact absurd ha (Finset.notMem_empty _)
        | insert b t hbt ih =>
            intro a ha; rw [Finset.fold_insert hbt]
            rcases Finset.mem_insert.mp ha with rfl | hat
            · exact le_max_left _ _
            · exact le_trans (ih a hat) (le_max_right _ _)
      exact hgen Finset.univ (fun j ↦ β * |hfield j| + ∑ e : IsingEdge N,
        ((if e.1.1 = j then isingHSParam β (J e.1.1 e.1.2) else 0) +
         (if e.1.2 = j then isingHSParam β (J e.1.1 e.1.2) else 0))) i (Finset.mem_univ i)
    exact le_trans h1 hfold_le
  have hmix : ∀ σ : SpinConfig N, isingGibbsMeasure β J hfield σ =
      ∑ ξ : Ξ, w ξ * prodBernoulli (h_eff ξ) σ := by
    intro σ
    have hprod_cancel : ∀ ξ : Ξ, w ξ * prodBernoulli (h_eff ξ) σ =
        (C_pre / Z_ising) * Real.exp (∑ i : Fin N, h_eff ξ i * spinVal (σ i)) := by
      intro ξ; dsimp only [w]; unfold prodBernoulli siteBernoulli
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      have hterm : ∀ i : Fin N, (2 * Real.cosh (h_eff ξ i)) *
          (Real.exp (h_eff ξ i * spinVal (σ i)) / (2 * Real.cosh (h_eff ξ i))) =
          Real.exp (h_eff ξ i * spinVal (σ i)) := fun i ↦
        mul_div_cancel₀ _ (by linarith [Real.cosh_pos (h_eff ξ i)])
      simp_rw [hterm, ← Real.exp_sum]
    simp_rw [hprod_cancel]
    unfold isingGibbsMeasure
    have hnum : Real.exp (-β * isingHamiltonianStrict J hfield σ) =
        C_pre * ∑ ξ : Ξ, Real.exp (∑ i : Fin N, h_eff ξ i * spinVal (σ i)) := by
      have hexp_split : Real.exp (-β * isingHamiltonianStrict J hfield σ) =
          Real.exp (∑ i : Fin N, β * hfield i * spinVal (σ i)) *
          ∏ e : IsingEdge N, Real.exp (β * J e.1.1 e.1.2 * spinVal (σ e.1.1) * spinVal (σ e.1.2)) := by
        rw [← Real.exp_sum, ← Real.exp_add]
        congr 1
        unfold isingHamiltonianStrict
        have h1 : β * (∑ i : Fin N, hfield i * spinVal (σ i)) = ∑ i : Fin N, β * hfield i * spinVal (σ i) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
        have h2 : β * (∑ e : IsingEdge N, J e.1.1 e.1.2 * spinVal (σ e.1.1) * spinVal (σ e.1.2)) =
            ∑ e : IsingEdge N, β * J e.1.1 e.1.2 * spinVal (σ e.1.1) * spinVal (σ e.1.2) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro e _; ring
        linarith
      rw [hexp_split]
      have hedge : ∀ e : IsingEdge N,
          Real.exp (β * J e.1.1 e.1.2 * spinVal (σ e.1.1) * spinVal (σ e.1.2)) =
            (Real.exp (-β * |J e.1.1 e.1.2|) * (1 / 2 : ℝ)) *
              ∑ b : Bool, Real.exp ((if b then c e else -c e) * (spinVal (σ e.1.1) + sgn e * spinVal (σ e.1.2))) :=
        fun e ↦ single_edge_discrete_hs hβ (J e.1.1 e.1.2) (σ e.1.1) (σ e.1.2)
      simp_rw [hedge]
      rw [Finset.prod_mul_distrib, ← mul_assoc, mul_comm (Real.exp _), mul_assoc]
      congr 1
      rw [Fintype.prod_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro ξ _
      rw [← Real.exp_sum, ← Real.exp_add]
      congr 1
      dsimp only [h_eff]
      trans (∑ i : Fin N, (β * hfield i * spinVal (σ i) +
          (∑ e : IsingEdge N, ((if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
            (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0))) * spinVal (σ i)))
      · rw [Finset.sum_add_distrib]
        congr 1
        trans (∑ i : Fin N, ∑ e : IsingEdge N,
            ((if e.1.1 = i then (if ξ e then c e else -c e) else 0) +
             (if e.1.2 = i then (if ξ e then c e else -c e) * sgn e else 0)) * spinVal (σ i))
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro e _
          simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq,
            Finset.mem_univ, ↓reduceIte]
          split_ifs <;> ring
        · exact Finset.sum_congr rfl fun i _ ↦ (Finset.sum_mul _ _ _).symm
      · exact Finset.sum_congr rfl fun i _ ↦ (add_mul _ _ _).symm
    rw [hnum, div_eq_mul_inv, mul_comm (C_pre * _), ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ξ _; ring
  have hw_sum : ∑ ξ : Ξ, w ξ = 1 := by
    have hsum1 : ∑ σ : SpinConfig N, isingGibbsMeasure β J hfield σ = 1 := by
      unfold isingGibbsMeasure
      rw [← Finset.sum_div, div_self hZ_pos.ne']
    calc ∑ ξ : Ξ, w ξ = ∑ ξ : Ξ, w ξ * (∑ σ : SpinConfig N, prodBernoulli (h_eff ξ) σ) := by
            apply Finset.sum_congr rfl; intro ξ _; rw [prodBernoulli_sum, mul_one]
      _ = ∑ ξ : Ξ, ∑ σ : SpinConfig N, w ξ * prodBernoulli (h_eff ξ) σ := by
            apply Finset.sum_congr rfl; intro ξ _; rw [Finset.mul_sum]
      _ = ∑ σ : SpinConfig N, ∑ ξ : Ξ, w ξ * prodBernoulli (h_eff ξ) σ := Finset.sum_comm
      _ = ∑ σ : SpinConfig N, isingGibbsMeasure β J hfield σ :=
            Finset.sum_congr rfl fun σ _ ↦ (hmix σ).symm
      _ = 1 := hsum1
  exact ⟨w, h_eff, hw_nn, hw_sum, hh_le, hmix⟩

/-- **Proposition 8.3 (Explicit Linear Bound, Eq. 8.4)**:
With incident degree `≤ Δ` and local energy `≤ H_max`,
`glauberDirichlet (isingGibbsMeasure β J hfield) f ≤ 2 ^ Δ * Real.exp (2 * β * H_max) * degreeFiltrationQ (isingGibbsMeasure β J hfield) f`. -/
theorem prop_8_3_ising_explicit_eq_8_4 {N Δ : ℕ} {β H_max : ℝ} (hβ : 0 ≤ β) (hHmax : 0 ≤ H_max)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ)
    (hdeg : ∀ i : Fin N,
      (∑ e : IsingEdge N, ((if e.1.1 = i then (1 : ℝ) else 0) + (if e.1.2 = i then (1 : ℝ) else 0))) ≤ (Δ : ℝ))
    (hloc : ∀ i : Fin N,
      |hfield i| +
        ∑ e : IsingEdge N,
          ((if e.1.1 = i then |J e.1.1 e.1.2| else 0) + (if e.1.2 = i then |J e.1.1 e.1.2| else 0)) ≤ H_max)
    (f : SpinConfig N → ℝ) :
    glauberDirichlet (isingGibbsMeasure β J hfield) f ≤
      (2 : ℝ) ^ Δ * Real.exp (2 * β * H_max) *
        degreeFiltrationQ (isingGibbsMeasure β J hfield) f := by
  have h1 := prop_8_3_classical_ising_reverse_poincare_eq_8_4 hβ J hfield f
  have hphi := isingPhiMaxExact_le_linear hβ hHmax J hfield hdeg hloc
  have hphi_nn : 0 ≤ isingPhiMaxExact β J hfield := by
    unfold isingPhiMaxExact
    have hfold_nn : ∀ (S : Finset (Fin N)) (g : Fin N → ℝ), 0 ≤ S.fold max 0 g := by
      intro S g; classical
      induction S using Finset.induction_on with
      | empty => simp
      | insert a t hat ih => rw [Finset.fold_insert hat]; exact le_trans ih (le_max_right _ _)
    exact hfold_nn Finset.univ _
  have hcosh_le : (Real.cosh (isingPhiMaxExact β J hfield)) ^ 2 ≤
      (2 : ℝ) ^ Δ * Real.exp (2 * β * H_max) := by
    have hcosh_exp : Real.cosh (isingPhiMaxExact β J hfield) ≤ Real.exp (isingPhiMaxExact β J hfield) := by
      rw [Real.cosh_eq]
      have : Real.exp (-(isingPhiMaxExact β J hfield)) ≤ Real.exp (isingPhiMaxExact β J hfield) :=
        Real.exp_le_exp.mpr (by linarith)
      linarith
    have hsq : (Real.cosh (isingPhiMaxExact β J hfield)) ^ 2 ≤
        Real.exp (2 * isingPhiMaxExact β J hfield) := by
      calc (Real.cosh (isingPhiMaxExact β J hfield)) ^ 2
          ≤ (Real.exp (isingPhiMaxExact β J hfield)) ^ 2 :=
            pow_le_pow_left₀ (Real.cosh_pos _).le hcosh_exp 2
        _ = Real.exp (2 * isingPhiMaxExact β J hfield) := by
            rw [sq, ← Real.exp_add]; congr 1; ring
    have hexp_le : Real.exp (2 * isingPhiMaxExact β J hfield) ≤
        (2 : ℝ) ^ Δ * Real.exp (2 * β * H_max) := by
      calc Real.exp (2 * isingPhiMaxExact β J hfield)
          ≤ Real.exp (2 * (β * H_max + ((Δ : ℝ) / 2) * Real.log 2)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp ((Δ : ℝ) * Real.log 2) * Real.exp (2 * β * H_max) := by
            rw [← Real.exp_add]; congr 1; ring
        _ = (2 : ℝ) ^ Δ * Real.exp (2 * β * H_max) := by
            rw [mul_comm (Δ : ℝ), Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
    exact le_trans hsq hexp_le
  have hQ_nn : 0 ≤ degreeFiltrationQ (isingGibbsMeasure β J hfield) f := by
    unfold degreeFiltrationQ distSqDegree
    apply Finset.sum_nonneg; intro k _
    apply Real.sInf_nonneg; rintro _ ⟨g, _, rfl⟩
    apply Finset.sum_nonneg; intro σ _
    have hμ_nn : 0 ≤ isingGibbsMeasure β J hfield σ := by
      unfold isingGibbsMeasure
      exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le)
    exact mul_nonneg hμ_nn (sq_nonneg _)
  exact le_trans h1 (mul_le_mul_of_nonneg_right hcosh_le hQ_nn)

/-- Diagonal real-part projection of a `QubitOp N` onto classical spin functions `SpinConfig N → ℝ`. -/
def diagSpinFnOfQubitOp {N : ℕ} (B : QubitOp N) : SpinConfig N → ℝ :=
  fun σ ↦ (B ((qubitIdxEquivSpinConfig N).symm σ) ((qubitIdxEquivSpinConfig N).symm σ)).re

private lemma diagQubitOpOfSpinFn_herm {N : ℕ} (f : SpinConfig N → ℝ) :
    (diagQubitOpOfSpinFn f).IsHermitian := by
  unfold diagQubitOpOfSpinFn Matrix.IsHermitian
  ext i j; simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

/-- For diagonal Ising `Hdiag`, `G.ρHalf` is diagonal with entries `√(isingGibbsMeasure β J hfield (e q))`. -/
private lemma diagIsing_rhoHalf_eq {N : ℕ} (β : ℝ)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ) :
    let Hdiag := diagQubitOpOfSpinFn (isingHamiltonianStrict J hfield)
    let hH := diagQubitOpOfSpinFn_herm (isingHamiltonianStrict J hfield)
    (concreteGibbsData hH β).ρHalf = Matrix.diagonal (fun q : QubitIdx N ↦
      ((Real.sqrt (isingGibbsMeasure β J hfield (qubitIdxEquivSpinConfig N q)) : ℝ) : ℂ)) := by
  intro Hdiag hH
  set U : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  have hU_mul : U * Uᴴ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hU_mul' : Uᴴ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hherm_diag : ∀ g : ℝ → ℂ,
      hermFunc hH g = Matrix.diagonal (fun q : QubitIdx N ↦
        g (isingHamiltonianStrict J hfield (qubitIdxEquivSpinConfig N q))) := by
    intro g
    have hU_eig : ∀ (q k : QubitIdx N),
        ((isingHamiltonianStrict J hfield (qubitIdxEquivSpinConfig N q) : ℝ) : ℂ) * U q k =
        ((hH.eigenvalues k : ℝ) : ℂ) * U q k := by
      intro q k
      have h1 : Hdiag = U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * Uᴴ := by
        simpa [U, Unitary.conjStarAlgAut_apply, Function.comp_def, Matrix.star_eq_conjTranspose] using
          hH.spectral_theorem
      have hHU : Hdiag * U = U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by
        calc Hdiag * U = (U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * Uᴴ) * U := by rw [← h1]
          _ = U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) * (Uᴴ * U) := by simp only [Matrix.mul_assoc]
          _ = U * Matrix.diagonal (fun i ↦ (hH.eigenvalues i : ℂ)) := by rw [hU_mul', Matrix.mul_one]
      have hqk := congrFun (congrFun hHU q) k
      simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte] at hqk
      have hlhs : ∑ x : QubitIdx N, Hdiag q x * U x k =
          ((isingHamiltonianStrict J hfield (qubitIdxEquivSpinConfig N q) : ℝ) : ℂ) * U q k := by
        simp only [Hdiag, diagQubitOpOfSpinFn, Matrix.diagonal_apply, ite_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      rw [hlhs] at hqk
      simpa [mul_comm] using hqk
    ext q r
    change (U * Matrix.diagonal (fun k ↦ g (hH.eigenvalues k)) * Uᴴ) q r = _
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    have hpull : (∑ k : QubitIdx N, U q k * g (hH.eigenvalues k) * Uᴴ k r) =
        g (isingHamiltonianStrict J hfield (qubitIdxEquivSpinConfig N q)) * (U * Uᴴ) q r := by
      rw [Matrix.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      by_cases h0 : U q k = 0
      · simp [h0]
      · have heq : isingHamiltonianStrict J hfield (qubitIdxEquivSpinConfig N q) = hH.eigenvalues k :=
          Complex.ofReal_injective (mul_right_cancel₀ h0 (hU_eig q k))
        rw [heq]; ring
    rw [hpull, hU_mul, Matrix.one_apply]; split_ifs <;> simp
  have hZ_eq : gibbsPartitionFn hH β =
      ∑ τ : SpinConfig N, Real.exp (-β * isingHamiltonianStrict J hfield τ) := by
    have htr : (hermFunc hH (fun x : ℝ ↦ Complex.exp (((-β * x : ℝ) : ℂ)))).trace.re =
        gibbsPartitionFn hH β := by
      unfold hermFunc gibbsPartitionFn
      change (U * Matrix.diagonal (fun i ↦ Complex.exp (((-β * hH.eigenvalues i : ℝ) : ℂ))) * Uᴴ).trace.re = _
      calc (U * Matrix.diagonal (fun i ↦ Complex.exp (((-β * hH.eigenvalues i : ℝ) : ℂ))) * Uᴴ).trace.re
          = (Uᴴ * (U * Matrix.diagonal (fun i ↦ Complex.exp (((-β * hH.eigenvalues i : ℝ) : ℂ))))).trace.re := by
              rw [Matrix.trace_mul_comm]
        _ = ((Uᴴ * U) * Matrix.diagonal (fun i ↦ Complex.exp (((-β * hH.eigenvalues i : ℝ) : ℂ)))).trace.re := by
              rw [Matrix.mul_assoc]
        _ = (Matrix.diagonal (fun i ↦ Complex.exp (((-β * hH.eigenvalues i : ℝ) : ℂ)))).trace.re := by
              rw [hU_mul', Matrix.one_mul]
        _ = ∑ i : QubitIdx N, Real.exp (-β * hH.eigenvalues i) := by
              rw [Matrix.trace_diagonal, Complex.re_sum]
              apply Finset.sum_congr rfl; intro i _
              rw [← Complex.ofReal_exp, Complex.ofReal_re]
    rw [← htr, hherm_diag, Matrix.trace_diagonal, Complex.re_sum]
    simp_rw [← Complex.ofReal_exp, Complex.ofReal_re]
    exact Equiv.sum_comp (qubitIdxEquivSpinConfig N) (fun τ ↦ Real.exp (-β * isingHamiltonianStrict J hfield τ))
  change gibbsRhoHalf hH β = _
  unfold gibbsRhoHalf
  rw [hherm_diag, hZ_eq]
  ext i j
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul, isingGibbsMeasure]
  split_ifs with hij
  · subst hij
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    rw [Real.sqrt_div (Real.exp_pos _).le, div_eq_inv_mul]
    congr 1
    rw [← Real.exp_half]; congr 1; ring
  · simp

/-- Dropping off-diagonal entries and imaginary parts decreases `gibbsWightmanNormSq` for diagonal Ising `G`
and diagonal real observable `diagQubitOpOfSpinFn f`. -/
private lemma diagIsing_wightmanNormSq_sub_ge {N : ℕ} (β : ℝ)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ) (f : SpinConfig N → ℝ) (B : QubitOp N) :
    let hH := diagQubitOpOfSpinFn_herm (isingHamiltonianStrict J hfield)
    let G := concreteGibbsData hH β
    ∑ σ : SpinConfig N, isingGibbsMeasure β J hfield σ * (f σ - diagSpinFnOfQubitOp B σ) ^ 2 ≤
      gibbsWightmanNormSq G (diagQubitOpOfSpinFn f - B) := by
  intro hH G
  set d : QubitIdx N → ℝ := fun q ↦ Real.sqrt (isingGibbsMeasure β J hfield (qubitIdxEquivSpinConfig N q))
  have hρHalf : G.ρHalf = Matrix.diagonal (fun q ↦ (d q : ℂ)) := diagIsing_rhoHalf_eq β J hfield
  set X : QubitOp N := diagQubitOpOfSpinFn f - B
  have hdiag_le : ∑ q : QubitIdx N, d q * d q * ‖X q q‖ ^ 2 ≤ gibbsWightmanNormSq G X := by
    unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
    rw [hρHalf]
    have hL : ∀ q₁ q₂, (Matrix.diagonal (fun q ↦ (d q : ℂ)) * Xᴴ * Matrix.diagonal (fun q ↦ (d q : ℂ))) q₁ q₂ =
        (d q₁ : ℂ) * star (X q₂ q₁) * (d q₂ : ℂ) := fun q₁ q₂ ↦ by
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    apply Finset.sum_le_sum; intro q _
    rw [Matrix.mul_apply, Complex.re_sum]
    have hterm_eq : ∀ q₂ : QubitIdx N,
        ((Matrix.diagonal (fun r ↦ (d r : ℂ)) * Xᴴ * Matrix.diagonal (fun r ↦ (d r : ℂ))) q q₂ * X q₂ q).re =
        d q * d q₂ * ‖X q₂ q‖ ^ 2 := by
      intro q₂; rw [hL q q₂]
      have hx : star (X q₂ q) * X q₂ q = ((‖X q₂ q‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, mul_comm, Complex.mul_conj', Complex.ofReal_pow]
      have hmul : (d q : ℂ) * star (X q₂ q) * (d q₂ : ℂ) * X q₂ q =
          (((d q * d q₂) * ‖X q₂ q‖ ^ 2 : ℝ) : ℂ) := by
        calc (d q : ℂ) * star (X q₂ q) * (d q₂ : ℂ) * X q₂ q
            = ((d q : ℂ) * (d q₂ : ℂ)) * (star (X q₂ q) * X q₂ q) := by ring
          _ = ((d q * d q₂ : ℝ) : ℂ) * ((‖X q₂ q‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.ofReal_mul, hx]
          _ = _ := by rw [← Complex.ofReal_mul]
      rw [hmul, Complex.ofReal_re]
    simp_rw [hterm_eq]
    exact Finset.single_le_sum (f := fun q₂ : QubitIdx N ↦ d q * d q₂ * ‖X q₂ q‖ ^ 2)
      (fun q₂ _ ↦ mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (sq_nonneg _)) (Finset.mem_univ q)
  have hμ_nn : ∀ σ : SpinConfig N, 0 ≤ isingGibbsMeasure β J hfield σ := fun σ ↦ by
    unfold isingGibbsMeasure
    exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le)
  have hre_le : ∑ σ : SpinConfig N, isingGibbsMeasure β J hfield σ * (f σ - diagSpinFnOfQubitOp B σ) ^ 2 ≤
      ∑ q : QubitIdx N, d q * d q * ‖X q q‖ ^ 2 := by
    rw [← Equiv.sum_comp (qubitIdxEquivSpinConfig N)
      (fun σ ↦ isingGibbsMeasure β J hfield σ * (f σ - diagSpinFnOfQubitOp B σ) ^ 2)]
    apply Finset.sum_le_sum; intro q _
    have hdd : d q * d q = isingGibbsMeasure β J hfield (qubitIdxEquivSpinConfig N q) :=
      Real.mul_self_sqrt (hμ_nn _)
    rw [hdd]
    apply mul_le_mul_of_nonneg_left _ (hμ_nn _)
    have hXre : (X q q).re = f (qubitIdxEquivSpinConfig N q) - diagSpinFnOfQubitOp B (qubitIdxEquivSpinConfig N q) := by
      simp [X, diagQubitOpOfSpinFn, diagSpinFnOfQubitOp]
    rw [← hXre]
    have h1 : |(X q q).re| ≤ ‖X q q‖ := Complex.abs_re_le_norm _
    nlinarith [sq_abs (X q q).re, abs_nonneg (X q q).re, norm_nonneg (X q q)]
  exact le_trans hre_le hdiag_le

/-- Diagonal entry of `pauliMat α` at `b : Fin 2`. -/
private lemma pauliMat_diag_eq (α : Fin 4) (b : Fin 2) :
    pauliMat α b b =
      if α = 0 then 1
      else if α = 3 then (if b = 0 then 1 else -1)
      else 0 := by
  fin_cases α <;> fin_cases b <;> simp [pauliMat, pauliX, pauliY, pauliZ]

/-- Diagonal real part of a Pauli string `pauliString a` lies in `classicalDegreeSubspace N k`
whenever `|{i | a i ≠ 0}| ≤ k`. -/
private lemma diagSpinFn_pauliString_mem_classicalDegree {N k : ℕ} (a : Fin N → Fin 4)
    (ha : (Finset.univ.filter (fun i : Fin N ↦ a i ≠ 0)).card ≤ k) :
    diagSpinFnOfQubitOp (pauliString a) ∈ classicalDegreeSubspace N k := by
  by_cases hxy : ∃ i : Fin N, a i = 1 ∨ a i = 2
  · rcases hxy with ⟨i₀, hi₀⟩
    have hzero : diagSpinFnOfQubitOp (pauliString a) = 0 := by
      funext σ
      unfold diagSpinFnOfQubitOp pauliString kronOp
      simp only [Matrix.of_apply]
      have hterm0 : pauliMat (a i₀) ((qubitIdxEquivSpinConfig N).symm σ i₀)
          ((qubitIdxEquivSpinConfig N).symm σ i₀) = 0 := by
        rw [pauliMat_diag_eq]
        rcases hi₀ with h1 | h2 <;> simp [h1, h2]
      rw [Finset.prod_eq_zero (Finset.mem_univ i₀) hterm0, Complex.zero_re]; rfl
    rw [hzero]; exact Submodule.zero_mem _
  · push Not at hxy
    let S : Finset (Fin N) := Finset.univ.filter (fun i : Fin N ↦ a i = 3)
    have hScard : S.card ≤ k := by
      refine le_trans (Finset.card_le_card ?_) ha
      intro i hi; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hi]; decide
    have hfn : diagSpinFnOfQubitOp (pauliString a) =
        ((-1 : ℝ) ^ S.card) • (fun σ : SpinConfig N ↦ ∏ i ∈ S, spinVal (σ i)) := by
      funext σ
      unfold diagSpinFnOfQubitOp pauliString kronOp
      simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
      have hprod : ∏ i : Fin N, pauliMat (a i) ((qubitIdxEquivSpinConfig N).symm σ i)
          ((qubitIdxEquivSpinConfig N).symm σ i) =
          (((∏ i ∈ S, (-spinVal (σ i)) : ℝ) : ℂ)) := by
        rw [Complex.ofReal_prod]
        rw [← Finset.prod_subset (Finset.subset_univ S)]
        · apply Finset.prod_congr rfl; intro i hi
          have ha3 : a i = 3 := (Finset.mem_filter.mp hi).2
          rw [pauliMat_diag_eq, if_neg (by rw [ha3]; decide), if_pos ha3]
          cases hσ : σ i <;> simp [qubitIdxEquivSpinConfig, spinVal, hσ]
        · intro i _ hiS
          have ha0 : a i = 0 := by
            have hne3 : a i ≠ 3 := by simpa [S] using hiS
            have h12 := hxy i
            have ha_cases : a i = 0 ∨ a i = 1 ∨ a i = 2 ∨ a i = 3 := by
              generalize h : a i = v; fin_cases v <;> simp
            rcases ha_cases with h | h | h | h
            · exact h
            · exact absurd h h12.1
            · exact absurd h h12.2
            · exact absurd h hne3
          rw [pauliMat_diag_eq, if_pos ha0]
      rw [hprod, Complex.ofReal_re, Finset.prod_neg]
    rw [hfn]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, hScard, rfl⟩)

/-- Every classical character `fun σ ↦ ∏ i ∈ S, spinVal (σ i)` embeds via `diagQubitOpOfSpinFn`
into `filtrationSubmodule N k` whenever `S.card ≤ k`. -/
private lemma diagQubitOp_character_mem_filtration {N k : ℕ} (S : Finset (Fin N)) (hS : S.card ≤ k) :
    diagQubitOpOfSpinFn (fun σ : SpinConfig N ↦ ∏ i ∈ S, spinVal (σ i)) ∈ filtrationSubmodule N k := by
  let a : Fin N → Fin 4 := fun i ↦ if i ∈ S then 3 else 0
  have heq : diagQubitOpOfSpinFn (fun σ : SpinConfig N ↦ ∏ i ∈ S, spinVal (σ i)) =
      ((-1 : ℂ) ^ S.card) • pauliString a := by
    ext q₁ q₂
    simp only [diagQubitOpOfSpinFn, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
      pauliString, kronOp, Matrix.of_apply]
    by_cases hq : q₁ = q₂
    · subst hq
      rw [if_pos rfl, Complex.ofReal_prod]
      have hprod : ∏ i : Fin N, pauliMat (a i) (q₁ i) (q₁ i) =
          ∏ i ∈ S, ((-spinVal (qubitIdxEquivSpinConfig N q₁ i) : ℝ) : ℂ) := by
        rw [← Finset.prod_subset (Finset.subset_univ S)]
        · apply Finset.prod_congr rfl; intro i hi
          have hai : a i = 3 := if_pos hi
          rw [hai, pauliMat_diag_eq, if_neg (by decide), if_pos rfl]
          have hfin2 : q₁ i = 0 ∨ q₁ i = 1 := by generalize h : q₁ i = v; fin_cases v <;> simp
          rcases hfin2 with h0 | h1 <;> simp [qubitIdxEquivSpinConfig, spinVal, h0, h1]
        · intro i _ hiS
          have hai : a i = 0 := if_neg hiS
          rw [hai, pauliMat_diag_eq, if_pos rfl]
      rw [hprod]
      simp_rw [Complex.ofReal_neg, Finset.prod_neg]
      rw [← mul_assoc, ← mul_pow]; norm_num
    · rw [if_neg hq]
      have hne_coord : ∃ i : Fin N, q₁ i ≠ q₂ i := by
        by_contra hall; push Not at hall; exact hq (funext hall)
      rcases hne_coord with ⟨i₀, hi₀⟩
      have h0 : pauliMat (a i₀) (q₁ i₀) (q₂ i₀) = 0 := by
        dsimp only [a]; split_ifs
        · generalize h1 : q₁ i₀ = v1; generalize h2 : q₂ i₀ = v2
          rw [h1, h2] at hi₀; fin_cases v1 <;> fin_cases v2 <;> simp_all [pauliMat, pauliZ]
        · generalize h1 : q₁ i₀ = v1; generalize h2 : q₂ i₀ = v2
          rw [h1, h2] at hi₀; fin_cases v1 <;> fin_cases v2 <;> simp_all [pauliMat]
      rw [Finset.prod_eq_zero (Finset.mem_univ i₀) h0, mul_zero]
  rw [heq]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨a, ?_, rfl⟩
  have hsub : Finset.univ.filter (fun i : Fin N ↦ a i ≠ 0) ⊆ S := by
    intro i hi; by_contra hiS
    exact (Finset.mem_filter.mp hi).2 (if_neg hiS)
  exact le_trans (Finset.card_le_card hsub) hS

/-- **Exact Diagonal Ising Quantum-to-Classical Degree-Filtration Identity**:
For diagonal Ising Hamiltonian `Hdiag = diag(H_Ising)` and any classical observable `f : SpinConfig N → ℝ`,
`Re (A_f | 𝒬^{(β)} A_f)_β^W = degreeFiltrationQ (isingGibbsMeasure β J hfield) f`. -/
theorem diagIsing_wightmanQ_eq_classical_degreeFiltrationQ {N : ℕ} (β : ℝ)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ) (f : SpinConfig N → ℝ) :
    let hH := diagQubitOpOfSpinFn_herm (isingHamiltonianStrict J hfield)
    let G := concreteGibbsData hH β
    (gibbsWightmanInner G (diagQubitOpOfSpinFn f) (wightmanQ G (diagQubitOpOfSpinFn f))).re =
      degreeFiltrationQ (isingGibbsMeasure β J hfield) f := by
  intro hH G
  unfold wightmanQ degreeFiltrationQ
  simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply]
  have hsum : gibbsWightmanInner G (diagQubitOpOfSpinFn f)
      (∑ s ∈ Finset.range N, (diagQubitOpOfSpinFn f - wightmanFiltrationProj G s (diagQubitOpOfSpinFn f))) =
      ∑ s ∈ Finset.range N, gibbsWightmanInner G (diagQubitOpOfSpinFn f)
        (diagQubitOpOfSpinFn f - wightmanFiltrationProj G s (diagQubitOpOfSpinFn f)) := by
    unfold gibbsWightmanInner wightmanInner; rw [Matrix.mul_sum, Matrix.trace_sum]
  rw [hsum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [wightmanFiltrationProj, wightmanSubspaceProj_eq_distSq]
  unfold wightmanDistSq distSqDegree
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_, 0, Submodule.zero_mem _, rfl⟩
    · rintro r ⟨g, hg, rfl⟩
      have hdiag_mem : diagQubitOpOfSpinFn g ∈ filtrationSubmodule N k := by
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
        · rintro _ ⟨S, hS, rfl⟩; exact diagQubitOp_character_mem_filtration S hS
        · convert Submodule.zero_mem (filtrationSubmodule N k)
          ext i j; simp [diagQubitOpOfSpinFn]
        · intro x y _ _ hx hy
          convert Submodule.add_mem _ hx hy
          ext i j; simp [diagQubitOpOfSpinFn, Matrix.diagonal_apply]; split_ifs <;> simp
        · intro c x _ hx
          convert Submodule.smul_mem _ (c : ℂ) hx
          ext i j; simp [diagQubitOpOfSpinFn, Matrix.diagonal_apply]; split_ifs <;> simp
      have hsub_eq : diagQubitOpOfSpinFn f - diagQubitOpOfSpinFn g = diagQubitOpOfSpinFn (f - g) := by
        ext i j; simp [diagQubitOpOfSpinFn, Matrix.diagonal_apply]; split_ifs <;> simp
      apply csInf_le
      · exact ⟨0, by rintro _ ⟨B, _, rfl⟩; exact gibbsWightmanNormSq_nonneg G _⟩
      · refine ⟨diagQubitOpOfSpinFn g, hdiag_mem, ?_⟩
        rw [hsub_eq, diagIsing_wightmanNormSq_eq_classical_L2]
  · apply le_csInf
    · exact ⟨_, 0, Submodule.zero_mem _, rfl⟩
    · rintro r ⟨B, hB, rfl⟩
      have hdiag_mem : diagSpinFnOfQubitOp B ∈ classicalDegreeSubspace N k := by
        have hlin_add : ∀ X Y : QubitOp N,
            diagSpinFnOfQubitOp (X + Y) = diagSpinFnOfQubitOp X + diagSpinFnOfQubitOp Y := fun X Y ↦ by
          funext σ; simp [diagSpinFnOfQubitOp]
        have hlin_smul : ∀ (c : ℂ) (X : QubitOp N),
            diagSpinFnOfQubitOp (c • X) =
              c.re • diagSpinFnOfQubitOp X + c.im • diagSpinFnOfQubitOp (Complex.I • X) := fun c X ↦ by
          funext σ; simp [diagSpinFnOfQubitOp]; ring
        have hboth : ∀ Z ∈ filtrationSubmodule N k,
            diagSpinFnOfQubitOp Z ∈ classicalDegreeSubspace N k ∧
            diagSpinFnOfQubitOp (Complex.I • Z) ∈ classicalDegreeSubspace N k := by
          intro Z hZ
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hZ
          · rintro _ ⟨a, ha, rfl⟩
            refine ⟨diagSpinFn_pauliString_mem_classicalDegree a ha, ?_⟩
            have him0 : diagSpinFnOfQubitOp (Complex.I • pauliString a) = 0 := by
              funext σ; simp only [diagSpinFnOfQubitOp, Matrix.smul_apply, smul_eq_mul, Complex.I_mul,
                Complex.re_ofReal_mul]
              have hreal : ((pauliString a) ((qubitIdxEquivSpinConfig N).symm σ)
                  ((qubitIdxEquivSpinConfig N).symm σ)).im = 0 := by
                unfold pauliString kronOp; simp only [Matrix.of_apply]
                have h1 : ∀ i : Fin N, ∃ r : ℝ, pauliMat (a i) ((qubitIdxEquivSpinConfig N).symm σ i)
                    ((qubitIdxEquivSpinConfig N).symm σ i) = (r : ℂ) := by
                  intro i; rw [pauliMat_diag_eq]; split_ifs <;> [exact ⟨1, by simp⟩; exact ⟨1, by simp⟩;
                    exact ⟨-1, by simp⟩; exact ⟨0, by simp⟩]
                choose r hr using h1
                simp_rw [hr, ← Complex.ofReal_prod, Complex.ofReal_im]
              simp [Complex.mul_re, hreal]
            rw [him0]; exact Submodule.zero_mem _
          · have h0 : diagSpinFnOfQubitOp (0 : QubitOp N) = 0 := by funext σ; simp [diagSpinFnOfQubitOp]
            simp [h0, Submodule.zero_mem]
          · intro U V _ _ hU hV
            refine ⟨by rw [hlin_add]; exact Submodule.add_mem _ hU.1 hV.1,
              by rw [smul_add, hlin_add]; exact Submodule.add_mem _ hU.2 hV.2⟩
          · intro z U _ hU
            refine ⟨by rw [hlin_smul]; exact Submodule.add_mem _ (Submodule.smul_mem _ _ hU.1) (Submodule.smul_mem _ _ hU.2), ?_⟩
            have hIU : Complex.I • (z • U) = (Complex.I * z) • U := by rw [smul_smul]
            rw [hIU, hlin_smul]
            exact Submodule.add_mem _ (Submodule.smul_mem _ _ hU.1) (Submodule.smul_mem _ _ hU.2)
        exact (hboth B hB).1
      refine le_trans ?_ (diagIsing_wightmanNormSq_sub_ge β J hfield f B)
      apply csInf_le
      · exact ⟨0, by
          rintro _ ⟨g, _, rfl⟩
          exact Finset.sum_nonneg fun σ _ ↦ mul_nonneg (by
            unfold isingGibbsMeasure
            exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ ↦ (Real.exp_pos _).le))
            (sq_nonneg _)⟩
      · exact ⟨diagSpinFnOfQubitOp B, hdiag_mem, rfl⟩

/-- **Exact Diagonal Ising Quantum-to-Classical Glauber Dirichlet Identity**:
For diagonal Ising Hamiltonian `Hdiag = diag(H_Ising)` and any classical observable `f : SpinConfig N → ℝ`,
`Re (A_f | 𝒬̃^{(β)} A_f)_β^W = glauberDirichlet (isingGibbsMeasure β J hfield) f`. -/
theorem diagIsing_glauberGen_eq_classical_dirichlet {N : ℕ} (β : ℝ)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ) (f : SpinConfig N → ℝ) :
    let hH := diagQubitOpOfSpinFn_herm (isingHamiltonianStrict J hfield)
    let G := concreteGibbsData hH β
    (gibbsWightmanInner G (diagQubitOpOfSpinFn f) (quantumGlauberGen G (diagQubitOpOfSpinFn f))).re =
      glauberDirichlet (isingGibbsMeasure β J hfield) f := by
  intro hH G
  unfold quantumGlauberGen glauberDirichlet
  simp only [LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.id_apply]
  have hsum : gibbsWightmanInner G (diagQubitOpOfSpinFn f)
      (∑ x : Fin N, (diagQubitOpOfSpinFn f - singleSiteWightmanProj G x (diagQubitOpOfSpinFn f))) =
      ∑ x : Fin N, gibbsWightmanInner G (diagQubitOpOfSpinFn f)
        (diagQubitOpOfSpinFn f - singleSiteWightmanProj G x (diagQubitOpOfSpinFn f)) := by
    unfold gibbsWightmanInner wightmanInner; rw [Matrix.mul_sum, Matrix.trace_sum]
  rw [hsum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro x _
  rw [singleSiteWightmanProj, wightmanSubspaceProj_eq_distSq]
  unfold wightmanDistSq
  set μ := isingGibbsMeasure β J hfield
  have hμ_pos : ∀ σ : SpinConfig N, 0 < μ σ := fun σ ↦ by
    unfold μ isingGibbsMeasure
    exact div_pos (Real.exp_pos _) (Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) ⟨fun _ ↦ false, Finset.mem_univ _⟩)
  have hce_indep : ∀ σ : SpinConfig N, condExpSite μ x f (flipSpin σ x) = condExpSite μ x f σ := by
    intro σ
    have hff : flipSpin (flipSpin σ x) x = σ := by
      funext i; unfold flipSpin; by_cases hi : i = x <;> simp [hi]
    unfold condExpSite; rw [hff, add_comm (μ (flipSpin σ x) * _), add_comm (μ (flipSpin σ x))]
  have hdiag_indep_mem : ∀ g : SpinConfig N → ℝ, (∀ σ, g (flipSpin σ x) = g σ) →
      diagQubitOpOfSpinFn g ∈ singleSiteTrivialSubmodule N x := by
    intro g hg
    have hexp : ∀ σ : SpinConfig N,
        g σ = ∑ S ∈ (Finset.univ.erase x).powerset,
          ((1 / (2 : ℝ) ^ N) * ∑ τ : SpinConfig N, g τ * ∏ i ∈ S, spinVal (τ i)) *
          ∏ i ∈ S, spinVal (σ i) := by
      intro σ
      have hwalsh : ∀ τ : SpinConfig N,
          ∑ S ∈ (Finset.univ.erase x).powerset, (∏ i ∈ S, spinVal (τ i)) * (∏ i ∈ S, spinVal (σ i)) =
            if ∀ i ≠ x, τ i = σ i then (2 : ℝ) ^ (N - 1) else 0 := by
        intro τ
        have h1 : ∀ S : Finset (Fin N), (∏ i ∈ S, spinVal (τ i)) * (∏ i ∈ S, spinVal (σ i)) =
            ∏ i ∈ S, (spinVal (τ i) * spinVal (σ i)) := fun S ↦ (Finset.prod_mul_distrib).symm
        simp_rw [h1]
        rw [← Finset.prod_one_add]
        by_cases hall : ∀ i ≠ x, τ i = σ i
        · rw [if_pos hall]
          have hterm : ∀ i ∈ Finset.univ.erase x, 1 + spinVal (τ i) * spinVal (σ i) = 2 := by
            intro i hi
            have hne : i ≠ x := (Finset.mem_erase.mp hi).1
            rw [hall i hne]; cases σ i <;> simp [spinVal] <;> norm_num
          rw [Finset.prod_congr rfl hterm, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ x),
            Finset.card_univ, Fintype.card_fin]
        · rw [if_neg hall]; push Not at hall
          rcases hall with ⟨i₀, hi₀x, hi₀ne⟩
          apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi₀x, Finset.mem_univ i₀⟩)
          cases h1 : τ i₀ <;> cases h2 : σ i₀ <;> simp_all [spinVal]
      have hswap : ∑ S ∈ (Finset.univ.erase x).powerset,
            ((1 / (2 : ℝ) ^ N) * ∑ τ : SpinConfig N, g τ * ∏ i ∈ S, spinVal (τ i)) *
            ∏ i ∈ S, spinVal (σ i) =
          (1 / (2 : ℝ) ^ N) * ∑ τ : SpinConfig N, g τ *
            (∑ S ∈ (Finset.univ.erase x).powerset, (∏ i ∈ S, spinVal (τ i)) * (∏ i ∈ S, spinVal (σ i))) := by
        rw [Finset.mul_sum]
        trans (∑ S ∈ (Finset.univ.erase x).powerset, ∑ τ : SpinConfig N,
            (1 / (2 : ℝ) ^ N) * (g τ * ((∏ i ∈ S, spinVal (τ i)) * (∏ i ∈ S, spinVal (σ i)))))
        · apply Finset.sum_congr rfl; intro S _
          rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro τ _; ring
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro τ _
          rw [Finset.mul_sum, Finset.mul_sum]
      rw [hswap]
      simp_rw [hwalsh]
      have hpair : ∑ τ : SpinConfig N, g τ * (if ∀ i ≠ x, τ i = σ i then (2 : ℝ) ^ (N - 1) else 0) =
          (g σ + g (flipSpin σ x)) * (2 : ℝ) ^ (N - 1) := by
        have hmem_pair : ∀ τ : SpinConfig N, (∀ i ≠ x, τ i = σ i) ↔ τ = σ ∨ τ = flipSpin σ x := by
          intro τ; constructor
          · intro h
            by_cases hx : τ x = σ x
            · left; funext i; by_cases hi : i = x; exact hi ▸ hx; exact h i hi
            · right; funext i; unfold flipSpin
              by_cases hi : i = x
              · subst hi; simp only [Function.update_self]; cases h1 : τ i <;> cases h2 : σ i <;> simp_all
              · simp [hi, h i hi]
          · rintro (rfl | rfl) i hi
            · rfl
            · unfold flipSpin; simp [hi]
        have hne : σ ≠ flipSpin σ x := by
          intro h; have := congrFun h x; unfold flipSpin at this; simp at this
        have hfilt : Finset.univ.filter (fun τ : SpinConfig N ↦ ∀ i ≠ x, τ i = σ i) = {σ, flipSpin σ x} := by
          ext τ; simp [hmem_pair]
        calc ∑ τ : SpinConfig N, g τ * (if ∀ i ≠ x, τ i = σ i then (2 : ℝ) ^ (N - 1) else 0)
            = ∑ τ ∈ Finset.univ.filter (fun τ : SpinConfig N ↦ ∀ i ≠ x, τ i = σ i), g τ * (2 : ℝ) ^ (N - 1) := by
                rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro τ _; split_ifs <;> simp
          _ = ∑ τ ∈ ({σ, flipSpin σ x} : Finset (SpinConfig N)), g τ * (2 : ℝ) ^ (N - 1) := by rw [hfilt]
          _ = (g σ + g (flipSpin σ x)) * (2 : ℝ) ^ (N - 1) := by
                rw [Finset.sum_pair hne]; ring
      rw [hpair, hg σ]
      have hNpos : 1 ≤ N := Fin.pos x
      have h2pow : (2 : ℝ) ^ N = 2 * (2 : ℝ) ^ (N - 1) := by
        conv_lhs => rw [show N = (N - 1) + 1 by omega, pow_succ]
        ring
      rw [h2pow]
      have h2ne : (2 : ℝ) ^ (N - 1) ≠ 0 := by positivity
      field_simp [h2ne]; ring
    have hdiag_eq : diagQubitOpOfSpinFn g =
        ∑ S ∈ (Finset.univ.erase x).powerset,
          (((1 / (2 : ℝ) ^ N) * ∑ τ : SpinConfig N, g τ * ∏ i ∈ S, spinVal (τ i) : ℝ) : ℂ) •
          diagQubitOpOfSpinFn (fun σ ↦ ∏ i ∈ S, spinVal (σ i)) := by
      ext q₁ q₂
      simp only [diagQubitOpOfSpinFn, Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      by_cases hq : q₁ = q₂
      · subst hq; rw [if_pos rfl, hexp (qubitIdxEquivSpinConfig N q₁), Complex.ofReal_sum]
        apply Finset.sum_congr rfl; intro S _; rw [if_pos rfl, Complex.ofReal_mul]
      · rw [if_neg hq]; symm; apply Finset.sum_eq_zero; intro S _; rw [if_neg hq, mul_zero]
    rw [hdiag_eq]
    apply Submodule.sum_mem; intro S hS
    apply Submodule.smul_mem
    have hxS : x ∉ S := fun hx ↦ (Finset.mem_erase.mp (Finset.mem_powerset.mp hS hx)).1 rfl
    let a : Fin N → Fin 4 := fun i ↦ if i ∈ S then 3 else 0
    have hchar_eq : diagQubitOpOfSpinFn (fun σ : SpinConfig N ↦ ∏ i ∈ S, spinVal (σ i)) =
        ((-1 : ℂ) ^ S.card) • pauliString a := by
      ext q₁ q₂
      simp only [diagQubitOpOfSpinFn, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul,
        pauliString, kronOp, Matrix.of_apply]
      by_cases hq : q₁ = q₂
      · subst hq; rw [if_pos rfl, Complex.ofReal_prod]
        have hprod : ∏ i : Fin N, pauliMat (a i) (q₁ i) (q₁ i) =
            ∏ i ∈ S, ((-spinVal (qubitIdxEquivSpinConfig N q₁ i) : ℝ) : ℂ) := by
          rw [← Finset.prod_subset (Finset.subset_univ S)]
          · apply Finset.prod_congr rfl; intro i hi
            have hai : a i = 3 := if_pos hi
            rw [hai, pauliMat_diag_eq, if_neg (by decide), if_pos rfl]
            have hfin2 : q₁ i = 0 ∨ q₁ i = 1 := by generalize h : q₁ i = v; fin_cases v <;> simp
            rcases hfin2 with h0 | h1 <;> simp [qubitIdxEquivSpinConfig, spinVal, h0, h1]
          · intro i _ hiS; rw [show a i = 0 from if_neg hiS, pauliMat_diag_eq, if_pos rfl]
        rw [hprod]; simp_rw [Complex.ofReal_neg, Finset.prod_neg]
        rw [← mul_assoc, ← mul_pow]; norm_num
      · rw [if_neg hq]
        have hne_coord : ∃ i : Fin N, q₁ i ≠ q₂ i := by
          by_contra hall; push Not at hall; exact hq (funext hall)
        rcases hne_coord with ⟨i₀, hi₀⟩
        have h0 : pauliMat (a i₀) (q₁ i₀) (q₂ i₀) = 0 := by
          dsimp only [a]; split_ifs
          · generalize h1 : q₁ i₀ = v1; generalize h2 : q₂ i₀ = v2
            rw [h1, h2] at hi₀; fin_cases v1 <;> fin_cases v2 <;> simp_all [pauliMat, pauliZ]
          · generalize h1 : q₁ i₀ = v1; generalize h2 : q₂ i₀ = v2
            rw [h1, h2] at hi₀; fin_cases v1 <;> fin_cases v2 <;> simp_all [pauliMat]
        rw [Finset.prod_eq_zero (Finset.mem_univ i₀) h0, mul_zero]
    rw [hchar_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, if_neg hxS, rfl⟩)
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, by rintro _ ⟨B, _, rfl⟩; exact gibbsWightmanNormSq_nonneg G _⟩
    · refine ⟨diagQubitOpOfSpinFn (condExpSite μ x f), hdiag_indep_mem _ hce_indep, ?_⟩
      have hsub_eq : diagQubitOpOfSpinFn f - diagQubitOpOfSpinFn (condExpSite μ x f) =
          diagQubitOpOfSpinFn (fun σ ↦ f σ - condExpSite μ x f σ) := by
        ext i j; simp [diagQubitOpOfSpinFn, Matrix.diagonal_apply]; split_ifs <;> simp
      rw [hsub_eq, diagIsing_wightmanNormSq_eq_classical_L2]
  · apply le_csInf
    · exact ⟨_, 0, Submodule.zero_mem _, rfl⟩
    · rintro r ⟨B, hB, rfl⟩
      have hB_indep : ∀ σ : SpinConfig N,
          diagSpinFnOfQubitOp B (flipSpin σ x) = diagSpinFnOfQubitOp B σ := by
        have hboth : ∀ Z ∈ singleSiteTrivialSubmodule N x,
            ∀ σ : SpinConfig N, Z ((qubitIdxEquivSpinConfig N).symm (flipSpin σ x))
              ((qubitIdxEquivSpinConfig N).symm (flipSpin σ x)) =
              Z ((qubitIdxEquivSpinConfig N).symm σ) ((qubitIdxEquivSpinConfig N).symm σ) := by
          intro Z hZ
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hZ
          · rintro _ ⟨a, hax, rfl⟩ σ
            unfold pauliString kronOp; simp only [Matrix.of_apply]
            apply Finset.prod_congr rfl; intro i _
            by_cases hi : i = x
            · subst hi; rw [hax, pauliMat_diag_eq, pauliMat_diag_eq, if_pos rfl]
            · have hsame : (qubitIdxEquivSpinConfig N).symm (flipSpin σ x) i =
                  (qubitIdxEquivSpinConfig N).symm σ i := by
                simp [qubitIdxEquivSpinConfig, flipSpin, hi]
              rw [hsame]
          · intro σ; simp
          · intro U V _ _ hU hV σ; simp [hU σ, hV σ]
          · intro c U _ hU σ; simp [hU σ]
        intro σ; unfold diagSpinFnOfQubitOp; rw [hboth B hB σ]
      set g := diagSpinFnOfQubitOp B
      have horth : ∑ σ : SpinConfig N, μ σ * (f σ - condExpSite μ x f σ) * (condExpSite μ x f σ - g σ) = 0 := by
        have hflip_sum : ∑ σ : SpinConfig N, μ σ * (f σ - condExpSite μ x f σ) * (condExpSite μ x f σ - g σ) =
            ∑ σ : SpinConfig N, μ (flipSpin σ x) * (f (flipSpin σ x) - condExpSite μ x f (flipSpin σ x)) *
              (condExpSite μ x f (flipSpin σ x) - g (flipSpin σ x)) := by
          let eFlip : SpinConfig N ≃ SpinConfig N :=
            { toFun := fun σ ↦ flipSpin σ x
              invFun := fun σ ↦ flipSpin σ x
              left_inv := fun σ ↦ by funext i; unfold flipSpin; by_cases hi : i = x <;> simp [hi]
              right_inv := fun σ ↦ by funext i; unfold flipSpin; by_cases hi : i = x <;> simp [hi] }
          exact (Equiv.sum_comp eFlip (fun σ ↦ μ σ * (f σ - condExpSite μ x f σ) * (condExpSite μ x f σ - g σ))).symm
        have hadd : (∑ σ : SpinConfig N, μ σ * (f σ - condExpSite μ x f σ) * (condExpSite μ x f σ - g σ)) +
            (∑ σ : SpinConfig N, μ (flipSpin σ x) * (f (flipSpin σ x) - condExpSite μ x f (flipSpin σ x)) *
              (condExpSite μ x f (flipSpin σ x) - g (flipSpin σ x))) = 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_eq_zero; intro σ _
          rw [hce_indep σ, hB_indep σ]
          have hden : μ σ + μ (flipSpin σ x) ≠ 0 := by linarith [hμ_pos σ, hμ_pos (flipSpin σ x)]
          have hce0 : μ σ * (f σ - condExpSite μ x f σ) +
              μ (flipSpin σ x) * (f (flipSpin σ x) - condExpSite μ x f σ) = 0 := by
            unfold condExpSite; field_simp [hden]; ring
          linear_combination (condExpSite μ x f σ - g σ) * hce0
        linarith
      have hclass_le : ∑ σ : SpinConfig N, μ σ * (f σ - condExpSite μ x f σ) ^ 2 ≤
          ∑ σ : SpinConfig N, μ σ * (f σ - g σ) ^ 2 := by
        have hdiff : ∑ σ : SpinConfig N, μ σ * (f σ - g σ) ^ 2 =
            (∑ σ : SpinConfig N, μ σ * (f σ - condExpSite μ x f σ) ^ 2) +
            2 * (∑ σ : SpinConfig N, μ σ * (f σ - condExpSite μ x f σ) * (condExpSite μ x f σ - g σ)) +
            (∑ σ : SpinConfig N, μ σ * (condExpSite μ x f σ - g σ) ^ 2) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro σ _; ring
        rw [hdiff, horth, mul_zero, add_zero]
        have hnn : 0 ≤ ∑ σ : SpinConfig N, μ σ * (condExpSite μ x f σ - g σ) ^ 2 :=
          Finset.sum_nonneg fun σ _ ↦ mul_nonneg (hμ_pos σ).le (sq_nonneg _)
        linarith
      exact le_trans hclass_le (diagIsing_wightmanNormSq_sub_ge β J hfield f B)

/-- **Proposition 8.3 (Quantum Operator Reverse Poincaré on Diagonal Ising Observables)**:
For diagonal Ising `Hdiag = diag(H_Ising)` (`β ≥ 0`) and EVERY diagonal observable `A_f = diag(f)`:
`Re (A_f | 𝒬̃^{(β)} A_f)_β^W ≤ (Real.cosh (isingPhiMaxExact β J hfield)) ^ 2 * Re (A_f | 𝒬^{(β)} A_f)_β^W`. -/
theorem prop_8_3_quantum_diag_ising_reverse_poincare {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (J : Fin N → Fin N → ℝ) (hfield : Fin N → ℝ) (f : SpinConfig N → ℝ) :
    let hH := diagQubitOpOfSpinFn_herm (isingHamiltonianStrict J hfield)
    let G := concreteGibbsData hH β
    (gibbsWightmanInner G (diagQubitOpOfSpinFn f) (quantumGlauberGen G (diagQubitOpOfSpinFn f))).re ≤
      (Real.cosh (isingPhiMaxExact β J hfield)) ^ 2 *
        (gibbsWightmanInner G (diagQubitOpOfSpinFn f) (wightmanQ G (diagQubitOpOfSpinFn f))).re := by
  intro hH G
  rw [diagIsing_glauberGen_eq_classical_dirichlet β J hfield f,
    diagIsing_wightmanQ_eq_classical_degreeFiltrationQ β J hfield f]
  exact prop_8_3_classical_ising_reverse_poincare_eq_8_4 hβ J hfield f

end ClassicalIsingLemma82AndQuantumBridge

section Theorem11bQuantifierAlignment

/-- For `s ≥ N`, `filtrationSubmodule N s = filtrationSubmodule N N`. -/
private lemma filtrationSubmodule_eq_top_of_ge {N s : ℕ} (hs : N ≤ s) :
    filtrationSubmodule N s = filtrationSubmodule N N := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, _, rfl⟩
    apply Submodule.subset_span
    refine ⟨a, ?_, rfl⟩
    unfold stringWeight; exact le_trans (Finset.card_filter_le _ _) (by simp)
  · exact filtrationSubmodule_mono N hs

/-- For `s ≥ 2 * n`, `majoranaFiltrationSubmodule n s = majoranaFiltrationSubmodule n (2 * n)`. -/
private lemma majoranaFiltrationSubmodule_eq_top_of_ge {n s : ℕ} (hs : 2 * n ≤ s) :
    majoranaFiltrationSubmodule n s = majoranaFiltrationSubmodule n (2 * n) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨P, _, rfl⟩
    apply Submodule.subset_span
    refine ⟨P, ?_, rfl⟩
    exact le_trans (Finset.card_le_univ P) (by simp)
  · apply Submodule.span_le.mpr
    rintro _ ⟨P, hP, rfl⟩
    exact Submodule.subset_span ⟨P, le_trans hP hs, rfl⟩

private lemma totalSizeOp_smul {N : ℕ} (c : ℂ) (X : QubitOp N) :
    totalSizeOp (c • X) = c • totalSizeOp X := by
  unfold totalSizeOp siteSizeOp partialTraceSite
  simp only [Finset.smul_sum, smul_sub, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  apply Finset.sum_congr rfl; intro x _
  congr 1
  simp only [Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul]
  congr 1; apply Finset.sum_congr rfl; intro α _; ring_nf

/-- For `s = 0`, `lambdaMSS G 0 ≤ 0` because every operator in `filtrationSubmodule N 0` is scalar. -/
private lemma lambdaMSS_zero_le_zero {N : ℕ} (G : GibbsData N) : lambdaMSS G 0 ≤ 0 := by
  unfold lambdaMSS
  by_cases hne : ({ r : ℝ | ∃ A ∈ filtrationSubmodule N 0,
      gibbsWightmanNormSq G A = 1 ∧ r = mssThermalSize G A }).Nonempty
  · apply csSup_le hne
    rintro r ⟨A, hA, hAnorm, rfl⟩
    have hscalar : ∃ c : ℂ, A = c • (1 : QubitOp N) := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
      · rintro _ ⟨a, ha, rfl⟩
        have ha0 : a = fun _ ↦ 0 := by
          funext i; by_contra hi
          have h1 : 1 ≤ (Finset.univ.filter (fun j : Fin N ↦ a j ≠ 0)).card :=
            Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
          unfold stringWeight at ha
          omega
        refine ⟨1, ?_⟩
        rw [ha0, one_smul]
        ext i j; unfold pauliString kronOp; simp only [Matrix.of_apply, Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl]; apply Finset.prod_eq_one; intro k _
          rw [pauliMat_diag_eq, if_pos rfl]
        · rw [if_neg hij]
          have hne_c : ∃ k : Fin N, i k ≠ j k := by by_contra h; push Not at h; exact hij (funext h)
          rcases hne_c with ⟨k, hk⟩
          apply Finset.prod_eq_zero (Finset.mem_univ k)
          generalize h1 : i k = v1; generalize h2 : j k = v2
          rw [h1, h2] at hk; fin_cases v1 <;> fin_cases v2 <;> simp_all [pauliMat]
      · exact ⟨0, by simp⟩
      · rintro X Y _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩; exact ⟨c₁ + c₂, by rw [add_smul]⟩
      · rintro c X _ ⟨c₁, rfl⟩; exact ⟨c * c₁, by rw [smul_smul]⟩
    rcases hscalar with ⟨c, rfl⟩
    have hnorm_c : ‖c‖ ^ 2 = 1 := by
      have h1 : gibbsWightmanNormSq G (c • (1 : QubitOp N)) = ‖c‖ ^ 2 := by
        unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
        simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, Matrix.trace_smul,
          G.sq_half, G.trace_one, smul_eq_mul, mul_one, Complex.star_def]
        rw [mul_comm, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
      linarith
    have hj : jBeta G.ρQuarter (c • (1 : QubitOp N)) = c • G.ρHalf := by
      unfold jBeta; rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, G.sq_quarter]
    unfold mssThermalSize
    rw [hj, totalSizeOp_smul]
    have hin : (hsInner (c • G.ρHalf) (c • totalSizeOp G.ρHalf)).re =
        ‖c‖ ^ 2 * (hsInner G.ρHalf (totalSizeOp G.ρHalf)).re := by
      unfold hsInner
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.trace_smul, smul_eq_mul, Complex.star_def, mul_comm (starRingEnd ℂ c),
        Complex.mul_conj', ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    rw [hin, hnorm_c, one_mul, sub_self]
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]

/-- For `s = 0`, `majoranaLambdaMSS G 0 ≤ 0` because every operator in `majoranaFiltrationSubmodule n 0` is scalar. -/
private lemma majoranaLambdaMSS_zero_le_zero {n : ℕ} (G : GibbsData n) :
    majoranaLambdaMSS G 0 ≤ 0 := by
  unfold majoranaLambdaMSS
  by_cases hne : ({ x : ℝ | ∃ A : QubitOp n, A ∈ majoranaFiltrationSubmodule n 0 ∧
      gibbsWightmanNormSq G A = 1 ∧ x = majoranaThermalSize G A }).Nonempty
  · apply csSup_le hne
    rintro r ⟨A, hA, hAnorm, rfl⟩
    have hscalar : ∃ c : ℂ, A = c • (1 : QubitOp n) := by
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
      · rintro _ ⟨P, hP, rfl⟩
        have hP0 : P = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hP)
        subst hP0
        exact ⟨1, by simp [majoranaString]⟩
      · exact ⟨0, by simp⟩
      · rintro X Y _ _ ⟨c₁, rfl⟩ ⟨c₂, rfl⟩; exact ⟨c₁ + c₂, by rw [add_smul]⟩
      · rintro c X _ ⟨c₁, rfl⟩; exact ⟨c * c₁, by rw [smul_smul]⟩
    rcases hscalar with ⟨c, rfl⟩
    have hnorm_c : ‖c‖ ^ 2 = 1 := by
      have h1 : gibbsWightmanNormSq G (c • (1 : QubitOp n)) = ‖c‖ ^ 2 := by
        unfold gibbsWightmanNormSq gibbsWightmanInner wightmanInner
        simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, Matrix.trace_smul,
          G.sq_half, G.trace_one, smul_eq_mul, mul_one, Complex.star_def]
        rw [mul_comm, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
      linarith
    have hj : jBeta G.ρQuarter (c • (1 : QubitOp n)) = c • G.ρHalf := by
      unfold jBeta; rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, G.sq_quarter]
    have hmsmul : majoranaParitySizeOp n (c • G.ρHalf) = c • majoranaParitySizeOp n G.ρHalf := by
      unfold majoranaParitySizeOp majoranaTotalSizeOp majoranaOddTotalSizeOp
        majoranaModeSizeOp majoranaOddModeSizeOp evenPart oddPart
      simp only [Finset.smul_sum, smul_add, smul_sub, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring_nf
    unfold majoranaThermalSize
    rw [hj, hmsmul]
    have hin : (hsInner (c • G.ρHalf) (c • majoranaParitySizeOp n G.ρHalf)).re =
        ‖c‖ ^ 2 * (hsInner G.ρHalf (majoranaParitySizeOp n G.ρHalf)).re := by
      unfold hsInner
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.trace_smul, smul_eq_mul, Complex.star_def, mul_comm (starRingEnd ℂ c),
        Complex.mul_conj', ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    rw [hin, hnorm_c, one_mul, sub_self]
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]

/-- **Theorem 1.1(b) (Qubit Family with Bounded `1 ≤ s ≤ N` Quantifier on (H2))**:
Matches the static quantifier `∀ N s, 1 ≤ N → 1 ≤ s → s ≤ N → Λ_β^{MSS}(s) ≤ C₁ s + C₂ N^δ s^{1-δ}`. -/
theorem theorem_1_1b_family_concrete_qubit_bounded_s
    {r s₀ : ℕ} (hr : 1 ≤ r) {α γ lamL δ C₁ C₂ : ℝ} (β : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hlam : 0 < lamL)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (H_N O_N : (N : ℕ) → QubitOp N)
    (hH : ∀ N, (H_N N).IsHermitian) (hO : ∀ N, (O_N N).IsHermitian)
    (hHf : ∀ N, H_N N ∈ filtrationSubmodule N r)
    (hOf : ∀ N, O_N N ∈ filtrationSubmodule N s₀)
    (hOnorm : ∀ N, gibbsWightmanNormSq (concreteGibbsData (hH N) β) (O_N N) = 1)
    (hb_lin : ∀ N n, 1 ≤ n → n ≤ 4 ^ N - 1 →
      lanczosCoeff (concreteGibbsData (hH N) β) (H_N N) (O_N N) n ≤ α * (n : ℝ) + γ)
    (hH2 : ∀ (N s : ℕ), 1 ≤ N → 1 ≤ s → s ≤ N →
      lambdaMSS (concreteGibbsData (hH N) β) s ≤
        C₁ * (s : ℝ) + C₂ * (N : ℝ) ^ δ * ((s : ℝ) ^ (1 - δ)))
    (hH1 : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        let tN := ((1 - ε) / lamL) * Real.log (N : ℝ)
        c * (N : ℝ) ^ (1 - ε) ≤
          mssThermalSize (concreteGibbsData (hH N) β)
            (heisenbergEvol (hH N) (tN : ℂ) (O_N N))) :
    lamL ≤ 2 * α := by
  refine theorem_1_1b_family_concrete_qubit hr β hα hγ hlam hδ0 hδ1 hC₁ hC₂
    H_N O_N hH hO hHf hOf hOnorm hb_lin ?_ hH1
  intro N s hN
  by_cases hs0 : s = 0
  · subst hs0
    have h0 := lambdaMSS_zero_le_zero (concreteGibbsData (hH N) β)
    have hrhs : 0 ≤ C₁ * (0 : ℝ) + C₂ * (N : ℝ) ^ δ * ((0 : ℝ) ^ (1 - δ)) := by
      have : (0 : ℝ) ^ (1 - δ) = 0 := Real.zero_rpow (by linarith)
      simp [this]
    simpa using le_trans h0 hrhs
  · have hs1 : 1 ≤ s := Nat.pos_of_ne_zero hs0
    by_cases hsN : s ≤ N
    · exact hH2 N s hN hs1 hsN
    · push Not at hsN
      have heq : lambdaMSS (concreteGibbsData (hH N) β) s =
          lambdaMSS (concreteGibbsData (hH N) β) N := by
        unfold lambdaMSS; rw [filtrationSubmodule_eq_top_of_ge hsN.le]
      rw [heq]
      have hN_bd := hH2 N N hN hN le_rfl
      have hNs : (N : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsN.le
      have hrpow_le : (N : ℝ) ^ (1 - δ) ≤ (s : ℝ) ^ (1 - δ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg N) hNs (by linarith)
      calc lambdaMSS (concreteGibbsData (hH N) β) N
          ≤ C₁ * (N : ℝ) + C₂ * (N : ℝ) ^ δ * (N : ℝ) ^ (1 - δ) := hN_bd
        _ ≤ C₁ * (s : ℝ) + C₂ * (N : ℝ) ^ δ * (s : ℝ) ^ (1 - δ) :=
            add_le_add (mul_le_mul_of_nonneg_left hNs hC₁)
              (mul_le_mul_of_nonneg_left hrpow_le (mul_nonneg hC₂ (Real.rpow_nonneg (Nat.cast_nonneg N) δ)))

/-- **Theorem 1.1(b) (Majorana Family with `1 ≤ s ≤ 2 * n` and `2 * n`-Normalized Scrambling Time)**:
Matches the Majorana normalization `N_Maj = 2 * n` in BOTH (H1) (`t_n = ((1 - ε) / λ_L) log(2 n)`,
`c * (2 n)^{1 - ε} ≤ S_β^{Maj}`) and (H2) (`∀ n s, 1 ≤ n → 1 ≤ s → s ≤ 2 * n → ...`). -/
theorem theorem_1_1b_family_majorana_2n_normalized {r s₀ : ℕ} (hr : 1 ≤ r)
    {α γ C₁ C₂ δ lamL : ℝ} (β : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hlam : 0 < lamL)
    (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (H_n O_n : (n : ℕ) → QubitOp n)
    (hH : ∀ n, (H_n n).IsHermitian) (hO : ∀ n, (O_n n).IsHermitian)
    (hHf : ∀ n, H_n n ∈ majoranaEvenFiltrationSubmodule n r)
    (hOf : ∀ n, O_n n ∈ majoranaFiltrationSubmodule n s₀)
    (hOnorm : ∀ n, gibbsWightmanNormSq (concreteGibbsData (hH n) β) (O_n n) = 1)
    (hb_lin : ∀ n k, 1 ≤ k → k ≤ 4 ^ n - 1 →
      lanczosCoeff (concreteGibbsData (hH n) β) (H_n n) (O_n n) k ≤ α * (k : ℝ) + γ)
    (hH2 : ∀ (n s : ℕ), 1 ≤ n → 1 ≤ s → s ≤ 2 * n →
      majoranaLambdaMSS (concreteGibbsData (hH n) β) s ≤
        C₁ * (s : ℝ) + C₂ * ((2 * n : ℕ) : ℝ) ^ δ * ((s : ℝ) ^ (1 - δ)))
    (hH1 : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ n ≥ N₁,
        let tn := ((1 - ε) / lamL) * Real.log ((2 * n : ℕ) : ℝ)
        c * ((2 * n : ℕ) : ℝ) ^ (1 - ε) ≤
          majoranaThermalSize (concreteGibbsData (hH n) β)
            (heisenbergEvol (hH n) (tn : ℂ) (O_n n))) :
    lamL ≤ 2 * α := by
  by_contra hgt; push Not at hgt
  have hH2_all : ∀ (n s : ℕ), 1 ≤ n →
      majoranaLambdaMSS (concreteGibbsData (hH n) β) s ≤
        C₁ * (s : ℝ) + C₂ * ((2 * n : ℕ) : ℝ) ^ δ * ((s : ℝ) ^ (1 - δ)) := by
    intro n s hn
    by_cases hs0 : s = 0
    · subst hs0
      have h0 := majoranaLambdaMSS_zero_le_zero (concreteGibbsData (hH n) β)
      have : (0 : ℝ) ^ (1 - δ) = 0 := Real.zero_rpow (by linarith)
      simp [this]; exact h0
    · have hs1 : 1 ≤ s := Nat.pos_of_ne_zero hs0
      by_cases hs2n : s ≤ 2 * n
      · exact hH2 n s hn hs1 hs2n
      · push Not at hs2n
        have heq : majoranaLambdaMSS (concreteGibbsData (hH n) β) s =
            majoranaLambdaMSS (concreteGibbsData (hH n) β) (2 * n) := by
          unfold majoranaLambdaMSS; rw [majoranaFiltrationSubmodule_eq_top_of_ge hs2n.le]
        rw [heq]
        have h2n_bd := hH2 n (2 * n) hn (by omega) le_rfl
        have hle : ((2 * n : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2n.le
        have hrpow_le : ((2 * n : ℕ) : ℝ) ^ (1 - δ) ≤ (s : ℝ) ^ (1 - δ) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by linarith)
        calc majoranaLambdaMSS (concreteGibbsData (hH n) β) (2 * n)
            ≤ C₁ * ((2 * n : ℕ) : ℝ) + C₂ * ((2 * n : ℕ) : ℝ) ^ δ * ((2 * n : ℕ) : ℝ) ^ (1 - δ) := h2n_bd
          _ ≤ C₁ * (s : ℝ) + C₂ * ((2 * n : ℕ) : ℝ) ^ δ * (s : ℝ) ^ (1 - δ) :=
              add_le_add (mul_le_mul_of_nonneg_left hle hC₁)
                (mul_le_mul_of_nonneg_left hrpow_le (mul_nonneg hC₂ (Real.rpow_nonneg (Nat.cast_nonneg _) δ)))
  have hratio_lt : 2 * α / lamL < 1 := (div_lt_one hlam).mpr hgt
  set ε₀ : ℝ := min ((1 - δ) * (1 - 2 * α / lamL) / 2) (1 / 2)
  have hε₀ : 0 < ε₀ := lt_min (by nlinarith) (by norm_num)
  rcases hH1 ε₀ hε₀ with ⟨ε, ⟨hε_pos, hε_lt⟩, c, hc_pos, N₁, hN₁⟩
  have hε_half : ε < 1 / 2 := lt_of_lt_of_le hε_lt (min_le_right _ _)
  have hε_gap : ε < (1 - δ) * (1 - 2 * α / lamL) / 2 := lt_of_lt_of_le hε_lt (min_le_left _ _)
  set η : ℝ := (1 - ε) * (2 * α / lamL)
  have hη_pos : 0 < η := by dsimp only [η]; positivity
  have hη_lt : η < 1 - ε := by dsimp only [η]; nlinarith
  have hδ_lt : δ + (1 - δ) * η < 1 - ε := by
    have h1 : η ≤ 2 * α / lamL := by dsimp only [η]; nlinarith [div_pos (by linarith : 0 < 2 * α) hlam]
    nlinarith
  set E₀ : ℝ := Real.exp ((1 / 2 + γ / α) * 4)
  have hE₀_pos : 0 < E₀ := Real.exp_pos _
  have htanh1 : (2 : ℝ) ≤ 4 * Real.tanh 1 := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
    have he1 : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
    have heinv : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hden : 0 < (Real.exp 1 + Real.exp (-1)) / 2 := by linarith [Real.exp_pos (1 : ℝ), Real.exp_pos (-1 : ℝ)]
    rw [mul_div_assoc', le_div_iff₀ hden]
    nlinarith [Real.exp_pos (-1 : ℝ)]
  set a : ℝ := min ((1 - ε - η) / 2) ((1 - ε - (δ + (1 - δ) * η)) / 2)
  have ha_pos : 0 < a := lt_min (by linarith) (by linarith)
  have hlog_little : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ x ^ a := by
    refine Filter.eventually_atTop.mpr ⟨max 2 ((2 / a) ^ (2 / a)), fun x hx ↦ ?_⟩
    have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
    have hx_pos : 0 < x := by linarith
    have ha2_pos : 0 < a / 2 := by linarith
    have hlog_half : (a / 2) * Real.log x ≤ x ^ (a / 2) := by
      have h1 : Real.log (x ^ (a / 2)) ≤ x ^ (a / 2) := Real.log_le_self (Real.rpow_pos_of_pos hx_pos _).le
      rwa [Real.log_rpow hx_pos] at h1
    have h2a_le : 2 / a ≤ x ^ (a / 2) := by
      have hx_ge : (2 / a) ^ (2 / a) ≤ x := le_trans (le_max_right _ _) hx
      have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hx_ge ha2_pos.le
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 / a)] at hpow
      have hmul1 : (2 / a) * (a / 2) = 1 := by field_simp [ha_pos.ne']
      rw [hmul1, Real.rpow_one] at hpow
      exact hpow
    have hlog_bd : Real.log x ≤ (2 / a) * x ^ (a / 2) := by
      have := mul_le_mul_of_nonneg_left hlog_half (show 0 ≤ 2 / a by positivity)
      have hcancel : (2 / a) * ((a / 2) * Real.log x) = Real.log x := by field_simp [ha_pos.ne']
      linarith
    calc Real.log x ≤ (2 / a) * x ^ (a / 2) := hlog_bd
      _ ≤ x ^ (a / 2) * x ^ (a / 2) := mul_le_mul_of_nonneg_right h2a_le (Real.rpow_nonneg hx_pos.le _)
      _ = x ^ (a / 2 + a / 2) := (Real.rpow_add hx_pos _ _).symm
      _ = x ^ a := by congr 1; ring
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp hlog_little
  set K_s : ℝ := (s₀ : ℝ) + ((r - 1 : ℕ) : ℝ) * 3
  have hKs_nn : 0 ≤ K_s := by dsimp only [K_s]; positivity
  set B_tail : ℝ := 2 * Real.sqrt E₀ + E₀
  have hBtail_nn : 0 ≤ B_tail := by dsimp only [B_tail]; linarith [Real.sqrt_nonneg E₀, hE₀_pos]
  have hexp1 : η + a - (1 - ε) < 0 := by
    have : a ≤ (1 - ε - η) / 2 := min_le_left _ _; linarith
  have hexp2 : δ + (1 - δ) * (η + a) - (1 - ε) < 0 := by
    have : a ≤ (1 - ε - (δ + (1 - δ) * η)) / 2 := min_le_right _ _
    have : (1 - δ) * a ≤ a := by nlinarith
    linarith
  have hexp3 : -(1 - ε) < 0 := by linarith
  have h2n_top : Filter.Tendsto (fun n : ℕ ↦ ((2 * n : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have h1 : (fun n : ℕ ↦ ((2 * n : ℕ) : ℝ)) = fun n : ℕ ↦ 2 * (n : ℝ) := by funext n; push_cast; rfl
    rw [h1]
    exact Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have hlim1 : Filter.Tendsto (fun n : ℕ ↦ ((2 * n : ℕ) : ℝ) ^ (η + a - (1 - ε))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < -(η + a - (1 - ε)))).comp h2n_top |>.congr
      fun n ↦ by dsimp only [Function.comp_apply]; congr 1; ring
  have hlim2 : Filter.Tendsto (fun n : ℕ ↦ ((2 * n : ℕ) : ℝ) ^ (δ + (1 - δ) * (η + a) - (1 - ε))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < -(δ + (1 - δ) * (η + a) - (1 - ε)))).comp h2n_top |>.congr
      fun n ↦ by dsimp only [Function.comp_apply]; congr 1; ring
  have hlim3 : Filter.Tendsto (fun n : ℕ ↦ ((2 * n : ℕ) : ℝ) ^ (-(1 - ε))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - ε)).comp h2n_top
  have hlim_tot : Filter.Tendsto (fun n : ℕ ↦
      C₁ * K_s * ((2 * n : ℕ) : ℝ) ^ (η + a - (1 - ε)) +
      C₂ * K_s ^ (1 - δ) * ((2 * n : ℕ) : ℝ) ^ (δ + (1 - δ) * (η + a) - (1 - ε)) +
      B_tail * ((2 * n : ℕ) : ℝ) ^ (-(1 - ε))) Filter.atTop (nhds 0) := by
    simpa using ((hlim1.const_mul (C₁ * K_s)).add (hlim2.const_mul (C₂ * K_s ^ (1 - δ)))).add
      (hlim3.const_mul B_tail)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hlim_tot) c hc_pos
  set n : ℕ := max (max N₁ N₂) (max (Nat.ceil X₀ + 2) 2)
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) (le_max_left _ _)
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) (le_max_left _ _)
  have hn_ge2 : 2 ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
  have hn_pos : 1 ≤ n := by omega
  set x : ℝ := ((2 * n : ℕ) : ℝ)
  have hx_ge4 : (4 : ℝ) ≤ x := by dsimp only [x]; exact_mod_cast (by omega : 4 ≤ 2 * n)
  have hx_pos : 0 < x := by linarith
  have hx_geX0 : X₀ ≤ x := by
    have h1 : Nat.ceil X₀ + 2 ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 : X₀ ≤ (Nat.ceil X₀ : ℝ) := Nat.le_ceil X₀
    have h3 : (Nat.ceil X₀ : ℝ) ≤ x := by dsimp only [x]; exact_mod_cast (by omega : Nat.ceil X₀ ≤ 2 * n)
    linarith
  have hlog_le : Real.log x ≤ x ^ a := hX₀ x hx_geX0
  have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
  set tn : ℝ := ((1 - ε) / lamL) * Real.log x
  have htn_nn : 0 ≤ tn := mul_nonneg (div_nonneg (by linarith) hlam.le) hlog_pos.le
  set M : ℕ := Nat.ceil (2 * Real.log x * x ^ η) + 1
  have hM_ge1 : 1 ≤ M := Nat.succ_pos _
  have h11b := theorem_1_1b_majorana_concrete hr hM_ge1 (hH n) (hO n) β (hHf n) (hOf n)
    (hOnorm n) hα hγ (by norm_num : (0 : ℝ) < 4) (hb_lin n) tn htn_nn
  have hlow := hN₁ n hn1
  have hexp_tn : Real.exp (2 * α * tn) = x ^ η := by
    rw [Real.rpow_def_of_pos hx_pos]; congr 1; dsimp only [η, tn]; ring
  have hexp_neg_tn : Real.exp (-2 * α * tn) = (x ^ η)⁻¹ := by
    rw [show -2 * α * tn = -(2 * α * tn) by ring, Real.exp_neg, hexp_tn]
  have hqM_le : E₀ * Real.exp (-4 * Real.tanh (4 / 4) * (M : ℝ) * Real.exp (-2 * α * tn)) ≤ E₀ * x ^ (-4 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ hE₀_pos.le
    rw [show (4 : ℝ) / 4 = 1 by norm_num, hexp_neg_tn]
    have hM_ge : 2 * Real.log x * x ^ η ≤ (M : ℝ) := by
      have := Nat.le_ceil (2 * Real.log x * x ^ η)
      dsimp only [M]; push_cast; linarith
    have hprod_ge : 4 * Real.log x ≤ 4 * Real.tanh 1 * (M : ℝ) * (x ^ η)⁻¹ := by
      have hxη_pos : 0 < x ^ η := Real.rpow_pos_of_pos hx_pos η
      calc 4 * Real.log x = 2 * (2 * Real.log x * x ^ η) * (x ^ η)⁻¹ := by
              field_simp [hxη_pos.ne']; ring
        _ ≤ (4 * Real.tanh 1) * (M : ℝ) * (x ^ η)⁻¹ := by
              apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hxη_pos.le)
              exact mul_le_mul htanh1 hM_ge (by positivity) (by linarith)
    calc Real.exp (-4 * Real.tanh 1 * (M : ℝ) * (x ^ η)⁻¹)
        ≤ Real.exp (-(4 * Real.log x)) := Real.exp_le_exp.mpr (by linarith)
      _ = x ^ (-4 : ℝ) := by rw [Real.rpow_def_of_pos hx_pos]; congr 1; ring
  have htail_le : 2 * x * Real.sqrt (E₀ * Real.exp (-4 * Real.tanh (4 / 4) * (M : ℝ) * Real.exp (-2 * α * tn))) +
      x * (E₀ * Real.exp (-4 * Real.tanh (4 / 4) * (M : ℝ) * Real.exp (-2 * α * tn))) ≤ B_tail := by
    have hsqrt_q : Real.sqrt (E₀ * x ^ (-4 : ℝ)) = Real.sqrt E₀ * x ^ (-2 : ℝ) := by
      rw [Real.sqrt_mul hE₀_pos.le, Real.sqrt_eq_rpow (x ^ (-4 : ℝ)), ← Real.rpow_mul hx_pos.le]
      congr 2; norm_num
    have hx_m1 : x * x ^ (-2 : ℝ) ≤ 1 := by
      have : x * x ^ (-2 : ℝ) = x ^ (-1 : ℝ) := by
        calc x * x ^ (-2 : ℝ) = x ^ (1 : ℝ) * x ^ (-2 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ ((1 : ℝ) + (-2 : ℝ)) := (Real.rpow_add hx_pos _ _).symm
          _ = x ^ (-1 : ℝ) := by norm_num
      rw [this, Real.rpow_neg_one]; exact inv_le_one_of_one_le₀ (by linarith)
    have hx_m3 : x * x ^ (-4 : ℝ) ≤ 1 := by
      have : x * x ^ (-4 : ℝ) = x ^ (-3 : ℝ) := by
        calc x * x ^ (-4 : ℝ) = x ^ (1 : ℝ) * x ^ (-4 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ ((1 : ℝ) + (-4 : ℝ)) := (Real.rpow_add hx_pos _ _).symm
          _ = x ^ (-3 : ℝ) := by norm_num
      rw [this, Real.rpow_neg hx_pos.le]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) (by norm_num))
    have h1 : 2 * x * Real.sqrt (E₀ * Real.exp (-4 * Real.tanh (4 / 4) * (M : ℝ) * Real.exp (-2 * α * tn))) ≤
        2 * Real.sqrt E₀ := by
      calc 2 * x * Real.sqrt (E₀ * Real.exp (-4 * Real.tanh (4 / 4) * (M : ℝ) * Real.exp (-2 * α * tn)))
          ≤ 2 * x * Real.sqrt (E₀ * x ^ (-4 : ℝ)) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqM_le) (by positivity)
        _ = 2 * Real.sqrt E₀ * (x * x ^ (-2 : ℝ)) := by rw [hsqrt_q]; ring
        _ ≤ 2 * Real.sqrt E₀ * 1 := mul_le_mul_of_nonneg_left hx_m1 (by positivity)
        _ = 2 * Real.sqrt E₀ := mul_one _
    have h2 : x * (E₀ * Real.exp (-4 * Real.tanh (4 / 4) * (M : ℝ) * Real.exp (-2 * α * tn))) ≤ E₀ := by
      calc x * (E₀ * Real.exp (-4 * Real.tanh (4 / 4) * (M : ℝ) * Real.exp (-2 * α * tn)))
          ≤ x * (E₀ * x ^ (-4 : ℝ)) := mul_le_mul_of_nonneg_left hqM_le hx_pos.le
        _ = E₀ * (x * x ^ (-4 : ℝ)) := by ring
        _ ≤ E₀ * 1 := mul_le_mul_of_nonneg_left hx_m3 hE₀_pos.le
        _ = E₀ := mul_one _
    dsimp only [B_tail]; linarith
  have hs_le : ((s₀ + (M - 1) * (r - 1) : ℕ) : ℝ) ≤ K_s * x ^ (η + a) := by
    have hM1 : ((M - 1 : ℕ) : ℝ) ≤ 3 * x ^ (η + a) := by
      have hceil : (Nat.ceil (2 * Real.log x * x ^ η) : ℝ) < 2 * Real.log x * x ^ η + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have hxa : Real.log x * x ^ η ≤ x ^ (η + a) := by
        rw [Real.rpow_add hx_pos, mul_comm (x ^ η)]
        exact mul_le_mul_of_nonneg_right hlog_le (Real.rpow_nonneg hx_pos.le η)
      have h1_le : (1 : ℝ) ≤ x ^ (η + a) := Real.one_le_rpow (by linarith) (by linarith)
      have hM_sub : ((M - 1 : ℕ) : ℝ) = (Nat.ceil (2 * Real.log x * x ^ η) : ℝ) := by
        dsimp only [M]; simp
      rw [hM_sub]
      linarith
    have h1_le : (1 : ℝ) ≤ x ^ (η + a) := Real.one_le_rpow (by linarith) (by linarith)
    push_cast; dsimp only [K_s]; nlinarith [Nat.cast_nonneg (α := ℝ) s₀, Nat.cast_nonneg (α := ℝ) (r - 1)]
  have hlam_bd := hH2_all n (s₀ + (M - 1) * (r - 1)) hn_pos
  have hcomb : c * x ^ (1 - ε) ≤
      C₁ * K_s * x ^ (η + a) + C₂ * K_s ^ (1 - δ) * x ^ (δ + (1 - δ) * (η + a)) + B_tail := by
    have hrpow_s : ((s₀ + (M - 1) * (r - 1) : ℕ) : ℝ) ^ (1 - δ) ≤
        K_s ^ (1 - δ) * x ^ ((1 - δ) * (η + a)) := by
      calc ((s₀ + (M - 1) * (r - 1) : ℕ) : ℝ) ^ (1 - δ)
          ≤ (K_s * x ^ (η + a)) ^ (1 - δ) := Real.rpow_le_rpow (Nat.cast_nonneg _) hs_le (by linarith)
        _ = K_s ^ (1 - δ) * (x ^ (η + a)) ^ (1 - δ) := Real.mul_rpow hKs_nn (Real.rpow_nonneg hx_pos.le _)
        _ = K_s ^ (1 - δ) * x ^ ((1 - δ) * (η + a)) := by
            rw [← Real.rpow_mul hx_pos.le]; congr 2; ring
    have hC2_term : C₂ * x ^ δ * ((s₀ + (M - 1) * (r - 1) : ℕ) : ℝ) ^ (1 - δ) ≤
        C₂ * K_s ^ (1 - δ) * x ^ (δ + (1 - δ) * (η + a)) := by
      calc C₂ * x ^ δ * ((s₀ + (M - 1) * (r - 1) : ℕ) : ℝ) ^ (1 - δ)
          ≤ C₂ * x ^ δ * (K_s ^ (1 - δ) * x ^ ((1 - δ) * (η + a))) :=
            mul_le_mul_of_nonneg_left hrpow_s (mul_nonneg hC₂ (Real.rpow_nonneg hx_pos.le δ))
        _ = C₂ * K_s ^ (1 - δ) * (x ^ δ * x ^ ((1 - δ) * (η + a))) := by ring
        _ = C₂ * K_s ^ (1 - δ) * x ^ (δ + (1 - δ) * (η + a)) := by rw [← Real.rpow_add hx_pos]
    have hC1_term : C₁ * ((s₀ + (M - 1) * (r - 1) : ℕ) : ℝ) ≤ C₁ * K_s * x ^ (η + a) := by
      calc C₁ * ((s₀ + (M - 1) * (r - 1) : ℕ) : ℝ) ≤ C₁ * (K_s * x ^ (η + a)) :=
              mul_le_mul_of_nonneg_left hs_le hC₁
        _ = C₁ * K_s * x ^ (η + a) := by ring
    dsimp only [x, tn, E₀] at hlow h11b hlam_bd htail_le hC1_term hC2_term ⊢
    linarith
  have hx1e_pos : 0 < x ^ (1 - ε) := Real.rpow_pos_of_pos hx_pos (1 - ε)
  have hdiv : c ≤ C₁ * K_s * x ^ (η + a - (1 - ε)) +
      C₂ * K_s ^ (1 - δ) * x ^ (δ + (1 - δ) * (η + a) - (1 - ε)) +
      B_tail * x ^ (-(1 - ε)) := by
    have h := div_le_div_of_nonneg_right hcomb hx1e_pos.le
    rw [mul_div_cancel_right₀ c hx1e_pos.ne'] at h
    have hr1 : x ^ (η + a) / x ^ (1 - ε) = x ^ (η + a - (1 - ε)) := (Real.rpow_sub hx_pos _ _).symm
    have hr2 : x ^ (δ + (1 - δ) * (η + a)) / x ^ (1 - ε) = x ^ (δ + (1 - δ) * (η + a) - (1 - ε)) :=
      (Real.rpow_sub hx_pos _ _).symm
    have hr3 : (1 : ℝ) / x ^ (1 - ε) = x ^ (-(1 - ε)) := by rw [Real.rpow_neg hx_pos.le, one_div]
    calc c ≤ (C₁ * K_s * x ^ (η + a) + C₂ * K_s ^ (1 - δ) * x ^ (δ + (1 - δ) * (η + a)) + B_tail) / x ^ (1 - ε) := h
      _ = C₁ * K_s * (x ^ (η + a) / x ^ (1 - ε)) +
          C₂ * K_s ^ (1 - δ) * (x ^ (δ + (1 - δ) * (η + a)) / x ^ (1 - ε)) +
          B_tail * (1 / x ^ (1 - ε)) := by ring
      _ = _ := by rw [hr1, hr2, hr3]
  have hsmall := hN₂ n hn2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmall
  dsimp only [x] at hdiv
  linarith

end Theorem11bQuantifierAlignment

section ExtendedProp64Part2

/-- **Proposition 6.4(2) (Extended High-Temperature Domain `0 ≤ β ≤ 1 / (8 e² r Jsite)`, Eq. 6.7)**:
Establishes the background decoupling bound and Eq. (6.7) on the full extended high-temperature
domain `0 ≤ β ≤ 1 / (8 * e² * r * Jsite)` without requiring the smaller `highTempBetaWC` threshold. -/
theorem prop_6_4_part2_extended {N r s₀ : ℕ}
    (hN : 1 ≤ N) (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hE_ne : ∀ Z ∈ E, Z.Nonempty) (hE_card : ∀ Z ∈ E, Z.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hh_supp : ∀ Z, h Z ∈ supportedOn Z)
    (hH : (∑ Z ∈ E, h Z).IsHermitian)
    {Jsite : ℝ} (hJ : 0 < Jsite)
    (hH_site : ∀ x : Fin N, ∑ Z ∈ E.filter (fun Z ↦ x ∈ Z), opNorm (h Z) ≤ Jsite)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ_cum : β ≤ 1 / (8 * Real.exp 2 * (r : ℝ) * Jsite))
    {U₀ : Finset (Fin N)} (hU₀ : U₀.card ≤ s₀)
    {O : QubitOp N} (hO_supp : O ∈ supportedOn U₀)
    (hOnorm : gibbsWightmanNormSq (concreteGibbsData hH β) O = 1)
    {C_O : ℝ} (hCO_ge1 : 1 ≤ C_O) (hCO : opNorm O ≤ C_O) (t : ℝ) :
    let G := concreteGibbsData hH β
    let Ot := heisenbergEvol hH (t : ℂ) O
    |shiftedThermalSizeIII hH β Ot| ≤ bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ) ∧
    ((G.ρβ * thermalBackgroundOp hH β).trace).re ≤ (N : ℝ) ∧
    mssThermalSize G Ot ≤
      otocI hH β Ot +
      2 * Real.sqrt (otocI hH β Ot) * Real.sqrt ((N : ℝ) + bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ)) +
      bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ) := by
  intro G Ot
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hβ_q : β * Real.exp 1 * (r : ℝ) * Jsite ≤ 1 / 16 := by
    have h1 : β * (8 * Real.exp 2 * (r : ℝ) * Jsite) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hβ_cum (by positivity : 0 ≤ 8 * Real.exp 2 * (r : ℝ) * Jsite)
      rwa [one_div_mul_cancel (by positivity)] at this
    have he1_gt2 : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
    have he2_eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h2 : 16 * (β * Real.exp 1 * (r : ℝ) * Jsite) ≤
        β * (8 * Real.exp 2 * (r : ℝ) * Jsite) := by
      rw [he2_eq]
      have hnn : 0 ≤ β * (r : ℝ) * Jsite := by positivity
      have hprod : (16 : ℝ) * Real.exp 1 ≤ 8 * (Real.exp 1 * Real.exp 1) := by nlinarith [Real.exp_pos 1]
      calc 16 * (β * Real.exp 1 * (r : ℝ) * Jsite)
          = (16 * Real.exp 1) * (β * (r : ℝ) * Jsite) := by ring
        _ ≤ (8 * (Real.exp 1 * Real.exp 1)) * (β * (r : ℝ) * Jsite) :=
            mul_le_mul_of_nonneg_right hprod hnn
        _ = β * (8 * (Real.exp 1 * Real.exp 1) * (r : ℝ) * Jsite) := by ring
    linarith
  have hD_le : gibbsRelEntropy (rhoO_op_isHermitian hH β O) hH β ≤
      2 * Real.log (C_O * (2 : ℝ) ^ (s₀ + 1)) := by
    have hrel := rhoO_op_relEntropy_le_two_log_opNorm hH β O hOnorm
    have hz_small : 2 * ‖Complex.I * ((β / 4 : ℝ) : ℂ)‖ * (r : ℝ) * Jsite ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ β / 4)]
      have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith [hβ_q]
    have hbd := heisenbergEvol_concrete_norm_bound (by omega : 1 ≤ r) E hE_card h hh_supp hH hJ.le
      hH_site hO_supp (Complex.I * ((β / 4 : ℝ) : ℂ)) (by linarith)
    set q := 2 * ‖Complex.I * ((β / 4 : ℝ) : ℂ)‖ * (r : ℝ) * Jsite
    have hq_nn : 0 ≤ q := by dsimp only [q]; positivity
    have hq_le_quarter : q ≤ 1 / 4 := by
      dsimp only [q]
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ β / 4)]
      have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith [hβ_q]
    have htsum_le : ∑' k : ℕ, ((k + U₀.card).choose U₀.card : ℝ) * q ^ k ≤ (2 : ℝ) ^ (U₀.card + 1) := by
      have hterm : ∀ k : ℕ, ((k + U₀.card).choose U₀.card : ℝ) * q ^ k ≤
          (2 : ℝ) ^ U₀.card * ((1 / 2 : ℝ) ^ k) := by
        intro k
        have hch : ((k + U₀.card).choose U₀.card : ℝ) ≤ (2 : ℝ) ^ (k + U₀.card) := by
          exact_mod_cast Nat.choose_le_two_pow (k + U₀.card) U₀.card
        have hqk : q ^ k ≤ (1 / 4 : ℝ) ^ k := pow_le_pow_left₀ hq_nn hq_le_quarter k
        calc ((k + U₀.card).choose U₀.card : ℝ) * q ^ k
            ≤ (2 : ℝ) ^ (k + U₀.card) * (1 / 4 : ℝ) ^ k :=
              mul_le_mul hch hqk (pow_nonneg hq_nn k) (by positivity)
          _ = (2 : ℝ) ^ U₀.card * ((2 : ℝ) * (1 / 4 : ℝ)) ^ k := by rw [pow_add, mul_pow]; ring
          _ = (2 : ℝ) ^ U₀.card * (1 / 2 : ℝ) ^ k := by norm_num
      have hsumm_g : Summable (fun k : ℕ ↦ (2 : ℝ) ^ U₀.card * (1 / 2 : ℝ) ^ k) :=
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      have hsumm_l : Summable (fun k : ℕ ↦ ((k + U₀.card).choose U₀.card : ℝ) * q ^ k) :=
        Summable.of_nonneg_of_le (fun _ ↦ by positivity) hterm hsumm_g
      calc ∑' k : ℕ, ((k + U₀.card).choose U₀.card : ℝ) * q ^ k
          ≤ ∑' k : ℕ, (2 : ℝ) ^ U₀.card * (1 / 2 : ℝ) ^ k := hsumm_l.tsum_le_tsum hterm hsumm_g
        _ = (2 : ℝ) ^ U₀.card * ∑' k : ℕ, (1 / 2 : ℝ) ^ k := tsum_mul_left
        _ = (2 : ℝ) ^ U₀.card * 2 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
        _ = (2 : ℝ) ^ (U₀.card + 1) := by rw [pow_succ]
    have hop_le : opNorm (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) O) ≤
        C_O * (2 : ℝ) ^ (s₀ + 1) := by
      calc opNorm (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) O)
          ≤ opNorm O * ∑' k : ℕ, ((k + U₀.card).choose U₀.card : ℝ) * q ^ k := hbd
        _ ≤ C_O * (2 : ℝ) ^ (U₀.card + 1) :=
            mul_le_mul hCO htsum_le (tsum_nonneg fun _ ↦ by positivity) (by positivity)
        _ ≤ C_O * (2 : ℝ) ^ (s₀ + 1) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
    have hop_pos : 0 < opNorm (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) O) := by
      by_contra hle; push Not at hle
      have h0 : opNorm (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) O) = 0 :=
        le_antisymm hle (opNorm_nonneg _)
      have hmat0 : heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) O = 0 := by
        have hclm : opToCLM (heisenbergEvol hH (Complex.I * ((β / 4 : ℝ) : ℂ)) O) = 0 :=
          norm_eq_zero.mp h0
        ext i j
        have he := congrArg (fun f ↦ (f (EuclideanSpace.single j (1 : ℂ))).ofLp i) hclm
        simpa [opToCLM, Matrix.mulVec, dotProduct] using he
      have hO0 : O = 0 := by
        have hinv := heisenbergEvol_add hH (-Complex.I * ((β / 4 : ℝ) : ℂ))
          (Complex.I * ((β / 4 : ℝ) : ℂ)) O
        rw [show -Complex.I * ((β / 4 : ℝ) : ℂ) + Complex.I * ((β / 4 : ℝ) : ℂ) = 0 by ring,
          heisenbergEvol_zero, hmat0] at hinv
        simpa [heisenbergEvol] using hinv.symm
      rw [hO0] at hOnorm
      simp [gibbsWightmanNormSq, gibbsWightmanInner, wightmanInner] at hOnorm
    exact le_trans hrel (mul_le_mul_of_nonneg_left (Real.log_le_log hop_pos hop_le) (by norm_num))
  have hrho_tr : (rhoO_op hH β O).trace = 1 := by
    rw [rhoO_op_trace_eq_normSq, hOnorm]; simp
  set D_bd : ℝ := 2 * Real.log (C_O * (2 : ℝ) ^ (s₀ + 1)) + 1
  have hD_bd_pos : 0 < D_bd := by
    dsimp only [D_bd]
    have h1 : (1 : ℝ) ≤ C_O * (2 : ℝ) ^ (s₀ + 1) := by
      calc (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ C_O * (2 : ℝ) ^ (s₀ + 1) := mul_le_mul hCO_ge1 (one_le_pow₀ (by norm_num)) (by norm_num) (by positivity)
    linarith [Real.log_nonneg h1]
  have hshell_bound : ∀ k : ℕ,
      |((rhoO_op hH β Ot - G.ρβ) * bgShell (∑ Z ∈ E, h Z) β k).trace.re| ≤
        (4 * Real.sqrt 2 * D_bd * (12 * Real.exp 1 * (r : ℝ))) * Real.sqrt (N : ℝ) *
          (if 2 ≤ k then ((k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k) else 0) := by
    intro k
    by_cases hk : 2 ≤ k
    · rw [if_pos hk]
      rcases bgShell_local_decomp hr E hE_card h hh_supp hJ.le hH_site hβ0 hk with
        ⟨E_k, xOp_k, hEk_prop, hx_supp, hsum_k, hsite_k⟩
      set g_k : ℝ := (3 / 4 : ℝ) * (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (β * (r : ℝ) * Jsite) ^ k
      by_cases hβ_eq0 : β = 0
      · have hgk0 : g_k = 0 := by dsimp only [g_k]; rw [hβ_eq0]; simp [zero_pow (by omega : k ≠ 0)]
        have hbg0 : bgShell (∑ Z ∈ E, h Z) β k = 0 := by
          rw [← hsum_k]
          refine Finset.sum_eq_zero fun Z hZ ↦ ?_
          rcases (hEk_prop Z hZ).1 with ⟨y, hyZ⟩
          have hle : opNorm (xOp_k Z) ≤ g_k :=
            le_trans (Finset.single_le_sum (fun _ _ ↦ opNorm_nonneg _) (Finset.mem_filter.mpr ⟨hZ, hyZ⟩)) (hsite_k y)
          rw [hgk0] at hle
          have h0 : opNorm (xOp_k Z) = 0 := le_antisymm hle (opNorm_nonneg _)
          have hclm : opToCLM (xOp_k Z) = 0 := norm_eq_zero.mp h0
          ext i j
          have he := congrArg (fun f ↦ (f (EuclideanSpace.single j (1 : ℂ))).ofLp i) hclm
          simpa [opToCLM, Matrix.mulVec, dotProduct] using he
        rw [hbg0, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, abs_zero]
        positivity
      · have hβ_pos : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm hβ_eq0)
        have hgk_pos : 0 < g_k := by
          dsimp only [g_k]
          have hk1 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
          have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
          positivity
        have hdec := entropic_decoupling_single_shell hN hr (by omega : 1 ≤ 1 + k * (r - 1))
          E hE_ne hE_card h hh_supp hH hJ hH_site
          E_k (fun Z hZ ↦ (hEk_prop Z hZ).1) (fun Z hZ ↦ (hEk_prop Z hZ).2)
          xOp_k hx_supp (by rw [hsum_k]; exact bgShell_isHermitian _ _ _) hgk_pos hsite_k
          hβ0 hβ_cum (rhoO_op_isHermitian hH β O) (rhoO_op_eigenvalues_nonneg hH β O) hrho_tr t
        dsimp only at hdec
        rw [hsum_k, ← rhoO_op_heisenbergEvol_eq_conj hH β t O] at hdec
        set k_X := 1 + k * (r - 1)
        set kr := max r k_X
        have hkr_eq : kr = k_X := max_eq_right (by
          dsimp only [k_X]
          have h1 : 1 * (r - 1) ≤ k * (r - 1) := Nat.mul_le_mul_right (r - 1) (by omega)
          omega)
        have hkr_le : (kr : ℝ) ≤ (k : ℝ) * (r : ℝ) := by
          rw [hkr_eq]; dsimp only [k_X]
          have : 1 + k * (r - 1) ≤ k * r := by
            have h1 : k * (r - 1) + k = k * r := by
              rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega : 1 ≤ r)]
            omega
          exact_mod_cast this
        have hexp_le : Real.exp (1 + (kr : ℝ) / (r : ℝ)) ≤ Real.exp 1 * (Real.exp 1) ^ k := by
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hdiv : (kr : ℝ) / (r : ℝ) ≤ (k : ℝ) := (div_le_iff₀ hr_pos).mpr hkr_le
          linarith
        have hinvΛ : 1 / (1 / (16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * g_k)) ≤
            12 * Real.exp 1 * (r : ℝ) * ((k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k) := by
          rw [one_div_one_div]
          have hkm1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
          have hqpow : (Real.exp 1) ^ k * (β * (r : ℝ) * Jsite) ^ k ≤ (1 / 16 : ℝ) ^ k := by
            rw [← mul_pow]
            refine pow_le_pow_left₀ (by positivity) ?_ k
            linarith [hβ_q]
          calc 16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * g_k
              ≤ 16 * ((k : ℝ) * (r : ℝ)) * (Real.exp 1 * (Real.exp 1) ^ k) * g_k := by gcongr
            _ = 12 * Real.exp 1 * (r : ℝ) * ((k : ℝ) ^ 2 * ((k - 1 : ℕ) : ℝ)) *
                  ((Real.exp 1) ^ k * (β * (r : ℝ) * Jsite) ^ k) := by dsimp only [g_k]; ring
            _ ≤ 12 * Real.exp 1 * (r : ℝ) * ((k : ℝ) ^ 2 * (k : ℝ)) * (1 / 16 : ℝ) ^ k := by gcongr
            _ = 12 * Real.exp 1 * (r : ℝ) * ((k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k) := by ring
        refine le_trans hdec ?_
        have hD_step : gibbsRelEntropy (rhoO_op_isHermitian hH β O) hH β + 1 ≤ D_bd := by
          dsimp only [D_bd]; linarith
        have hdiv_rew : 4 * Real.sqrt 2 * (gibbsRelEntropy (rhoO_op_isHermitian hH β O) hH β + 1) /
            (1 / (16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * g_k)) * Real.sqrt (N : ℝ) =
            4 * Real.sqrt 2 * (gibbsRelEntropy (rhoO_op_isHermitian hH β O) hH β + 1) *
              (1 / (1 / (16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * g_k))) * Real.sqrt (N : ℝ) := by
          ring
        rw [hdiv_rew]
        calc 4 * Real.sqrt 2 * (gibbsRelEntropy (rhoO_op_isHermitian hH β O) hH β + 1) *
              (1 / (1 / (16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * g_k))) * Real.sqrt (N : ℝ)
            ≤ 4 * Real.sqrt 2 * D_bd *
                (12 * Real.exp 1 * (r : ℝ) * ((k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k)) * Real.sqrt (N : ℝ) := by
              have hnn1 : 0 ≤ gibbsRelEntropy (rhoO_op_isHermitian hH β O) hH β + 1 := by
                linarith [gibbsRelEntropy_nonneg_psd (rhoO_op_isHermitian hH β O) hH
                  (rhoO_op_eigenvalues_nonneg hH β O) hrho_tr β]
              gcongr
          _ = (4 * Real.sqrt 2 * D_bd * (12 * Real.exp 1 * (r : ℝ))) * Real.sqrt (N : ℝ) *
                ((k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k) := by ring
    · rw [if_neg hk, mul_zero]
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · simp [bgShell_zero]
      · simp [bgShell_one]
  have hgeom_le1 : Summable (fun k : ℕ ↦ if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k else 0) ∧
      (∑' k : ℕ, if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k else 0) ≤ 1 := by
    have hdom : ∀ k : ℕ, (if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k else 0) ≤ (1 / 2 : ℝ) ^ k / 2 := by
      intro k
      split_ifs with hk
      · have h2k3 : ∀ m : ℕ, 2 ≤ m → 2 * (m : ℝ) ^ 3 ≤ (8 : ℝ) ^ m := by
          intro m hm
          induction m with
          | zero => omega
          | succ m ih =>
            by_cases hm2 : 2 ≤ m
            · have hih := ih hm2
              have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
              have hstep : 2 * ((m + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * (2 * (m : ℝ) ^ 3) := by
                push_cast
                have hm1 : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
                have hcube : ((m : ℝ) + 1) ^ 3 ≤ (2 * (m : ℝ)) ^ 3 :=
                  pow_le_pow_left₀ (by linarith) hm1 3
                linarith [show (2 * (m : ℝ)) ^ 3 = 8 * (m : ℝ) ^ 3 by ring]
              calc 2 * ((m + 1 : ℕ) : ℝ) ^ 3 ≤ 8 * (2 * (m : ℝ) ^ 3) := hstep
                _ ≤ 8 * (8 : ℝ) ^ m := mul_le_mul_of_nonneg_left hih (by norm_num)
                _ = (8 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
            · have hm1 : m = 1 := by omega
              subst hm1; norm_num
        have hk3 : (k : ℝ) ^ 3 ≤ (8 : ℝ) ^ k / 2 := by linarith [h2k3 k hk]
        calc (k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k
            ≤ ((8 : ℝ) ^ k / 2) * (1 / 16 : ℝ) ^ k := mul_le_mul_of_nonneg_right hk3 (by positivity)
          _ = ((8 : ℝ) * (1 / 16 : ℝ)) ^ k / 2 := by rw [mul_pow]; ring
          _ = (1 / 2 : ℝ) ^ k / 2 := by norm_num
      · positivity
    have hsumm_g : Summable (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k / 2) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).div_const 2
    have hsumm : Summable (fun k : ℕ ↦ if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k else 0) :=
      Summable.of_nonneg_of_le (fun k ↦ by split_ifs <;> positivity) hdom hsumm_g
    refine ⟨hsumm, ?_⟩
    calc ∑' k : ℕ, (if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k else 0)
        ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k / 2 := hsumm.tsum_le_tsum hdom hsumm_g
      _ = (∑' k : ℕ, (1 / 2 : ℝ) ^ k) / 2 := tsum_div_const
      _ = 2 / 2 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
      _ = 1 := by norm_num
  have hIII_le : |shiftedThermalSizeIII hH β Ot| ≤ bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ) := by
    have hhas := hasSum_trace_bgShell hH β (rhoO_op hH β Ot - G.ρβ)
    have hIII_eq : shiftedThermalSizeIII hH β Ot =
        ∑' k : ℕ, ((rhoO_op hH β Ot - G.ρβ) * bgShell (∑ Z ∈ E, h Z) β k).trace.re :=
      hhas.tsum_eq.symm
    rw [hIII_eq]
    have hsumm_abs : Summable (fun k : ℕ ↦ |((rhoO_op hH β Ot - G.ρβ) * bgShell (∑ Z ∈ E, h Z) β k).trace.re|) :=
      Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) hshell_bound (hgeom_le1.1.mul_left _)
    have hsumm_norm : Summable (fun k : ℕ ↦ ‖((rhoO_op hH β Ot - G.ρβ) * bgShell (∑ Z ∈ E, h Z) β k).trace.re‖) := by
      simpa only [Real.norm_eq_abs] using hsumm_abs
    calc |∑' k : ℕ, ((rhoO_op hH β Ot - G.ρβ) * bgShell (∑ Z ∈ E, h Z) β k).trace.re|
        ≤ ∑' k : ℕ, |((rhoO_op hH β Ot - G.ρβ) * bgShell (∑ Z ∈ E, h Z) β k).trace.re| := by
          simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsumm_norm
      _ ≤ ∑' k : ℕ, (4 * Real.sqrt 2 * D_bd * (12 * Real.exp 1 * (r : ℝ))) * Real.sqrt (N : ℝ) *
            (if 2 ≤ k then ((k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k) else 0) :=
          hsumm_abs.tsum_le_tsum hshell_bound (hgeom_le1.1.mul_left _)
      _ = (4 * Real.sqrt 2 * D_bd * (12 * Real.exp 1 * (r : ℝ))) * Real.sqrt (N : ℝ) *
            ∑' k : ℕ, (if 2 ≤ k then ((k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k) else 0) := tsum_mul_left
      _ ≤ (4 * Real.sqrt 2 * D_bd * (12 * Real.exp 1 * (r : ℝ))) * Real.sqrt (N : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hgeom_le1.2 (by positivity)
      _ = bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ) := by dsimp only [bgDecouplingC2, D_bd]; ring
  have hbg_le : ((G.ρβ * thermalBackgroundOp hH β).trace).re ≤ (N : ℝ) := by
    have hhas := hasSum_trace_bgShell hH β G.ρβ
    rw [← hhas.tsum_eq]
    have hterm_bg : ∀ k : ℕ, (G.ρβ * bgShell (∑ Z ∈ E, h Z) β k).trace.re ≤
        (N : ℝ) * (if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k else 0) := by
      intro k
      by_cases hk : 2 ≤ k
      · rw [if_pos hk]
        rcases bgShell_local_decomp hr E hE_card h hh_supp hJ.le hH_site hβ0 hk with
          ⟨E_k, xOp_k, hEk_prop, _, hsum_k, hsite_k⟩
        have h1 : (G.ρβ * bgShell (∑ Z ∈ E, h Z) β k).trace.re ≤ opNorm (bgShell (∑ Z ∈ E, h Z) β k) :=
          le_trans (le_abs_self _) (le_trans (Complex.abs_re_le_norm _) (norm_trace_gibbsRho_mul_le_opNorm hH β _))
        have h2 : opNorm (bgShell (∑ Z ∈ E, h Z) β k) ≤
            (N : ℝ) * ((3 / 4 : ℝ) * (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (β * (r : ℝ) * Jsite) ^ k) := by
          rw [← hsum_k]
          calc opNorm (∑ Z ∈ E_k, xOp_k Z) ≤ ∑ Z ∈ E_k, opNorm (xOp_k Z) := opNorm_sum_le _ _
            _ ≤ ∑ y : Fin N, ∑ Z ∈ E_k.filter (fun Z ↦ y ∈ Z), opNorm (xOp_k Z) := by
                have hsub : E_k ⊆ Finset.univ.biUnion (fun y : Fin N ↦ E_k.filter (fun Z ↦ y ∈ Z)) := by
                  intro Z hZ; rcases (hEk_prop Z hZ).1 with ⟨y, hyZ⟩
                  exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ y, Finset.mem_filter.mpr ⟨hZ, hyZ⟩⟩
                exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ opNorm_nonneg _)
                  (real_sum_biUnion_le _ _ _ fun _ _ ↦ opNorm_nonneg _)
            _ ≤ ∑ _y : Fin N, ((3 / 4 : ℝ) * (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (β * (r : ℝ) * Jsite) ^ k) :=
                Finset.sum_le_sum fun y _ ↦ hsite_k y
            _ = (N : ℝ) * ((3 / 4 : ℝ) * (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (β * (r : ℝ) * Jsite) ^ k) := by simp
        refine le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)))
        have hkm1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
        have h1k : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
        have hq1 : β * (r : ℝ) * Jsite ≤ 1 / 16 := by
          have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
          have hnn : 0 ≤ β * (r : ℝ) * Jsite := by positivity
          calc β * (r : ℝ) * Jsite = (β * (r : ℝ) * Jsite) * 1 := by ring
            _ ≤ (β * (r : ℝ) * Jsite) * Real.exp 1 := mul_le_mul_of_nonneg_left he1 hnn
            _ = β * Real.exp 1 * (r : ℝ) * Jsite := by ring
            _ ≤ 1 / 16 := hβ_q
        calc (3 / 4 : ℝ) * (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (β * (r : ℝ) * Jsite) ^ k
            ≤ 1 * (k : ℝ) * (k : ℝ) * (1 / 16 : ℝ) ^ k := by
              have hp : (β * (r : ℝ) * Jsite) ^ k ≤ (1 / 16 : ℝ) ^ k :=
                pow_le_pow_left₀ (by positivity) hq1 k
              gcongr; norm_num
          _ ≤ (k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k := by
              have hk23 : 1 * (k : ℝ) * (k : ℝ) ≤ (k : ℝ) ^ 3 := by
                calc 1 * (k : ℝ) * (k : ℝ) = (k : ℝ) ^ 2 * 1 := by ring
                  _ ≤ (k : ℝ) ^ 2 * (k : ℝ) := mul_le_mul_of_nonneg_left h1k (sq_nonneg _)
                  _ = (k : ℝ) ^ 3 := by ring
              exact mul_le_mul_of_nonneg_right hk23 (by positivity)
      · rw [if_neg hk, mul_zero]
        have hk01 : k = 0 ∨ k = 1 := by omega
        rcases hk01 with rfl | rfl <;> simp [bgShell_zero, bgShell_one]
    have hsumm_bg : Summable (fun k : ℕ ↦ (G.ρβ * bgShell (∑ Z ∈ E, h Z) β k).trace.re) := hhas.summable
    calc ∑' k : ℕ, (G.ρβ * bgShell (∑ Z ∈ E, h Z) β k).trace.re
        ≤ ∑' k : ℕ, (N : ℝ) * (if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k else 0) :=
          hsumm_bg.tsum_le_tsum hterm_bg (hgeom_le1.1.mul_left _)
      _ = (N : ℝ) * ∑' k : ℕ, (if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 16 : ℝ) ^ k else 0) := tsum_mul_left
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hgeom_le1.2 (Nat.cast_nonneg N)
      _ = (N : ℝ) := mul_one _
  rcases prop_6_4_part1_shifted_eq_6_4 hH β Ot with ⟨hdecomp, hII⟩
  have hIII_up : shiftedThermalSizeIII hH β Ot ≤ bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ) :=
    (abs_le.mp hIII_le).2
  have hII_up : shiftedThermalSizeII hH β Ot ≤
      2 * Real.sqrt (otocI hH β Ot) * Real.sqrt ((N : ℝ) + bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ)) := by
    calc shiftedThermalSizeII hH β Ot
        ≤ |shiftedThermalSizeII hH β Ot| := le_abs_self _
      _ ≤ 2 * Real.sqrt (otocI hH β Ot) *
            Real.sqrt (((G.ρβ * thermalBackgroundOp hH β).trace).re + shiftedThermalSizeIII hH β Ot) := hII
      _ ≤ 2 * Real.sqrt (otocI hH β Ot) *
            Real.sqrt ((N : ℝ) + bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ)) := by
          apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (add_le_add hbg_le hIII_up)) (by positivity)
  refine ⟨hIII_le, hbg_le, ?_⟩
  linarith [hdecomp, hII_up, hIII_up]

end ExtendedProp64Part2

section StandaloneLemma21AndTheorem13a

/-- **Lemma 2.1 (Concrete Qubit Imaginary-Time Exponential Norm Bound, Eq. 2.5)**:
Standalone wrapper for `r`-local qubit Hamiltonians (`r ≥ 2`, site norm `≤ Jsite`),
`W ∈ supportedOn U₀` (`|U₀| ≤ sW`), and `0 ≤ κ' < κ = (2 * (r - 1) * Jsite)⁻¹`. -/
theorem lemma_2_1_qubit_exp_bound {N r sW : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {Jsite : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    {U₀ : Finset (Fin N)} (hU₀ : U₀.card ≤ sW) {W : QubitOp N} (hW : W ∈ supportedOn U₀)
    {κ' : ℝ} (hκ'0 : 0 ≤ κ')
    (hκ'_lt : κ' < 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)) :
    let κ : ℝ := 1 / (2 * ((r - 1 : ℕ) : ℝ) * Jsite)
    opNorm (heisenbergEvol hH (-(Complex.I * (κ' : ℂ))) W) ≤
      opNorm W * (1 - κ' / κ) ^ (-((sW : ℝ) / ((r - 1 : ℕ) : ℝ))) :=
  theorem_1_2a_concrete_eq54_r_local_norm_bound hr E hcard h hsupp hH hJ hsite hU₀ hW hκ'0 hκ'_lt

/-- **Theorem 1.3(a) (Complete Two-Sided High-Temperature Operator Inequality, Eq. 1.20)**:
Combines the universal single-site bound `Re (A | 𝒬̃^{(β)} A)_β^W ≤ ∑ x, ‖𝒮_x(A)‖_{β,W}²` with
the high-temperature reverse-Poincaré inequality `Re (A | 𝒬̃^{(β)} A)_β^W ≤ 9 * Re (A | 𝒬^{(β)} A)_β^W`
for all `0 ≤ β ≤ highTempBetaWC r Jsite` and every `A : QubitOp N`. -/
theorem theorem_1_3a_high_temp_two_sided {N r : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hne : ∀ X ∈ E, X.Nonempty)
    (hcard : ∀ X ∈ E, X.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hsupp : ∀ X, h X ∈ supportedOn X)
    (hH : (∑ X ∈ E, h X).IsHermitian)
    {Jsite β : ℝ} (hJ : 0 < Jsite)
    (hsite : ∀ x : Fin N, ∑ X ∈ E.filter (fun X ↦ x ∈ X), opNorm (h X) ≤ Jsite)
    (hβ0 : 0 ≤ β) (hβ : β ≤ highTempBetaWC r Jsite)
    (A : QubitOp N) :
    let G := concreteGibbsData hH β
    (gibbsWightmanInner G A (quantumGlauberGen G A)).re ≤
      ∑ x : Fin N, gibbsWightmanNormSq G (siteSizeOp x A) ∧
    (gibbsWightmanInner G A (quantumGlauberGen G A)).re ≤
      9 * (gibbsWightmanInner G A (wightmanQ G A)).re :=
  ⟨theorem_1_3a_lower_concrete (concreteGibbsData hH β) A,
   theorem_1_3a_high_temp hr E hne hcard h hsupp hH hJ hsite hβ0 hβ A⟩

end StandaloneLemma21AndTheorem13a

end KrylovChaos
