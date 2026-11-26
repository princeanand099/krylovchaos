/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.WightmanIsometry
import KrylovChaos.KrylovTail
import KrylovChaos.CarlemanJacobi
import KrylovChaos.Filtration
import KrylovChaos.ProductState
import KrylovChaos.SpectralDyck
import KrylovChaos.VitaliAnalytic
import KrylovChaos.GlauberDecoupling
import KrylovChaos.DepolarizedFrame
import KrylovChaos.KoteckyPreiss
import KrylovChaos.PolymerTrees
import KrylovChaos.ClassicalIsing
import KrylovChaos.ArakiOneDim
import KrylovChaos.StructuralNecessity
import Mathlib.Tactic

/-!
# Concrete Operator Bridges, De-Orphaning & Corollary 6.5

Connects all previously standalone modules (`CarlemanJacobi`, `KoteckyPreiss`, `PolymerTrees`,
`VitaliAnalytic`, `ArakiOneDim`, `QubitAlgebra`, `ManyBodySetup`) into the unified theorem DAG
and provides:
1. `theorem_1_1a_limsup_rate_bound`: actual `Filter.limsup_{t → ∞} (1/t) ln K(t) ≤ 2α`.
2. `theorem_1_1a_carleman_esa`: bridges linear Lanczos growth `b_n ≤ α n + γ` to Carleman's
   divergence criterion and zero deficiency indices in `CarlemanJacobi`.
3. `prop_4_1_concrete_qubit_filtration`: concrete `N`-qubit proof that `ad_H^k(A) ∈ V_{s₀ + (r-1)k}`
   for any `r`-local Hamiltonian `H : LocalHamiltonian N r`.
4. `corollary_6_5_krylov_lieb_robinson`: **Corollary 6.5 (Krylov–Lieb–Robinson Bound, Eq. 6.11)**.
5. `globalDepolP`, `globalDepolP_herm`, `globalDepolP_trace`, `globalDepolP_avg` (global `N`-qubit
   depolarized 2-design frame) and `lemma_7_1_dual_trace_bound` (Lemma 7.1(3b)).
6. `lemma_8_2_multi_edge_hs`: multi-edge Hubbard–Stratonovich factorization on arbitrary edge sets.
-/

namespace KrylovChaos

open Matrix

section Section3Bridges

/-- **Theorem 1.1(a) (Limsup Growth Rate Bound, Eq. 1.13)**:
Actual `Filter.limsup` statement `limsup_{t → ∞} (1 / t) ln K(t) ≤ 2 α` for any positive `K(t)`
whose log-rate is eventually bounded below and which satisfies `K(t) ≤ C e^{2αt}`. -/
theorem theorem_1_1a_limsup_rate_bound {C α : ℝ} {K : ℝ → ℝ}
    (hC : 0 < C) (hKp : ∀ t > 0, 0 < K t)
    (hKlb : ∃ M : ℝ, ∀ᶠ t : ℝ in Filter.atTop, M ≤ Real.log (K t) / t)
    (hK : ∀ t > 0, K t ≤ C * Real.exp (2 * α * t)) :
    Filter.limsup (fun t : ℝ ↦ Real.log (K t) / t) Filter.atTop ≤ 2 * α := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hcob : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop (fun t : ℝ ↦ Real.log (K t) / t) := by
    rcases hKlb with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro a ha
    have hboth := hM.and ha
    rcases hboth.exists with ⟨t, ht1, ht2⟩
    exact le_trans ht1 ht2
  apply Filter.limsup_le_of_le hcob
  rw [Filter.eventually_atTop]
  refine ⟨max 1 (|Real.log C| / ε + 1), fun t ht ↦ ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have htpos : 0 < t := by linarith
  have ht2 : |Real.log C| / ε < t := by
    have := le_trans (le_max_right _ _) ht
    linarith
  have hlog_div : Real.log C / t ≤ ε := by
    have h1 : Real.log C ≤ |Real.log C| := le_abs_self _
    have h2 : |Real.log C| < t * ε := (div_lt_iff₀ hε).mp ht2
    rw [div_le_iff₀ htpos]
    linarith
  have hpt : Real.log (K t) / t ≤ 2 * α + Real.log C / t := by
    have h1 : Real.log (K t) ≤ Real.log (C * Real.exp (2 * α * t)) :=
      Real.log_le_log (hKp t htpos) (hK t htpos)
    rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
    have hdiv := div_le_div_of_nonneg_right h1 htpos.le
    have hrew : (Real.log C + 2 * α * t) / t = 2 * α + Real.log C / t := by
      field_simp [htpos.ne']; ring
    linarith
  linarith

/-- **Theorem 1.1(a) (Carleman Essential Self-Adjointness Bridge)**:
Connects linear Lanczos growth `0 < b_n ≤ α n + γ` directly to Carleman's divergence
criterion and zero deficiency indices in `KrylovChaos.CarlemanJacobi`. -/
theorem theorem_1_1a_carleman_esa {α γ : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ)
    (b : ℕ → ℝ) (hb_pos : ∀ n : ℕ, 0 < b n) (hb_lin : ∀ n : ℕ, b n ≤ α * (n : ℝ) + γ) :
    (¬ Summable (fun n : ℕ ↦ (b n)⁻¹)) ∧
    (∀ (u : ℕ → ℂ) (z : ℂ), z.im ≠ 0 →
      (∀ n : ℕ, (b n : ℂ) * u (n + 1) +
        (if h : n = 0 then (0 : ℂ) else (b (n - 1) : ℂ) * u (n - 1)) = z * u n) →
      Summable (fun n : ℕ ↦ ‖u n‖ ^ 2) → ∀ n : ℕ, u n = 0) := by
  have hdiv : ¬ Summable (fun n : ℕ ↦ (b n)⁻¹) :=
    carleman_divergence_of_linear_growth b hα hγ hb_pos hb_lin
  exact ⟨hdiv, fun u z hz hrec hℓ2 ↦ carleman_deficiency_zero b hb_pos hdiv u z hz hrec hℓ2⟩

end Section3Bridges

section Section4Bridges

/-- Iterated Liouvillian action `ad_H^k(A)` on the concrete `N`-qubit operator algebra `QubitOp N`. -/
def iterMatCommQubit {N : ℕ} (H : QubitOp N) : ℕ → QubitOp N → QubitOp N
  | 0, A => A
  | k + 1, A => matComm H (iterMatCommQubit H k A)

/-- **Proposition 4.1 (Concrete N-Qubit Filtration Inclusion)**:
For any concrete `r`-local `N`-qubit Hamiltonian `ham : LocalHamiltonian N r` (`r ≥ 1`)
and any `s₀`-local operator `A ∈ filtrationSubmodule N s₀`, the `k`-th nested commutator
`ad_H^k(A)` lies in `filtrationSubmodule N (s₀ + (r - 1) * k)`. -/
theorem prop_4_1_concrete_qubit_filtration {N r s₀ : ℕ} (hr : 1 ≤ r)
    (ham : LocalHamiltonian N r) (A : QubitOp N)
    (hA : A ∈ filtrationSubmodule N s₀) :
    ∀ k : ℕ, iterMatCommQubit ham.totalOp k A ∈
      filtrationSubmodule N (s₀ + (r - 1) * k) := by
  have hH : ham.totalOp ∈ filtrationSubmodule N r := ham.totalOp_in_filtration
  intro k
  induction k with
  | zero =>
    simpa [iterMatCommQubit] using hA
  | succ k ih =>
    simp only [iterMatCommQubit]
    have hstep := filtration_comm_step hr hH ih
    have hle : min N (s₀ + (r - 1) * k + r - 1) ≤ s₀ + (r - 1) * (k + 1) := by
      have h1 : min N (s₀ + (r - 1) * k + r - 1) ≤ s₀ + (r - 1) * k + r - 1 := min_le_right _ _
      rw [mul_add, mul_one]
      omega
    exact filtrationSubmodule_mono N hle hstep

end Section4Bridges

section Section6Bridges

/-- Geometric tail bound used in Corollary 6.5: truncating the causal-sequence expansion
at order `m₀` leaves remainder `∑_{m > m₀} q^m = q^{m₀ + 1} / (1 - q)` for `0 ≤ q < 1`. -/
theorem corollary_6_5_causal_tail_geom {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (m₀ : ℕ) :
    (∑' k : ℕ, q ^ (m₀ + 1 + k)) = q ^ (m₀ + 1) / (1 - q) := by
  have hrew : (fun k : ℕ ↦ q ^ (m₀ + 1 + k)) = (fun k : ℕ ↦ q ^ (m₀ + 1) * q ^ k) := by
    funext k; rw [pow_add]
  rw [hrew, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

/-- **Corollary 6.5 (Krylov–Lieb–Robinson Bound, Eq. 6.11)**:
Combining Proposition 6.4(2) (entropic background decoupling) with a `d`-dimensional
Lieb–Robinson light-cone bound `I(O(t)) ≤ C_LR (v_LR t + 1)^d` yields
`S_β(O(t)) ≤ C_LR (v_LR t + 1)^d + 2 √(c_B C_LR) √(N (v_LR t + 1)^d) + C_2 √N`. -/
theorem corollary_6_5_krylov_lieb_robinson
    {Sβ I Bavg II III N cB C₂ C_LR v_LR t : ℝ} {d : ℕ}
    (hN : 0 ≤ N) (hI : 0 ≤ I) (hcB : 0 ≤ cB) (hCLR : 0 ≤ C_LR)
    (hv : 0 ≤ v_LR) (ht : 0 ≤ t)
    (hdecomp : Sβ = I + II + III)
    (hIII : |III| ≤ C₂ * Real.sqrt N)
    (hII : |II| ≤ 2 * Real.sqrt I * Real.sqrt (Bavg + III))
    (hB : Bavg + |III| ≤ cB * N)
    (hLR : I ≤ C_LR * (v_LR * t + 1) ^ d) :
    Sβ ≤ C_LR * (v_LR * t + 1) ^ d +
      (2 * Real.sqrt (cB * C_LR)) * Real.sqrt (N * (v_LR * t + 1) ^ d) +
      C₂ * Real.sqrt N := by
  have hdec := prop_6_4_decoupling_combine hN hI hcB hdecomp hIII hII hB
  have hvt_nn : 0 ≤ (v_LR * t + 1) ^ d := pow_nonneg (by nlinarith) d
  have hsqrt_I : Real.sqrt (N * I) ≤ Real.sqrt C_LR * Real.sqrt (N * (v_LR * t + 1) ^ d) := by
    have hNI : N * I ≤ C_LR * (N * (v_LR * t + 1) ^ d) := by
      have := mul_le_mul_of_nonneg_left hLR hN
      linarith
    calc Real.sqrt (N * I)
        ≤ Real.sqrt (C_LR * (N * (v_LR * t + 1) ^ d)) := Real.sqrt_le_sqrt hNI
      _ = Real.sqrt C_LR * Real.sqrt (N * (v_LR * t + 1) ^ d) := Real.sqrt_mul hCLR _
  have hmid : (2 * Real.sqrt cB) * Real.sqrt (N * I) ≤
      (2 * Real.sqrt (cB * C_LR)) * Real.sqrt (N * (v_LR * t + 1) ^ d) := by
    rw [Real.sqrt_mul hcB C_LR]
    calc (2 * Real.sqrt cB) * Real.sqrt (N * I)
        ≤ (2 * Real.sqrt cB) * (Real.sqrt C_LR * Real.sqrt (N * (v_LR * t + 1) ^ d)) :=
          mul_le_mul_of_nonneg_left hsqrt_I (by positivity)
      _ = (2 * (Real.sqrt cB * Real.sqrt C_LR)) * Real.sqrt (N * (v_LR * t + 1) ^ d) := by ring
  linarith

end Section6Bridges

section Section7Bridges

/-- Global `N`-qubit depolarized product frame operator `P̃_s = ⨂_{x=1}^N P̃_{s_x}` on `QubitOp N`. -/
noncomputable def globalDepolP (N : ℕ) (s : Fin N → Fin 6) : QubitOp N :=
  kronOp (fun x ↦ depolP (s x))

/-- Global `N`-qubit dual frame operator `F̃_s = ⨂_{x=1}^N F̃_{s_x}` on `QubitOp N`. -/
noncomputable def globalDepolF (N : ℕ) (s : Fin N → Fin 6) : QubitOp N :=
  kronOp (fun x ↦ depolF (s x))

/-- Every global product frame operator `P̃_s` is Hermitian. -/
theorem globalDepolP_herm (N : ℕ) (s : Fin N → Fin 6) :
    (globalDepolP N s)ᴴ = globalDepolP N s := by
  unfold globalDepolP
  rw [kronOp_conjTranspose]
  congr 1; funext x
  exact lemma_7_1_herm_trace_avg.1 (s x)

/-- Every global product frame operator `P̃_s` has unit trace `Tr(P̃_s) = 1`. -/
theorem globalDepolP_trace (N : ℕ) (s : Fin N → Fin 6) :
    (globalDepolP N s).trace = 1 := by
  unfold globalDepolP
  rw [kronOp_trace]
  simp_rw [lemma_7_1_herm_trace_avg.2.1]
  simp

/-- Global `N`-qubit uniform frame average:
`(1 / 6^N) ∑_{s ∈ {0..5}^N} P̃_s = (1 / 2^N) I_{2^N}`. -/
theorem globalDepolP_avg (N : ℕ) :
    ((1 / 6 : ℂ) ^ N) • (∑ s : Fin N → Fin 6, globalDepolP N s) =
      ((1 / 2 : ℂ) ^ N) • (1 : QubitOp N) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.sum_apply, globalDepolP, kronOp, Matrix.of_apply,
    smul_eq_mul]
  rw [← Fintype.prod_sum (fun (x : Fin N) (sx : Fin 6) ↦ depolP sx (i x) (j x))]
  have hsingle : ∀ x : Fin N,
      (∑ sx : Fin 6, depolP sx (i x) (j x)) =
        (3 : ℂ) * (1 : Matrix (Fin 2) (Fin 2) ℂ) (i x) (j x) := by
    intro x
    have havg := congrFun (congrFun lemma_7_1_herm_trace_avg.2.2 (i x)) (j x)
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] at havg
    linear_combination 6 * havg
  simp_rw [hsingle, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : (∏ x : Fin N, (1 : Matrix (Fin 2) (Fin 2) ℂ) (i x) (j x)) = (1 : QubitOp N) i j := by
    have := congrFun (congrFun (kronOp_one (N := N)) i) j
    simpa [kronOp] using this
  rw [h1]
  have hpow : ((1 / 6 : ℂ) ^ N) * (3 : ℂ) ^ N = (1 / 2 : ℂ) ^ N := by
    rw [← mul_pow]; congr 1; norm_num
  rw [← mul_assoc, hpow]

/-- **Lemma 7.1(3b)** (Dual Frame Trace Bound):
For every `B : Matrix (Fin 2) (Fin 2) ℂ` and every `s : Fin 6`,
`‖(1 / 2) Tr(B F̃_s)‖ ≤ (7 / 2) (‖B 0 0‖ + ‖B 0 1‖ + ‖B 1 0‖ + ‖B 1 1‖)`. -/
theorem lemma_7_1_dual_trace_bound (s : Fin 6) (B : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖(1 / 2 : ℂ) * Matrix.trace (B * depolF s)‖ ≤
      (7 / 2 : ℝ) * (‖B 0 0‖ + ‖B 0 1‖ + ‖B 1 0‖ + ‖B 1 1‖) := by
  have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [norm_mul, hhalf]
  suffices h : ‖Matrix.trace (B * depolF s)‖ ≤
      7 * (‖B 0 0‖ + ‖B 0 1‖ + ‖B 1 0‖ + ‖B 1 1‖) by linarith
  have htr : Matrix.trace (B * depolF s) =
      B 0 0 * depolF s 0 0 + B 0 1 * depolF s 1 0 +
      B 1 0 * depolF s 0 1 + B 1 1 * depolF s 1 1 := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]; ring
  rw [htr]
  have hbound_entry : ∀ a b : Fin 2, ‖depolF s a b‖ ≤ 7 := by
    intro a b
    fin_cases s <;> fin_cases a <;> fin_cases b <;>
      simp [depolF, signedPauli, pauliX, pauliY, pauliZ] <;> norm_num
  have h1 : ‖B 0 0 * depolF s 0 0‖ ≤ 7 * ‖B 0 0‖ := by
    rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hbound_entry 0 0) (norm_nonneg _)
  have h2 : ‖B 0 1 * depolF s 1 0‖ ≤ 7 * ‖B 0 1‖ := by
    rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hbound_entry 1 0) (norm_nonneg _)
  have h3 : ‖B 1 0 * depolF s 0 1‖ ≤ 7 * ‖B 1 0‖ := by
    rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hbound_entry 0 1) (norm_nonneg _)
  have h4 : ‖B 1 1 * depolF s 1 1‖ ≤ 7 * ‖B 1 1‖ := by
    rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hbound_entry 1 1) (norm_nonneg _)
  have htri := norm_add_le (B 0 0 * depolF s 0 0 + B 0 1 * depolF s 1 0 + B 1 0 * depolF s 0 1)
    (B 1 1 * depolF s 1 1)
  have htri2 := norm_add_le (B 0 0 * depolF s 0 0 + B 0 1 * depolF s 1 0)
    (B 1 0 * depolF s 0 1)
  have htri3 := norm_add_le (B 0 0 * depolF s 0 0) (B 0 1 * depolF s 1 0)
  linarith

end Section7Bridges

section Section8Bridges

/-- Classical Ising spin value `±1` encoded by `Bool`. -/
def spinVal (b : Bool) : ℝ := if b then 1 else -1

lemma spinVal_mem (b : Bool) : spinVal b = 1 ∨ spinVal b = -1 := by
  cases b <;> simp [spinVal]

/-- **Lemma 8.2 (Multi-Edge Hubbard–Stratonovich Factorization)**:
For any finite edge set `E : Finset ι` with nonnegative couplings `u : ι → ℝ` and spin
endpoints `s_e, z₁_e, z₂_e ∈ {±1}`, the product of `2`-local Ising Boltzmann weights
`∏_{e ∈ E} exp(u_e s_e z₁_e z₂_e)` factorizes into an exact positive product of auxiliary
Hubbard–Stratonovich sums. -/
theorem lemma_8_2_multi_edge_hs {ι : Type*} [DecidableEq ι]
    (E : Finset ι) (u : ι → ℝ) (hu : ∀ e ∈ E, 0 ≤ u e)
    (s z₁ z₂ : ι → Bool) :
    (∏ e ∈ E, Real.exp (u e * spinVal (s e) * spinVal (z₁ e) * spinVal (z₂ e))) =
      ∏ e ∈ E, (Real.exp (-(u e)) * (1 / 2 : ℝ) *
        ∑ τ : Bool, Real.exp (hsPhi (u e) * spinVal τ *
          (spinVal (z₁ e) + spinVal (s e) * spinVal (z₂ e)))) := by
  apply Finset.prod_congr rfl
  intro e he
  have h1 := lemma_8_2_hubbard_stratonovich_identity (hu e he)
    (spinVal_mem (s e)) (spinVal_mem (z₁ e)) (spinVal_mem (z₂ e))
  have hsum : (∑ τ : Bool, Real.exp (hsPhi (u e) * spinVal τ *
      (spinVal (z₁ e) + spinVal (s e) * spinVal (z₂ e)))) =
      Real.exp (hsPhi (u e) * (spinVal (z₁ e) + spinVal (s e) * spinVal (z₂ e))) +
      Real.exp (-(hsPhi (u e)) * (spinVal (z₁ e) + spinVal (s e) * spinVal (z₂ e))) := by
    simp [Fintype.sum_bool, spinVal]
  rw [hsum]
  exact h1

end Section8Bridges

end KrylovChaos
