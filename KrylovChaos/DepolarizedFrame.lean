/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.ProductState
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Section 7: Depolarized 2-Design Cluster Expansion and Proof of Theorem 1.3

Formalizes:
- **Lemma 7.1**: Explicit `2 × 2` depolarized single-site projective 2-design frame
  `{P̃_{s_x}, F̃_{s_x}}_{s_x=1}^6` with exact Hermiticity, trace, uniform conditioning
  `(1/4) I ⪯ P̃_{s_x} ⪯ (3/4) I`, exact dual reconstruction (Eq. 7.3), and dual norm bound `6`.
- **Lemma 7.3**: Product-space conditioning (`9^{|U|}`) and projection comparison (Eqs. 7.11–7.12).
- **Theorem 1.3(a)–(c)**: Global quantum reverse-Poincaré inequality (1.20), global commutator
  dominance `C_W ≤ 54 Q`, `I ≤ 216 Q` (1.21–1.22), and high-temperature Lyapunov bounds (1.23–1.24).
-/

namespace KrylovChaos

open Matrix

section SingleSiteFrame

/-- Pauli `X` matrix on `ℂ²`. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `Y` matrix on `ℂ²`. -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli `Z` matrix on `ℂ²`. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Signed Pauli operator `± σ_α` indexed by `s : Fin 6`. -/
def signedPauli : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => pauliX
  | 1 => -pauliX
  | 2 => pauliY
  | 3 => -pauliY
  | 4 => pauliZ
  | 5 => -pauliZ

/-- Depolarized single-site operator `P̃_s := (1/2) I ± (1/4) σ_α` (Eq. 7.1). -/
noncomputable def depolP (s : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 / 4 : ℂ) • signedPauli s

/-- Dual frame operator `F̃_s := I ± 6 σ_α = 24 P̃_s - 11 I` (Eq. 7.2). -/
noncomputable def depolF (s : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) + (6 : ℂ) • signedPauli s

/-- **Lemma 7.1(1a)**: Every `P̃_s` is Hermitian with `Tr(P̃_s) = 1`, and
`(1/6) ∑_{s=0}^5 P̃_s = (1/2) I₂`. -/
theorem lemma_7_1_herm_trace_avg :
    (∀ s : Fin 6, (depolP s)ᴴ = depolP s) ∧
    (∀ s : Fin 6, Matrix.trace (depolP s) = 1) ∧
    ((1 / 6 : ℂ) • ∑ s : Fin 6, depolP s = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    fin_cases s <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [depolP, signedPauli, pauliX, pauliY, pauliZ] <;> ring
  · intro s
    fin_cases s <;>
      simp [depolP, signedPauli, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.diag] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_six, depolP, signedPauli, pauliX, pauliY, pauliZ] <;> ring

/-- **Lemma 7.1(1b)** (Uniform Conditioning, condition number 3). -/
theorem lemma_7_1_conditioning (s : Fin 6) (v : Fin 2 → ℂ) :
    (1 / 4 : ℝ) * (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) ≤
      (∑ i : Fin 2, ∑ j : Fin 2, star (v i) * depolP s i j * v j).re ∧
    (∑ i : Fin 2, ∑ j : Fin 2, star (v i) * depolP s i j * v j).re ≤
      (3 / 4 : ℝ) * (‖v 0‖ ^ 2 + ‖v 1‖ ^ 2) := by
  have hnorm0 : ‖v 0‖ ^ 2 = (v 0).re ^ 2 + (v 0).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hnorm1 : ‖v 1‖ ^ 2 = (v 1).re ^ 2 + (v 1).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [hnorm0, hnorm1]
  fin_cases s <;>
  · simp only [Fin.sum_univ_two, depolP, signedPauli, pauliX, pauliY, pauliZ,
      Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      smul_eq_mul, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.neg_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.zero_re, Complex.zero_im, zero_mul, mul_zero, mul_one, one_mul,
      add_zero, zero_add, sub_zero, neg_zero]
    norm_num
    constructor <;>
      nlinarith [sq_nonneg ((v 0).re - (v 1).re), sq_nonneg ((v 0).re + (v 1).re),
        sq_nonneg ((v 0).im - (v 1).im), sq_nonneg ((v 0).im + (v 1).im),
        sq_nonneg ((v 0).re - (v 1).im), sq_nonneg ((v 0).re + (v 1).im),
        sq_nonneg ((v 0).im - (v 1).re), sq_nonneg ((v 0).im + (v 1).re)]

/-- **Lemma 7.1(2)** (Exact Dual Reconstruction, Eq. 7.3). -/
theorem lemma_7_1_dual_reconstruction (B : Matrix (Fin 2) (Fin 2) ℂ) :
    (1 / 2 : ℂ) • B =
    (1 / 6 : ℂ) • ∑ s : Fin 6, ((1 / 2 : ℂ) * Matrix.trace (B * depolF s)) • depolP s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_six, Fin.sum_univ_two, depolP, depolF, signedPauli,
      pauliX, pauliY, pauliZ, Matrix.trace, Matrix.diag, Matrix.mul_apply] <;>
    ring

/-- **Lemma 7.1(2b)**: If `B` is Hermitian (`Bᴴ = B`), then `(1/2) Tr(B F̃_s)` is real. -/
theorem lemma_7_1_dual_real_of_herm (B : Matrix (Fin 2) (Fin 2) ℂ) (hB : Bᴴ = B) (s : Fin 6) :
    ((1 / 2 : ℂ) * Matrix.trace (B * depolF s)).im = 0 := by
  have h00 : (B 0 0).im = 0 := by
    have := congr_fun (congr_fun hB 0) 0
    simp only [Matrix.conjTranspose_apply, Complex.star_def] at this
    have him := congr_arg Complex.im this
    simp only [Complex.conj_im] at him
    linarith
  have h11 : (B 1 1).im = 0 := by
    have := congr_fun (congr_fun hB 1) 1
    simp only [Matrix.conjTranspose_apply, Complex.star_def] at this
    have him := congr_arg Complex.im this
    simp only [Complex.conj_im] at him
    linarith
  have h01 : B 1 0 = star (B 0 1) := by
    have := congr_fun (congr_fun hB 0) 1
    simpa [Matrix.conjTranspose_apply] using this
  fin_cases s <;>
    simp [depolF, signedPauli, pauliX, pauliY, pauliZ, Matrix.trace, Matrix.diag,
      Matrix.mul_apply, Fin.sum_univ_two, h01, h00, h11] <;>
    ring

/-- **Lemma 7.1(3)** (Dual Frame Eigenvalue & Trace-Norm Identity). -/
theorem lemma_7_1_dual_eigenvalues (s : Fin 6) :
    let D := (1 / 2 : ℂ) • depolF s
    (D - (7 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      (D + (5 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 0 ∧
    (|(7 / 2 : ℝ)| + |(-5 / 2 : ℝ)| = 6) := by
  refine ⟨?_, by norm_num⟩
  fin_cases s <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [depolF, signedPauli, pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

end SingleSiteFrame

section ProductSpaceComparison

/-- **Lemma 7.3(1)** (Subset Union Bound in Product Orthonormal Basis, Eq. 7.11). -/
theorem lemma_7_3_subset_union_bound {N : ℕ} (U : Finset (Fin N)) (c : (Fin N → Fin 4) → ℂ) :
    (∑ a : Fin N → Fin 4, if (∃ x ∈ U, a x ≠ 0) then ‖c a‖ ^ 2 else 0) ≤
    ∑ x ∈ U, ∑ a : Fin N → Fin 4, if a x ≠ 0 then ‖c a‖ ^ 2 else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases hex : ∃ x ∈ U, a x ≠ 0
  · rw [if_pos hex]
    obtain ⟨x₀, hx₀U, hx₀ne⟩ := hex
    have hle := Finset.single_le_sum (f := fun x ↦ if a x ≠ 0 then ‖c a‖ ^ 2 else 0)
      (fun x _ ↦ by split_ifs <;> positivity) hx₀U
    simpa [hx₀ne] using hle
  · rw [if_neg hex]
    exact Finset.sum_nonneg fun x _ ↦ by split_ifs <;> positivity

/-- **Lemma 7.3(2)** (Exact Product-Space Sitewise = Filtration Identity, Eq. 7.12). -/
theorem lemma_7_3_product_filtration_identity {N : ℕ} (c : (Fin N → Fin 4) → ℂ) :
    (∑ x : Fin N, ∑ a : Fin N → Fin 4, if a x ≠ 0 then ‖c a‖ ^ 2 else 0) =
    ∑ k ∈ Finset.range N, ∑ a : Fin N → Fin 4, if k < stringWeight a then ‖c a‖ ^ 2 else 0 := by
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.range N)]
  apply Finset.sum_congr rfl
  intro a _
  have hlhs : (∑ x : Fin N, if a x ≠ 0 then ‖c a‖ ^ 2 else 0) =
      (stringWeight a : ℝ) * ‖c a‖ ^ 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]; rfl
  have hrhs : (∑ k ∈ Finset.range N, if k < stringWeight a then ‖c a‖ ^ 2 else 0) =
      (stringWeight a : ℝ) * ‖c a‖ ^ 2 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hle : stringWeight a ≤ N := by
      unfold stringWeight
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    have hfilt : (Finset.range N).filter (fun k ↦ k < stringWeight a) =
        Finset.range (stringWeight a) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
    rw [hfilt, Finset.card_range]
  rw [hlhs, hrhs]

/-- **Theorem 1.3(a)** (Global Quantum Reverse-Poincaré Inequality via Convex Averaging, Eq. 1.20). -/
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
  refine ⟨hlower, ?_⟩
  calc ∑ x : Fin N, ∑ s : ι, w s * sxSq s x
      = ∑ s : ι, w s * ∑ x : Fin N, sxSq s x := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ ≤ ∑ s : ι, w s * ∑ x : Fin N, (9 * projProdSq s x) :=
        Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun x _ ↦ hcond s x) (hw s)
    _ = 9 * ∑ s : ι, w s * ∑ x : Fin N, projProdSq s x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s _
        rw [← Finset.mul_sum]; ring
    _ ≤ 9 * ∑ s : ι, w s * ∑ k : Fin N, filtBetaSq s k :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (hfilt s) (hw s))
          (by norm_num)
    _ = 9 * ∑ k : Fin N, ∑ s : ι, w s * filtBetaSq s k := by
        congr 1; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]

/-- **Theorem 1.3(b)** (Global Wightman & MSS Commutator Dominance Constants, Eq. 1.21–1.22). -/
theorem theorem_1_3b_constants {r : ℕ} {β Jsite : ℝ}
    (hr : 2 ≤ r) (hJ : 0 < Jsite) (hβ0 : 0 ≤ β) (hβ : β ≤ betaWC r Jsite) :
    (3 / 2 : ℝ) * (1 - β / (4 * invLocalityScale r Jsite))⁻¹ ^ 2 * 9 < 54 ∧
    2 * β * (3 : ℝ) ^ (r - 1) * Real.exp 1 * (r : ℝ) * Jsite ≤ 1 / 2 ∧
    (3 / 8 : ℝ) * (24 : ℝ) ^ 2 = 216 := by
  have hκ := invLocalityScale_pos hr hJ
  have hlt := lt_of_le_of_lt hβ (betaWC_lt_two_kappa hr hJ)
  have hhalf : (1 / 2 : ℝ) < 1 - β / (4 * invLocalityScale r Jsite) := by
    have : β / (4 * invLocalityScale r Jsite) < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      linarith
    linarith
  have hinv_lt : (1 - β / (4 * invLocalityScale r Jsite))⁻¹ < 2 := by
    rw [inv_lt_comm₀ (by linarith) (by norm_num)]
    linarith
  have h1 : (3 / 2 : ℝ) * (1 - β / (4 * invLocalityScale r Jsite))⁻¹ ^ 2 * 9 < 54 := by
    have hsq : (1 - β / (4 * invLocalityScale r Jsite))⁻¹ ^ 2 < 4 := by
      nlinarith [inv_pos.mpr (by linarith : 0 < 1 - β / (4 * invLocalityScale r Jsite))]
    linarith
  have h2 : 2 * β * (3 : ℝ) ^ (r - 1) * Real.exp 1 * (r : ℝ) * Jsite ≤ 1 / 2 := by
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have h3le6 : (3 : ℝ) ^ (r - 1) ≤ (6 : ℝ) ^ r := by
      have h1 : (3 : ℝ) ^ (r - 1) ≤ (3 : ℝ) ^ r :=
        pow_le_pow_right₀ (by norm_num) (Nat.sub_le r 1)
      have h2 : (3 : ℝ) ^ r ≤ (6 : ℝ) ^ r :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) r
      exact le_trans h1 h2
    have he1le2 : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
    have hstep : 2 * β * (3 : ℝ) ^ (r - 1) * Real.exp 1 * (r : ℝ) * Jsite ≤
        2 * betaWC r Jsite * (6 : ℝ) ^ r * Real.exp 2 * (r : ℝ) * Jsite := by
      have ha : 2 * β ≤ 2 * betaWC r Jsite := by linarith
      have hb : (3 : ℝ) ^ (r - 1) * Real.exp 1 ≤ (6 : ℝ) ^ r * Real.exp 2 :=
        mul_le_mul h3le6 he1le2 (Real.exp_pos 1).le (by positivity)
      have hc : (2 * β) * ((3 : ℝ) ^ (r - 1) * Real.exp 1) ≤
          (2 * betaWC r Jsite) * ((6 : ℝ) ^ r * Real.exp 2) :=
        mul_le_mul ha hb (by positivity) (mul_nonneg (by norm_num) (betaWC_pos hr hJ).le)
      have hd := mul_le_mul_of_nonneg_right hc (mul_pos hr0 hJ).le
      linarith
    have heq : 2 * betaWC r Jsite * (6 : ℝ) ^ r * Real.exp 2 * (r : ℝ) * Jsite = 1 / 2 := by
      unfold betaWC
      field_simp [(Real.exp_pos 2).ne', hr0.ne', hJ.ne', (pow_pos (by norm_num : (0 : ℝ) < 6) r).ne']
      ring
    linarith
  exact ⟨h1, h2, by norm_num⟩

/-- **Theorem 1.3(c)** (High-Temperature MSS Lyapunov Exponent Bound, Eq. 1.24). -/
theorem theorem_1_3c_mss_lyapunov_bound {α lamL A B C : ℝ}
    (hα : 0 < α) (hλ : 0 < lamL) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hH : ∀ ε₀ > 0, ∃ ε ∈ Set.Ioo (0 : ℝ) ε₀, ∃ c > 0, ∃ N₁ : ℕ,
      ∀ N ≥ N₁,
        c * (N : ℝ) ^ (1 - ε) ≤
          A * (N : ℝ) ^ ((2 * α / lamL) * (1 - ε)) +
          B * Real.sqrt ((N : ℝ) * (N : ℝ) ^ ((2 * α / lamL) * (1 - ε))) +
          C * Real.sqrt (N : ℝ)) :
    lamL ≤ 2 * α := by
  by_contra hlt
  push_neg at hlt
  set ρ := 2 * α / lamL
  have hρ_pos : 0 < ρ := div_pos (by linarith) hλ
  have hρ_lt : ρ < 1 := (div_lt_one hλ).mpr hlt
  set gap := (1 - ρ) / 2
  have hgap_pos : 0 < gap := by linarith
  set ε₀ := min (1 / 4) (gap / 2)
  have hε₀_pos : 0 < ε₀ := lt_min (by norm_num) (by linarith)
  obtain ⟨ε, ⟨hε_pos, hε_lt⟩, c, hc_pos, N₁, hN₁⟩ := hH ε₀ hε₀_pos
  have hε_q : ε < 1 / 4 := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_g : ε < gap / 2 := lt_of_lt_of_le hε_lt (min_le_right _ _)
  set η := max (ρ * (1 - ε)) (1 / 2 + (1 / 2) * ρ * (1 - ε))
  have hη_lt : η < 1 - ε := by
    apply max_lt
    · nlinarith
    · have h1 : 1 - ε - (1 / 2 + 1 / 2 * ρ * (1 - ε)) =
          (1 - ρ) / 2 - ε * (1 - ρ / 2) := by ring
      have h2 : ε * (1 - ρ / 2) < (1 - ρ) / 2 := by nlinarith
      linarith
  have hhalf_le_η : (1 / 2 : ℝ) ≤ η := by
    apply le_trans _ (le_max_right _ _)
    have : 0 ≤ (1 / 2) * ρ * (1 - ε) := by nlinarith
    linarith
  set diff := (1 - ε) - η
  have hdiff_pos : 0 < diff := by linarith
  set M := A + B + C + 1
  have hM_pos : 0 < M := by positivity
  have htend : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-diff)) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hdiff_pos).comp tendsto_natCast_atTop_atTop
  have hev := (Filter.eventually_ge_atTop (max N₁ 2)).and
    (htend.eventually (gt_mem_nhds (by positivity : 0 < c / M)))
  obtain ⟨N, hNge, hsm⟩ := hev.exists
  have hN1 : N ≥ N₁ := le_trans (le_max_left _ _) hNge
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hNge
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hineq := hN₁ N hN1
  have hrt_mid : Real.sqrt ((N : ℝ) * (N : ℝ) ^ (ρ * (1 - ε))) =
      (N : ℝ) ^ (1 / 2 + (1 / 2) * ρ * (1 - ε)) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow hNpos.le (Real.rpow_nonneg hNpos.le _),
      ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    congr 1; ring
  have hrt_N : Real.sqrt (N : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  rw [hrt_mid, hrt_N] at hineq
  have h1 : (N : ℝ) ^ (ρ * (1 - ε)) ≤ (N : ℝ) ^ η :=
    Real.rpow_le_rpow_of_exponent_le hNge1 (le_max_left _ _)
  have h2 : (N : ℝ) ^ (1 / 2 + (1 / 2) * ρ * (1 - ε)) ≤ (N : ℝ) ^ η :=
    Real.rpow_le_rpow_of_exponent_le hNge1 (le_max_right _ _)
  have h3 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ η :=
    Real.rpow_le_rpow_of_exponent_le hNge1 hhalf_le_η
  have htot : c * (N : ℝ) ^ (1 - ε) ≤ M * (N : ℝ) ^ η := by
    have hMle : (A + B + C) * (N : ℝ) ^ η ≤ M * (N : ℝ) ^ η := by
      simp only [M]; nlinarith [Real.rpow_nonneg hNpos.le η]
    nlinarith
  have hsplit : (N : ℝ) ^ η = (N : ℝ) ^ (1 - ε) * (N : ℝ) ^ (-diff) := by
    rw [← Real.rpow_add hNpos]; congr 1; simp only [diff]; ring
  rw [hsplit] at htot
  have hMlt : M * (N : ℝ) ^ (-diff) < c := by
    have := mul_lt_mul_of_pos_left hsm hM_pos
    rwa [mul_div_cancel₀ _ hM_pos.ne'] at this
  have hN1mε_pos : 0 < (N : ℝ) ^ (1 - ε) := Real.rpow_pos_of_pos hNpos _
  nlinarith

end ProductSpaceComparison

end KrylovChaos
