/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.HighTempCumulant
import KrylovChaos.HighTempParams
import KrylovChaos.ShiftedThermalSize
import KrylovChaos.Araki1DConcrete
import KrylovChaos.Milestone3Sections678

/-!
# Unconditional High-Temperature Entropic Background Decoupling (Proposition 6.4(2), Eq. 6.7)

Eliminates any external cumulant assumption by wiring `lemma_6_3_combined_cumulant_bound`
(`HighTempCumulant.lean`), the PSD Gibbs variational principle, Heisenberg invariance of
relative entropy, and the causal local shell expansion of the thermal background operator
`ℬ_β = thermalBackgroundOp hH β` into Proposition 6.4(2) (Eq. 6.7) on `QubitOp N`:
1. `gibbsRelEntropy_nonneg_psd` and `gibbs_variational_bound_psd`: Klein's inequality and
   Gibbs variational bound for arbitrary positive semidefinite density matrices `ρ` (`0 ≤ λ_i`).
2. `entropic_decoupling_psd`: for any `k_X`-local Hermitian observable `X` with site strength
   `≤ gX`, `|Re Tr((ρ_t - ρ_β) X)| ≤ (4 √2 (D(ρ ‖ ρ_β) + 1) / Λ₀') √N` for all `N ≥ 1, t : ℝ`.
3. `bgShell` and `bgShell_local_decomp`: Hermitian `(1 + k(r-1))`-local shell decomposition
   `ℬ_β = ∑' k, bgShell hH β k` with explicit site-strength bound `g_k`.
4. `prop_6_4_part2_unconditional`: unconditional bound `|III(O(t))| ≤ C₂ √N` and Eq. (6.7)
   for any `r`-local Hamiltonian (`r ≥ 2`), `β ∈ [0, highTempBetaWC r Jsite]`, and `s₀`-local
   Hermitian observable `O` (`‖O‖_{β,W} = 1`, `opNorm O ≤ C_O`).
-/

namespace KrylovChaos

open scoped BigOperators Matrix ComplexOrder
open Matrix Complex Filter Topology

section PSDGibbsVariational

private lemma log_ineq_kl_psd {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    0 ≤ x * (Real.log x - Real.log y) - x + y := by
  by_cases hx0 : x = 0
  · subst hx0; simp [hy.le]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have h1 : 1 - y / x ≤ -Real.log (y / x) := by
      have hlog := Real.log_le_sub_one_of_pos (div_pos hy hxp)
      linarith
    have h2 : Real.log (y / x) = Real.log y - Real.log x := Real.log_div hy.ne' hxp.ne'
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_left h1 hxp.le
    have hmul : x * (1 - y / x) = x - y := by field_simp [hxp.ne']
    linarith

private lemma trace_herm_mul_hermFunc_re_psd {N : ℕ} {ρ A : QubitOp N}
    (hρ : ρ.IsHermitian) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (ρ * hermFunc hA (fun y ↦ (f y : ℂ))).trace.re =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖((hρ.eigenvectorUnitary : QubitOp N)ᴴ * (hA.eigenvectorUnitary : QubitOp N)) i j‖ ^ 2 *
          (hρ.eigenvalues i * f (hA.eigenvalues j)) := by
  set U : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)
  set V : QubitOp N := (hA.eigenvectorUnitary : QubitOp N)
  set W : QubitOp N := Uᴴ * V
  set Dρ : QubitOp N := Matrix.diagonal (fun i ↦ (hρ.eigenvalues i : ℂ))
  set F : QubitOp N := Matrix.diagonal (fun j ↦ (f (hA.eigenvalues j) : ℂ))
  have hρ_eq : ρ = U * Dρ * Uᴴ := (hermFunc_id hρ).symm
  have hA_eq : hermFunc hA (fun y ↦ (f y : ℂ)) = V * F * Vᴴ := rfl
  have hcyc : (ρ * hermFunc hA (fun y ↦ (f y : ℂ))).trace = (Dρ * W * F * Wᴴ).trace := by
    rw [hρ_eq, hA_eq]
    have h1 : U * Dρ * Uᴴ * (V * F * Vᴴ) = U * (Dρ * W * F * Vᴴ) := by
      simp only [W, Matrix.mul_assoc]
    rw [h1, Matrix.trace_mul_comm]
    have h2 : Dρ * W * F * Vᴴ * U = Dρ * W * F * Wᴴ := by
      simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [h2]
  rw [hcyc]
  simp only [Dρ, F, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.conjTranspose_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have hnorm : W i j * star (W i j) = (‖W i j‖ : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.mul_conj']
  have hrew : (hρ.eigenvalues i : ℂ) * W i j * (f (hA.eigenvalues j) : ℂ) * star (W i j) =
      (((‖W i j‖ ^ 2 * (hρ.eigenvalues i * f (hA.eigenvalues j)) : ℝ) : ℂ)) := by
    push_cast; linear_combination (hρ.eigenvalues i : ℂ) * (f (hA.eigenvalues j) : ℂ) * hnorm
  rw [hrew, Complex.ofReal_re]

/-- **Klein's Inequality for PSD Density Matrices (`0 ≤ eigenvalues`)**: `gibbsRelEntropy hρ hH β ≥ 0`. -/
theorem gibbsRelEntropy_nonneg_psd {N : ℕ} {ρ H : QubitOp N}
    (hρ : ρ.IsHermitian) (hH : H.IsHermitian)
    (hρ_nn : ∀ i : QubitIdx N, 0 ≤ hρ.eigenvalues i)
    (hρ_tr : ρ.trace = 1) (β : ℝ) :
    0 ≤ gibbsRelEntropy hρ hH β := by
  set U : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)
  set V : QubitOp N := (hH.eigenvectorUnitary : QubitOp N)
  set W : QubitOp N := Uᴴ * V
  have hUU : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hρ.eigenvectorUnitary.2
  have hU'U : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hρ.eigenvectorUnitary.2
  have hVV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hH.eigenvectorUnitary.2
  have hV'V : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hH.eigenvectorUnitary.2
  have hrow : ∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 = 1 := by
    intro i
    have hW1 : W * Wᴴ = 1 := by
      simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc Uᴴ * V * (Vᴴ * U) = Uᴴ * (V * Vᴴ) * U := by simp only [Matrix.mul_assoc]
        _ = Uᴴ * U := by rw [hVV, Matrix.mul_one]
        _ = 1 := hU'U
    have h1 := congrFun (congrFun hW1 i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h1
    have hre := congrArg Complex.re h1
    rw [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    apply Finset.sum_congr rfl; intro j _
    rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hcol : ∀ j : QubitIdx N, ∑ i : QubitIdx N, ‖W i j‖ ^ 2 = 1 := by
    intro j
    have hW2 : Wᴴ * W = 1 := by
      simp only [W, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      calc Vᴴ * U * (Uᴴ * V) = Vᴴ * (U * Uᴴ) * V := by simp only [Matrix.mul_assoc]
        _ = Vᴴ * V := by rw [hUU, Matrix.mul_one]
        _ = 1 := hV'V
    have h1 := congrFun (congrFun hW2 j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h1
    have hre := congrArg Complex.re h1
    rw [Complex.re_sum, Complex.one_re] at hre
    rw [← hre]
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hsum_ρ : ∑ i : QubitIdx N, hρ.eigenvalues i = 1 := by
    have h1 := hermFunc_trace hρ (fun x ↦ (x : ℂ))
    rw [hermFunc_id hρ, hρ_tr] at h1
    simpa [Complex.re_sum] using (congrArg Complex.re h1.symm)
  set Z : ℝ := gibbsPartitionFn hH β
  have hZpos : 0 < Z := gibbsPartitionFn_pos hH β
  let q : QubitIdx N → ℝ := fun j ↦ Real.exp (-β * hH.eigenvalues j) / Z
  have hq_pos : ∀ j : QubitIdx N, 0 < q j := fun j ↦ div_pos (Real.exp_pos _) hZpos
  have hsum_q : ∑ j : QubitIdx N, q j = 1 := by
    dsimp only [q]
    rw [← Finset.sum_div]
    exact div_self hZpos.ne'
  have htr_log : (ρ * hermFunc hρ (fun x ↦ (Real.log x : ℂ))).trace.re =
      ∑ i : QubitIdx N, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
    have h1 : ρ * hermFunc hρ (fun x ↦ (Real.log x : ℂ)) =
        hermFunc hρ (fun x ↦ (x : ℂ) * (Real.log x : ℂ)) := by
      calc ρ * hermFunc hρ (fun x ↦ (Real.log x : ℂ))
          = hermFunc hρ (fun x ↦ (x : ℂ)) * hermFunc hρ (fun x ↦ (Real.log x : ℂ)) :=
            congrArg (· * _) (hermFunc_id hρ).symm
        _ = hermFunc hρ (fun x ↦ (x : ℂ) * (Real.log x : ℂ)) := hermFunc_mul hρ _ _
    rw [h1, hermFunc_trace, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have htr_H : (ρ * (((β : ℝ) : ℂ) • H)).trace.re =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (β * hH.eigenvalues j)) := by
    have hsm : (((β : ℝ) : ℂ) • H) = hermFunc hH (fun y ↦ ((β * y : ℝ) : ℂ)) := by
      conv_lhs => rw [← hermFunc_id hH]
      unfold hermFunc
      ext a b
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.diagonal_apply,
        Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _
      apply Finset.sum_congr rfl; intro k _
      split_ifs <;> simp [mul_comm, mul_left_comm, mul_assoc]
    rw [hsm]
    exact trace_herm_mul_hermFunc_re_psd hρ hH (fun y ↦ β * y)
  have hrel_eq : gibbsRelEntropy hρ hH β =
      ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - Real.log (q j)) -
          hρ.eigenvalues i + q j) := by
    unfold gibbsRelEntropy
    rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, htr_log, htr_H]
    have hlog_q : ∀ j : QubitIdx N, Real.log (q j) = -β * hH.eigenvalues j - Real.log Z := by
      intro j; dsimp only [q]; rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
    have hsum1 : ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (hρ.eigenvalues i)) =
        ∑ i : QubitIdx N, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) := by
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_mul, hrow i, one_mul]
    have hsum2 : ∑ i : QubitIdx N, ∑ j : QubitIdx N,
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log Z) = Real.log Z := by
      have : ∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log Z) =
          hρ.eigenvalues i * Real.log Z := fun i ↦ by rw [← Finset.sum_mul, hrow i, one_mul]
      simp_rw [this, ← Finset.sum_mul, hsum_ρ, one_mul]
    have hsum3 : ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i = 1 := by
      have : ∀ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * hρ.eigenvalues i = hρ.eigenvalues i :=
        fun i ↦ by rw [← Finset.sum_mul, hrow i, one_mul]
      simp_rw [this]; exact hsum_ρ
    have hsum4 : ∑ i : QubitIdx N, ∑ j : QubitIdx N, ‖W i j‖ ^ 2 * q j = 1 := by
      rw [Finset.sum_comm]
      have : ∀ j : QubitIdx N, ∑ i : QubitIdx N, ‖W i j‖ ^ 2 * q j = q j :=
        fun j ↦ by rw [← Finset.sum_mul, hcol j, one_mul]
      simp_rw [this]; exact hsum_q
    have hexpand : ∀ (i j : QubitIdx N),
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (Real.log (hρ.eigenvalues i) - Real.log (q j)) -
          hρ.eigenvalues i + q j) =
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log (hρ.eigenvalues i)) +
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * (β * hH.eigenvalues j)) +
        ‖W i j‖ ^ 2 * (hρ.eigenvalues i * Real.log Z) -
        ‖W i j‖ ^ 2 * hρ.eigenvalues i +
        ‖W i j‖ ^ 2 * q j := fun i j ↦ by rw [hlog_q j]; ring
    simp_rw [hexpand]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hsum1, hsum2, hsum3, hsum4]
    dsimp only [Z]
    ring
  rw [hrel_eq]
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (sq_nonneg _) (log_ineq_kl_psd (hρ_nn i) (hq_pos j))

/-- **Gibbs Variational Bound for PSD Density Matrices (`0 ≤ eigenvalues`)**:
`(ρ * X).trace.re ≤ gibbsRelEntropy hρ hH β + Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β)`. -/
theorem gibbs_variational_bound_psd {N : ℕ} {ρ H X : QubitOp N}
    (hρ : ρ.IsHermitian) (hH : H.IsHermitian) (hX : X.IsHermitian)
    (hρ_nn : ∀ i : QubitIdx N, 0 ≤ hρ.eigenvalues i)
    (hρ_tr : ρ.trace = 1) (β : ℝ) :
    let K : QubitOp N := ((-β : ℝ) : ℂ) • H + X
    have hK : K.IsHermitian := by
      simp only [K, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Complex.star_def, Complex.conj_ofReal, hH.eq, hX.eq]
    (ρ * X).trace.re ≤
      gibbsRelEntropy hρ hH β +
        Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β) := by
  intro K hK
  have hnn := gibbsRelEntropy_nonneg_psd hρ hK hρ_nn hρ_tr (-1)
  have hZβ := gibbsPartitionFn_pos hH β
  have hZK := gibbsPartitionFn_pos hK (-1)
  have hlog_div : Real.log (gibbsPartitionFn hK (-1) / gibbsPartitionFn hH β) =
      Real.log (gibbsPartitionFn hK (-1)) - Real.log (gibbsPartitionFn hH β) :=
    Real.log_div hZK.ne' hZβ.ne'
  have hK_smul : (((-1 : ℝ) : ℂ) • K) = ((β : ℝ) : ℂ) • H - X := by
    dsimp only [K]
    rw [smul_add, smul_smul]; push_cast
    rw [show (-1 : ℂ) * -(β : ℂ) = (β : ℂ) by ring, neg_one_smul, sub_eq_add_neg]
  unfold gibbsRelEntropy at hnn ⊢
  rw [hK_smul, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re] at hnn
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re, hlog_div]
  linarith

/-- **Unconditional Single-Shell Entropic Decoupling (Lemma 6.3 + PSD Variational Principle)**:
For any `N ≥ 1`, `r`-local Hermitian `H` (`r ≥ 2`, site strength `≤ Jsite`), `k_X`-local
Hermitian `X = ∑ Z ∈ E_X, xOp Z` (`1 ≤ k_X`, site strength `≤ gX`), `β ∈ [0, (8 e² r Jsite)⁻¹]`,
PSD density matrix `ρ` (`0 ≤ eigenvalues`, `ρ.trace = 1`), and real time `t : ℝ`:
`|((U(t) * ρ * U(t)ᴴ - gibbsRho hH β) * X).trace.re| ≤
  4 * √2 * (gibbsRelEntropy hρ hH β + 1) / Λ₀' * √N`. -/
theorem entropic_decoupling_single_shell {N r k_X : ℕ}
    (hN : 1 ≤ N) (hr : 2 ≤ r) (hkX : 1 ≤ k_X)
    (E : Finset (Finset (Fin N))) (hE_ne : ∀ Z ∈ E, Z.Nonempty) (hE_card : ∀ Z ∈ E, Z.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hh_supp : ∀ Z, h Z ∈ supportedOn Z)
    (hH : (∑ Z ∈ E, h Z).IsHermitian)
    {Jsite : ℝ} (hJ : 0 < Jsite)
    (hH_site : ∀ x : Fin N, ∑ Z ∈ E.filter (fun Z ↦ x ∈ Z), opNorm (h Z) ≤ Jsite)
    (E_X : Finset (Finset (Fin N))) (hEX_ne : ∀ Z ∈ E_X, Z.Nonempty)
    (hEX_card : ∀ Z ∈ E_X, Z.card ≤ k_X)
    (xOp : Finset (Fin N) → QubitOp N) (hx_supp : ∀ Z, xOp Z ∈ supportedOn Z)
    (hX : (∑ Z ∈ E_X, xOp Z).IsHermitian)
    {gX : ℝ} (hgX : 0 < gX)
    (hX_site : ∀ x : Fin N, ∑ Z ∈ E_X.filter (fun Z ↦ x ∈ Z), opNorm (xOp Z) ≤ gX)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / (8 * Real.exp 2 * (r : ℝ) * Jsite))
    {ρ : QubitOp N} (hρ : ρ.IsHermitian)
    (hρ_nn : ∀ i : QubitIdx N, 0 ≤ hρ.eigenvalues i)
    (hρ_tr : ρ.trace = 1) (t : ℝ) :
    let H := ∑ Z ∈ E, h Z
    let X := ∑ Z ∈ E_X, xOp Z
    let U := complexPropagator hH (t : ℂ)
    let ρt := U * ρ * Uᴴ
    let kr := max r k_X
    let Λ₀' := 1 / (16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * gX)
    |((ρt - gibbsRho hH β) * X).trace.re| ≤
      (4 * Real.sqrt 2 * (gibbsRelEntropy hρ hH β + 1) / Λ₀') * Real.sqrt (N : ℝ) := by
  intro H X U ρt kr Λ₀'
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hkr_pos : (0 : ℝ) < (kr : ℝ) := by exact_mod_cast (by omega : 0 < kr)
  have hΛ_pos : 0 < Λ₀' := by dsimp only [Λ₀']; positivity
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hD_nn : 0 ≤ gibbsRelEntropy hρ hH β := gibbsRelEntropy_nonneg_psd hρ hH hρ_nn hρ_tr β
  -- Prove one-sided bound for any `xOp'` with the same site strength `gX`, then apply to `xOp` and `-xOp`.
  have honesided : ∀ (xOp' : Finset (Fin N) → QubitOp N),
      (∀ Z, xOp' Z ∈ supportedOn Z) →
      (∑ Z ∈ E_X, xOp' Z).IsHermitian →
      (∀ x : Fin N, ∑ Z ∈ E_X.filter (fun Z ↦ x ∈ Z), opNorm (xOp' Z) ≤ gX) →
      ((ρt - gibbsRho hH β) * (∑ Z ∈ E_X, xOp' Z)).trace.re ≤
        (4 * Real.sqrt 2 * (gibbsRelEntropy hρ hH β + 1) / Λ₀') * Real.sqrt (N : ℝ) := by
    intro xOp' hx'_supp hX' hX'_site
    let X' := ∑ Z ∈ E_X, xOp' Z
    let μ' := (gibbsRho hH β * X').trace.re
    let Xtilde' : QubitOp N := X' - (μ' : ℂ) • 1
    have hXt'_herm : Xtilde'.IsHermitian := by
      simp only [Xtilde', X', Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal, hX'.eq]
    have hU_unit : Uᴴ * U = 1 := by
      dsimp only [U, complexPropagator]
      rw [hermFunc_conjTranspose, hermFunc_mul]
      have hfun : (fun x : ℝ ↦ star (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) *
          Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) = fun _ ↦ 1 := by
        funext x
        rw [Complex.star_def, ← Complex.exp_conj]
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
        rw [← Complex.exp_add]
        have h0 : -Complex.I * (t : ℂ) * (x : ℂ) + Complex.I * (t : ℂ) * (x : ℂ) = 0 := by ring
        rw [h0, Complex.exp_zero]
      rw [hfun, hermFunc_one]
    have hρt_herm : ρt.IsHermitian := by
      simp only [ρt, Matrix.IsHermitian, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hρ.eq, Matrix.mul_assoc]
    have hρt_tr : ρt.trace = 1 := by
      dsimp only [ρt]
      calc (U * ρ * Uᴴ).trace = (Uᴴ * (U * ρ)).trace := Matrix.trace_mul_comm _ _
        _ = ((Uᴴ * U) * ρ).trace := by simp only [Matrix.mul_assoc]
        _ = ρ.trace := by rw [hU_unit, Matrix.one_mul]
        _ = 1 := hρ_tr
    have hρt_nn : ∀ i : QubitIdx N, 0 ≤ hρt_herm.eigenvalues i := by
      intro i
      -- `hρt_herm.eigenvalues i` is a convex combination of `hρ.eigenvalues j ≥ 0`.
      set Q : QubitOp N := (hρt_herm.eigenvectorUnitary : QubitOp N)
      set P : QubitOp N := (hρ.eigenvectorUnitary : QubitOp N)
      have hQHQ : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.mp hρt_herm.eigenvectorUnitary.2
      let W : QubitOp N := Qᴴ * U * P
      have hW_eq : Qᴴ * ρt * Q = W * Matrix.diagonal (fun j ↦ (hρ.eigenvalues j : ℂ)) * Wᴴ := by
        have hρ_id : ρ = P * Matrix.diagonal (fun j ↦ (hρ.eigenvalues j : ℂ)) * Pᴴ := (hermFunc_id hρ).symm
        dsimp only [ρt, W]
        conv_lhs => rw [hρ_id]
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      have hD : Qᴴ * ρt * Q = Matrix.diagonal (fun a ↦ (hρt_herm.eigenvalues a : ℂ)) := by
        have hρt_id : ρt = Q * Matrix.diagonal (fun a ↦ (hρt_herm.eigenvalues a : ℂ)) * Qᴴ :=
          (hermFunc_id hρt_herm).symm
        conv_lhs => rw [hρt_id]
        calc Qᴴ * (Q * Matrix.diagonal (fun a ↦ (hρt_herm.eigenvalues a : ℂ)) * Qᴴ) * Q
            = (Qᴴ * Q) * Matrix.diagonal (fun a ↦ (hρt_herm.eigenvalues a : ℂ)) * (Qᴴ * Q) := by
              simp only [Matrix.mul_assoc]
          _ = Matrix.diagonal (fun a ↦ (hρt_herm.eigenvalues a : ℂ)) := by
              rw [hQHQ, Matrix.one_mul, Matrix.mul_one]
      have hent := congrFun (congrFun (hD.symm.trans hW_eq) i) i
      simp only [Matrix.diagonal_apply_eq, Matrix.mul_apply, Matrix.diagonal_apply,
        mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        Matrix.conjTranspose_apply] at hent
      have hre := congrArg Complex.re hent
      rw [Complex.ofReal_re, Complex.re_sum] at hre
      rw [hre]
      refine Finset.sum_nonneg fun j _ ↦ ?_
      have hnorm : W i j * star (W i j) = (‖W i j‖ : ℂ) ^ 2 := by
        rw [Complex.star_def, Complex.mul_conj']
      have hrew : W i j * (hρ.eigenvalues j : ℂ) * star (W i j) =
          (((‖W i j‖ ^ 2 * hρ.eigenvalues j : ℝ) : ℂ)) := by
        push_cast; linear_combination (hρ.eigenvalues j : ℂ) * hnorm
      rw [hrew, Complex.ofReal_re]
      exact mul_nonneg (sq_nonneg _) (hρ_nn j)
    have hdiff_eq : ((ρt - gibbsRho hH β) * X').trace.re = (ρt * Xtilde').trace.re := by
      dsimp only [Xtilde', μ']
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, Complex.sub_re,
        Complex.sub_re, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, hρt_tr, smul_eq_mul,
        mul_one, Complex.ofReal_re]
    rw [hdiff_eq]
    -- Apply variational bound + cumulant bound for any `lam ∈ (0, Λ₀' / 2]`.
    have hstep : ∀ lam : ℝ, 0 < lam → lam ≤ Λ₀' / 2 →
        (ρt * Xtilde').trace.re ≤
          gibbsRelEntropy hρ hH β / lam + 8 * (N : ℝ) * lam / (Λ₀') ^ 2 := by
      intro lam hlam_pos hlam_le
      have hlamX : (((lam : ℝ) : ℂ) • Xtilde').IsHermitian := by
        simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Complex.star_def,
          Complex.conj_ofReal, hXt'_herm.eq]
      have hvar := gibbs_variational_bound_psd hρt_herm hH hlamX hρt_nn hρt_tr β
      have hinv := gibbsRelEntropy_heisenberg_invariant hρ hH β t
      have hcum := lemma_6_3_combined_cumulant_bound hr hkX E hE_ne hE_card h hh_supp hH hJ hH_site
        E_X hEX_ne hEX_card xOp' hx'_supp hX' hgX hX'_site hβ0 hβ
        (by rw [abs_of_pos hlam_pos]; exact hlam_le)
      have htr_smul : (ρt * (((lam : ℝ) : ℂ) • Xtilde')).trace.re = lam * (ρt * Xtilde').trace.re := by
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im]; ring
      rw [htr_smul] at hvar
      have hcomb : lam * (ρt * Xtilde').trace.re ≤
          gibbsRelEntropy hρ hH β + 8 * (N : ℝ) * lam ^ 2 / (Λ₀') ^ 2 := by
        have h1 : gibbsRelEntropy hρt_herm hH β = gibbsRelEntropy hρ hH β := hinv
        have h2 : Real.log (gibbsPartitionFn (by
          simp only [H, Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
            Complex.star_def, Complex.conj_ofReal, hH.eq, hlamX.eq] :
            (((-β : ℝ) : ℂ) • H + ((lam : ℝ) : ℂ) • Xtilde').IsHermitian) (-1) /
          gibbsPartitionFn hH β) ≤ 8 * (N : ℝ) * lam ^ 2 / (Λ₀') ^ 2 := hcum
        linarith
      have hdiv := div_le_div_of_nonneg_right hcomb hlam_pos.le
      rw [mul_div_cancel_left₀ _ hlam_pos.ne', add_div] at hdiv
      have hsimpl : 8 * (N : ℝ) * lam ^ 2 / (Λ₀') ^ 2 / lam = 8 * (N : ℝ) * lam / (Λ₀') ^ 2 := by
        field_simp [hlam_pos.ne', hΛ_pos.ne']
      rw [hsimpl] at hdiv
      exact hdiv
    set D₁ : ℝ := gibbsRelEntropy hρ hH β + 1
    have hD₁_ge1 : 1 ≤ D₁ := by dsimp only [D₁]; linarith
    have hD₁_pos : 0 < D₁ := by linarith
    by_cases hcase : D₁ ≤ 2 * (N : ℝ)
    · -- Optimal interior `lam = Λ₀' * √(D₁ / (8 * N)) ≤ Λ₀' / 2`.
      let lam := Λ₀' * Real.sqrt (D₁ / (8 * (N : ℝ)))
      have hlam_pos : 0 < lam := by dsimp only [lam]; positivity
      have hlam_le : lam ≤ Λ₀' / 2 := by
        dsimp only [lam]
        have hsq : D₁ / (8 * (N : ℝ)) ≤ (1 / 2 : ℝ) ^ 2 := by
          rw [div_le_iff₀ (by positivity)]; linarith
        have hrt : Real.sqrt (D₁ / (8 * (N : ℝ))) ≤ 1 / 2 := by
          calc Real.sqrt (D₁ / (8 * (N : ℝ))) ≤ Real.sqrt ((1 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt hsq
            _ = 1 / 2 := Real.sqrt_sq (by norm_num)
        nlinarith
      have h1 := hstep lam hlam_pos hlam_le
      have h2 : gibbsRelEntropy hρ hH β / lam + 8 * (N : ℝ) * lam / (Λ₀') ^ 2 ≤
          D₁ / lam + 8 * (N : ℝ) * lam / (Λ₀') ^ 2 := by
        gcongr; dsimp only [D₁]; linarith
      have heq_opt : D₁ / lam + 8 * (N : ℝ) * lam / (Λ₀') ^ 2 =
          (4 * Real.sqrt 2 * Real.sqrt D₁ / Λ₀') * Real.sqrt (N : ℝ) := by
        dsimp only [lam]
        have h8N : 0 < 8 * (N : ℝ) := by positivity
        have hrt_eq : Real.sqrt (D₁ / (8 * (N : ℝ))) = Real.sqrt D₁ / (2 * Real.sqrt 2 * Real.sqrt (N : ℝ)) := by
          rw [Real.sqrt_div hD₁_pos.le, show (8 : ℝ) * (N : ℝ) = (2 ^ 2 * 2) * (N : ℝ) by ring,
            Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
        rw [hrt_eq]
        have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have hsqD : Real.sqrt D₁ ^ 2 = D₁ := Real.sq_sqrt hD₁_pos.le
        have hsqN : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hN_pos.le
        field_simp [hΛ_pos.ne', (Real.sqrt_pos.mpr hD₁_pos).ne', (Real.sqrt_pos.mpr hN_pos).ne',
          (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne']
        rw [hsq2, hsqD, hsqN]; ring
      have hsqrtD_le : Real.sqrt D₁ ≤ D₁ := by
        calc Real.sqrt D₁ ≤ Real.sqrt (D₁ ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          _ = D₁ := Real.sqrt_sq hD₁_pos.le
      refine le_trans h1 (le_trans h2 ?_)
      rw [heq_opt]
      gcongr
    · -- Small-`N` regime `2 * N < D₁`: pick `lam = Λ₀' / 2`.
      push Not at hcase
      have h1 := hstep (Λ₀' / 2) (by positivity) le_rfl
      have h2 : gibbsRelEntropy hρ hH β / (Λ₀' / 2) + 8 * (N : ℝ) * (Λ₀' / 2) / (Λ₀') ^ 2 ≤
          4 * D₁ / Λ₀' := by
        have hrew1 : gibbsRelEntropy hρ hH β / (Λ₀' / 2) = 2 * gibbsRelEntropy hρ hH β / Λ₀' := by
          field_simp [hΛ_pos.ne']
        have hrew2 : 8 * (N : ℝ) * (Λ₀' / 2) / (Λ₀') ^ 2 = 4 * (N : ℝ) / Λ₀' := by
          field_simp [hΛ_pos.ne']; ring
        rw [hrew1, hrew2, ← add_div]
        apply div_le_div_of_nonneg_right _ hΛ_pos.le
        dsimp only [D₁] at hcase ⊢; linarith
      have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
      have hsqrtN : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hN_ge1
      refine le_trans h1 (le_trans h2 ?_)
      calc 4 * D₁ / Λ₀' = (4 * 1 * D₁ / Λ₀') * 1 := by ring
        _ ≤ (4 * Real.sqrt 2 * D₁ / Λ₀') * Real.sqrt (N : ℝ) := by gcongr
  rw [abs_le]
  constructor
  · have hneg := honesided (fun Z ↦ -xOp Z)
      (fun Z ↦ (supportedOn Z).neg_mem (hx_supp Z))
      (by
        have heq : ∑ Z ∈ E_X, -xOp Z = -(∑ Z ∈ E_X, xOp Z) := by rw [Finset.sum_neg_distrib]
        rw [heq]; simp only [Matrix.IsHermitian, Matrix.conjTranspose_neg, hX.eq])
      (fun x ↦ by
        have hrew : ∀ Z, opNorm (-xOp Z) = opNorm (xOp Z) := fun Z ↦ by
          rw [show -xOp Z = (-1 : ℂ) • xOp Z by simp, opNorm_smul, norm_neg, norm_one, one_mul]
        simp_rw [hrew]; exact hX_site x)
    have hsum_neg : ∑ Z ∈ E_X, -xOp Z = -X := by dsimp only [X]; rw [Finset.sum_neg_distrib]
    rw [hsum_neg, Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re] at hneg
    linarith
  · exact honesided xOp hx_supp hX hX_site

end PSDGibbsVariational

section ThermalBackgroundShells

set_option maxHeartbeats 400000 in
/-- Heisenberg evolution invariance of `rhoO_op`:
`rhoO_op hH β (heisenbergEvol hH (t : ℂ) O) = U(t) * rhoO_op hH β O * U(t)ᴴ`. -/
lemma rhoO_op_heisenbergEvol_eq_conj {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β t : ℝ) (O : QubitOp N) :
    rhoO_op hH β (heisenbergEvol hH (t : ℂ) O) =
      complexPropagator hH (t : ℂ) * rhoO_op hH β O * (complexPropagator hH (t : ℂ))ᴴ := by
  let U := complexPropagator hH (t : ℂ)
  let Q := (concreteGibbsData hH β).ρQuarter
  have hU_unit : Uᴴ * U = 1 := by
    dsimp only [U, complexPropagator]
    rw [hermFunc_conjTranspose, hermFunc_mul]
    have hfun : (fun x : ℝ ↦ star (Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) *
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) = fun _ ↦ 1 := by
      funext x
      rw [Complex.star_def, ← Complex.exp_conj]
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      rw [← Complex.exp_add]
      have h0 : -Complex.I * (t : ℂ) * (x : ℂ) + Complex.I * (t : ℂ) * (x : ℂ) = 0 := by ring
      rw [h0, Complex.exp_zero]
    rw [hfun, hermFunc_one]
  have hU_neg : complexPropagator hH (-(t : ℂ)) = Uᴴ := by
    dsimp only [U, complexPropagator]
    rw [hermFunc_conjTranspose]
    congr 1; funext x
    rw [Complex.star_def, ← Complex.exp_conj]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]; congr 1; ring
  have hcomm_Q : Q * U = U * Q := by
    change gibbsRhoQuarter hH β * complexPropagator hH (t : ℂ) =
      complexPropagator hH (t : ℂ) * gibbsRhoQuarter hH β
    unfold gibbsRhoQuarter complexPropagator
    rw [Matrix.smul_mul, Matrix.mul_smul, hermFunc_mul, hermFunc_mul]
    have hfn : (fun x : ℝ ↦ ((Real.exp (-(β / 4) * x) : ℝ) : ℂ) * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))) =
        (fun x : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) * ((Real.exp (-(β / 4) * x) : ℝ) : ℂ)) := by
      funext x; ring
    rw [hfn]
  have hcomm_QH : Q * Uᴴ = Uᴴ * Q := by
    rw [← hU_neg]
    change gibbsRhoQuarter hH β * complexPropagator hH (-(t : ℂ)) =
      complexPropagator hH (-(t : ℂ)) * gibbsRhoQuarter hH β
    unfold gibbsRhoQuarter complexPropagator
    rw [Matrix.smul_mul, Matrix.mul_smul, hermFunc_mul, hermFunc_mul]
    have hfn : (fun x : ℝ ↦ ((Real.exp (-(β / 4) * x) : ℝ) : ℂ) * Complex.exp (Complex.I * -(t : ℂ) * (x : ℂ))) =
        (fun x : ℝ ↦ Complex.exp (Complex.I * -(t : ℂ) * (x : ℂ)) * ((Real.exp (-(β / 4) * x) : ℝ) : ℂ)) := by
      funext x; ring
    rw [hfn]
  have hj : jBeta Q (heisenbergEvol hH (t : ℂ) O) = U * jBeta Q O * Uᴴ := by
    unfold jBeta heisenbergEvol
    rw [hU_neg]
    calc Q * (U * O * Uᴴ) * Q
        = (Q * U) * O * (Uᴴ * Q) := by simp only [Matrix.mul_assoc]
      _ = (U * Q) * O * (Q * Uᴴ) := by rw [hcomm_Q, ← hcomm_QH]
      _ = U * (Q * O * Q) * Uᴴ := by simp only [Matrix.mul_assoc]
  change (jBeta Q (heisenbergEvol hH (t : ℂ) O))ᴴ * jBeta Q (heisenbergEvol hH (t : ℂ) O) =
    U * ((jBeta Q O)ᴴ * jBeta Q O) * Uᴴ
  rw [hj]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc U * (jBeta Q O)ᴴ * Uᴴ * (U * jBeta Q O * Uᴴ)
      = U * (jBeta Q O)ᴴ * (Uᴴ * U) * jBeta Q O * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = U * ((jBeta Q O)ᴴ * jBeta Q O) * Uᴴ := by
        rw [hU_unit, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-- The `m`-th imaginary-time commutator shell of
`Δ_{x,α} = e^{(β/2) H} σ_x^α e^{-(β/2) H} - σ_x^α` (`m = 0` gives `0`). -/
noncomputable def shellDelta {N : ℕ} {H : QubitOp N} (β : ℝ) (x : Fin N) (α : Fin 3) :
    ℕ → QubitOp N
  | 0 => 0
  | m + 1 =>
    (((β / 2 : ℝ) : ℂ) ^ (m + 1) / ((m + 1).factorial : ℂ)) •
      adPowMat H (m + 1) (pauliSite x α.succ)

/-- The `k`-th Hermitian shell of the thermal background operator `ℬ_β = thermalBackgroundOp hH β`. -/
noncomputable def bgShell {N : ℕ} (H : QubitOp N) (β : ℝ) (k : ℕ) : QubitOp N :=
  ((1 / 8 : ℝ) : ℂ) • ∑ x : Fin N, ∑ α : Fin 3,
    ∑ m ∈ Finset.Ico 1 k, shellDelta (H := H) β x α m * (shellDelta (H := H) β x α (k - m))ᴴ

lemma bgShell_zero {N : ℕ} (H : QubitOp N) (β : ℝ) : bgShell H β 0 = 0 := by
  unfold bgShell; simp

lemma bgShell_one {N : ℕ} (H : QubitOp N) (β : ℝ) : bgShell H β 1 = 0 := by
  unfold bgShell; simp

/-- Every shell `bgShell H β k` is Hermitian. -/
lemma bgShell_isHermitian {N : ℕ} (H : QubitOp N) (β : ℝ) (k : ℕ) :
    (bgShell H β k).IsHermitian := by
  unfold bgShell Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  congr 1
  simp only [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro α _
  refine Finset.sum_bij (fun m _ ↦ k - m) ?_ ?_ ?_ ?_
  · intro m hm; rw [Finset.mem_Ico] at hm ⊢; omega
  · intro a ha b hb h; rw [Finset.mem_Ico] at ha hb; omega
  · intro m hm; rw [Finset.mem_Ico] at hm
    exact ⟨k - m, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro m hm; rw [Finset.mem_Ico] at hm
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      show k - (k - m) = m by omega]

/-- Exact convergent series for `heisenbergEvol hH (-I * β / 2) (pauliSite x α.succ) - pauliSite x α.succ`. -/
lemma hasSum_shellDelta {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (x : Fin N) (α : Fin 3) :
    HasSum (shellDelta (H := H) β x α)
      (heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) (pauliSite x α.succ) - pauliSite x α.succ) := by
  have hhas := hasSum_heisenbergEvol_adPow hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) (pauliSite x α.succ)
  have hcoef : Complex.I * (-Complex.I * ((β / 2 : ℝ) : ℂ)) = ((β / 2 : ℝ) : ℂ) := by
    calc Complex.I * (-Complex.I * ((β / 2 : ℝ) : ℂ))
        = -(Complex.I * Complex.I) * ((β / 2 : ℝ) : ℂ) := by ring
      _ = -(-1) * ((β / 2 : ℝ) : ℂ) := by rw [Complex.I_mul_I]
      _ = ((β / 2 : ℝ) : ℂ) := by ring
  simp_rw [hcoef] at hhas
  have h0 : (((β / 2 : ℝ) : ℂ) ^ 0 / ((0 : ℕ).factorial : ℂ)) • adPowMat H 0 (pauliSite x α.succ) =
      pauliSite x α.succ := by
    simp [adPowMat]
  have hadd := hhas.add (hasSum_ite_eq 0 (-pauliSite x α.succ))
  have hsum_eq : heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) (pauliSite x α.succ) + -pauliSite x α.succ =
      heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) (pauliSite x α.succ) - pauliSite x α.succ := by
    abel
  rw [hsum_eq] at hadd
  refine hadd.congr_fun fun m ↦ ?_
  cases m with
  | zero => simp [shellDelta, adPowMat]
  | succ m => simp [shellDelta]

/-- Operator-norm bound on `shellDelta`: `opNorm (shellDelta β x α m) ≤ (2 * |β / 2| * opNorm H) ^ m / m!`. -/
lemma opNorm_shellDelta_le {N : ℕ} {H : QubitOp N} (β : ℝ) (x : Fin N) (α : Fin 3) (m : ℕ) :
    opNorm (shellDelta (H := H) β x α m) ≤
      (2 * |β / 2| * opNorm H) ^ m / (m.factorial : ℝ) := by
  cases m with
  | zero => simp [shellDelta, opNorm, opToCLM]
  | succ m =>
    unfold shellDelta
    rw [opNorm_smul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast]
    have hHnn : 0 ≤ opNorm H := opNorm_nonneg H
    have had : ∀ k : ℕ, opNorm (adPowMat H k (pauliSite x α.succ)) ≤
        (2 * opNorm H) ^ k * opNorm (pauliSite x α.succ) := by
      intro k
      induction k with
      | zero => simp [adPowMat]
      | succ k ih =>
        unfold adPowMat
        have hc : opNorm (matComm H (adPowMat H k (pauliSite x α.succ))) ≤
            2 * opNorm H * opNorm (adPowMat H k (pauliSite x α.succ)) := by
          unfold matComm
          have hsub : opNorm (H * adPowMat H k (pauliSite x α.succ) - adPowMat H k (pauliSite x α.succ) * H) ≤
              opNorm (H * adPowMat H k (pauliSite x α.succ)) +
                opNorm (adPowMat H k (pauliSite x α.succ) * H) := by
            unfold opNorm
            have hclm : opToCLM (H * adPowMat H k (pauliSite x α.succ) - adPowMat H k (pauliSite x α.succ) * H) =
                opToCLM (H * adPowMat H k (pauliSite x α.succ)) -
                  opToCLM (adPowMat H k (pauliSite x α.succ) * H) := by
              ext v i; simp [opToCLM, Matrix.sub_mulVec]
            rw [hclm]; exact norm_sub_le _ _
          calc opNorm (H * adPowMat H k (pauliSite x α.succ) - adPowMat H k (pauliSite x α.succ) * H)
              ≤ opNorm (H * adPowMat H k (pauliSite x α.succ)) +
                  opNorm (adPowMat H k (pauliSite x α.succ) * H) := hsub
            _ ≤ opNorm H * opNorm (adPowMat H k (pauliSite x α.succ)) +
                  opNorm (adPowMat H k (pauliSite x α.succ)) * opNorm H :=
                add_le_add (opNorm_mul_le _ _) (opNorm_mul_le _ _)
            _ = 2 * opNorm H * opNorm (adPowMat H k (pauliSite x α.succ)) := by ring
        calc opNorm (matComm H (adPowMat H k (pauliSite x α.succ)))
            ≤ 2 * opNorm H * ((2 * opNorm H) ^ k * opNorm (pauliSite x α.succ)) :=
              le_trans hc (mul_le_mul_of_nonneg_left ih (by linarith))
          _ = (2 * opNorm H) ^ (k + 1) * opNorm (pauliSite x α.succ) := by rw [pow_succ]; ring
    have h1 := le_trans (had (m + 1)) (mul_le_mul_of_nonneg_left (opNorm_pauliSite_le x α) (pow_nonneg (by linarith) _))
    rw [mul_one] at h1
    calc |β / 2| ^ (m + 1) / ((m + 1).factorial : ℝ) * opNorm (adPowMat H (m + 1) (pauliSite x α.succ))
        ≤ |β / 2| ^ (m + 1) / ((m + 1).factorial : ℝ) * (2 * opNorm H) ^ (m + 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2 * |β / 2| * opNorm H) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
          rw [mul_pow, mul_pow, mul_pow]; ring

private lemma hasSum_cauchy_product_complex_bg {a b : ℕ → ℂ} {A B : ℂ}
    (ha : HasSum a A) (hb : HasSum b B)
    (hsa : Summable (fun k ↦ ‖a k‖)) (hsb : Summable (fun k ↦ ‖b k‖)) :
    HasSum (fun m : ℕ ↦ ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2) (A * B) := by
  have hprod_norm : Summable (fun p : ℕ × ℕ ↦ ‖a p.1 * b p.2‖) := by
    have h1 : Summable (fun p : ℕ × ℕ ↦ ‖a p.1‖ * ‖b p.2‖) :=
      Summable.mul_of_nonneg hsa hsb (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
    exact h1.congr fun p ↦ (norm_mul _ _).symm
  have hanti_norm : Summable (fun m : ℕ ↦ ‖∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2‖) := by
    have h1 : Summable (fun m : ℕ ↦ ∑ p ∈ Finset.antidiagonal m, ‖a p.1 * b p.2‖) := by
      have hfib : ∀ n : ℕ, ∑ m ∈ Finset.range n, ∑ p ∈ Finset.antidiagonal m, ‖a p.1 * b p.2‖ ≤
          ∑' p : ℕ × ℕ, ‖a p.1 * b p.2‖ := by
        intro n
        have hdisj : (Finset.range n : Set ℕ).PairwiseDisjoint Finset.antidiagonal := by
          intro i _ j _ hij
          change Disjoint (Finset.antidiagonal i) (Finset.antidiagonal j)
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          exact hij ((Finset.mem_antidiagonal.mp hp1).symm.trans (Finset.mem_antidiagonal.mp hp2))
        rw [← Finset.sum_biUnion hdisj]
        exact hprod_norm.sum_le_tsum _ fun _ _ ↦ norm_nonneg _
      exact summable_of_sum_range_le (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hfib
    exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_sum_le _ _) h1
  have hanti_summ : Summable (fun m : ℕ ↦ ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2) :=
    hanti_norm.of_norm
  suffices hlim : Filter.Tendsto
      (fun n : ℕ ↦ ∑ m ∈ Finset.range (2 * n), ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2)
      Filter.atTop (nhds (A * B)) by
    have hsubseq : Filter.Tendsto
        (fun n : ℕ ↦ ∑ m ∈ Finset.range (2 * n), ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2)
        Filter.atTop (nhds (∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2)) :=
      hanti_summ.hasSum.tendsto_sum_nat.comp
        (Filter.tendsto_atTop_mono (fun n : ℕ ↦ show id n ≤ 2 * n by dsimp; omega) Filter.tendsto_id)
    rw [← tendsto_nhds_unique hsubseq hlim]
    exact hanti_summ.hasSum
  have hsq_lim : Filter.Tendsto
      (fun n : ℕ ↦ (∑ i ∈ Finset.range n, a i) * (∑ j ∈ Finset.range n, b j))
      Filter.atTop (nhds (A * B)) :=
    ha.tendsto_sum_nat.mul hb.tendsto_sum_nat
  have hdiff_zero : Filter.Tendsto
      (fun n : ℕ ↦ (∑ m ∈ Finset.range (2 * n), ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2) -
        (∑ i ∈ Finset.range n, a i) * (∑ j ∈ Finset.range n, b j))
      Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have htail : Filter.Tendsto (fun s : Finset (ℕ × ℕ) ↦ ∑ p ∈ s, ‖a p.1 * b p.2‖)
        Filter.atTop (nhds (∑' p : ℕ × ℕ, ‖a p.1 * b p.2‖)) := hprod_norm.hasSum
    rw [Metric.tendsto_atTop] at htail
    rcases htail ε hε with ⟨S, hS⟩
    let N₀ := S.sup (fun p : ℕ × ℕ ↦ max p.1 p.2 + 1)
    refine ⟨N₀, fun n hn ↦ ?_⟩
    have hsub_S : S ⊆ Finset.range n ×ˢ Finset.range n := by
      intro p hp
      have h1 : max p.1 p.2 + 1 ≤ N₀ := Finset.le_sup (f := fun q : ℕ × ℕ ↦ max q.1 q.2 + 1) hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      omega
    let T := (Finset.range (2 * n)).biUnion Finset.antidiagonal
    have hdisj : (Finset.range (2 * n) : Set ℕ).PairwiseDisjoint Finset.antidiagonal := by
      intro i _ j _ hij
      change Disjoint (Finset.antidiagonal i) (Finset.antidiagonal j)
      rw [Finset.disjoint_left]; intro p hp1 hp2
      exact hij ((Finset.mem_antidiagonal.mp hp1).symm.trans (Finset.mem_antidiagonal.mp hp2))
    have hT_eq : ∑ m ∈ Finset.range (2 * n), ∑ p ∈ Finset.antidiagonal m, a p.1 * b p.2 =
        ∑ p ∈ T, a p.1 * b p.2 := (Finset.sum_biUnion hdisj).symm
    have hsq_eq : (∑ i ∈ Finset.range n, a i) * (∑ j ∈ Finset.range n, b j) =
        ∑ p ∈ Finset.range n ×ˢ Finset.range n, a p.1 * b p.2 := by
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
    have hsq_sub_T : Finset.range n ×ˢ Finset.range n ⊆ T := by
      intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      rw [Finset.mem_range] at hp1 hp2
      exact Finset.mem_biUnion.mpr ⟨p.1 + p.2, Finset.mem_range.mpr (by omega),
        Finset.mem_antidiagonal.mpr rfl⟩
    rw [dist_zero_right, hT_eq, hsq_eq, ← Finset.sum_sdiff hsq_sub_T]
    have hnorm_le : ‖∑ p ∈ T \ (Finset.range n ×ˢ Finset.range n), a p.1 * b p.2‖ ≤
        ∑ p ∈ T \ (Finset.range n ×ˢ Finset.range n), ‖a p.1 * b p.2‖ := norm_sum_le _ _
    have hsdiff_eq : ∑ p ∈ T \ (Finset.range n ×ˢ Finset.range n), ‖a p.1 * b p.2‖ =
        (∑ p ∈ T, ‖a p.1 * b p.2‖) - ∑ p ∈ Finset.range n ×ˢ Finset.range n, ‖a p.1 * b p.2‖ :=
      eq_sub_of_add_eq (Finset.sum_sdiff hsq_sub_T)
    have hle_tsum : ∑ p ∈ T, ‖a p.1 * b p.2‖ ≤ ∑' p : ℕ × ℕ, ‖a p.1 * b p.2‖ :=
      hprod_norm.sum_le_tsum T fun _ _ ↦ norm_nonneg _
    have hclose := hS (Finset.range n ×ˢ Finset.range n) hsub_S
    rw [Real.dist_eq, abs_lt] at hclose
    linarith
  have hadd := hdiff_zero.add hsq_lim
  simp only [zero_add, sub_add_cancel] at hadd
  exact hadd

/-- Entrywise Cauchy-product convergence:
`HasSum (fun k ↦ (M * bgShell H β k).trace.re) ((M * thermalBackgroundOp hH β).trace.re)`. -/
theorem hasSum_trace_bgShell {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (β : ℝ) (M : QubitOp N) :
    HasSum (fun k : ℕ ↦ (M * bgShell H β k).trace.re)
      ((M * thermalBackgroundOp hH β).trace.re) := by
  have hmat : HasSum (fun k : ℕ ↦ bgShell H β k) (thermalBackgroundOp hH β) := by
    unfold bgShell thermalBackgroundOp
    have hterm : ∀ (x : Fin N) (α : Fin 3),
        HasSum (fun k : ℕ ↦ ∑ m ∈ Finset.Ico 1 k,
            shellDelta (H := H) β x α m * (shellDelta (H := H) β x α (k - m))ᴴ)
          ((heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) (pauliSite x α.succ) - pauliSite x α.succ) *
           (heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) (pauliSite x α.succ) - pauliSite x α.succ)ᴴ) := by
      intro x α
      let f : ℕ → QubitOp N := shellDelta (H := H) β x α
      let Δ : QubitOp N := heisenbergEvol hH (-Complex.I * ((β / 2 : ℝ) : ℂ)) (pauliSite x α.succ) - pauliSite x α.succ
      have hf_sum : HasSum f Δ := hasSum_shellDelta hH β x α
      have hf_summ_norm : ∀ a b : QubitIdx N, Summable (fun m : ℕ ↦ ‖f m a b‖) := by
        intro a b
        refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
          (Real.summable_pow_div_factorial (2 * |β / 2| * opNorm H))
        exact le_trans (norm_entry_le_opNorm (f m) a b) (opNorm_shellDelta_le β x α m)
      have hent_has : ∀ a b : QubitIdx N, HasSum (fun m : ℕ ↦ f m a b) (Δ a b) := by
        intro a b
        let evalAB : QubitOp N →L[ℂ] ℂ :=
          LinearMap.toContinuousLinearMap
            { toFun := fun A ↦ A a b
              map_add' := fun _ _ ↦ rfl
              map_smul' := fun _ _ ↦ rfl }
        exact hf_sum.map evalAB evalAB.continuous
      change HasSum (fun k : ℕ ↦ (fun i j : QubitIdx N ↦
          (∑ m ∈ Finset.Ico 1 k, f m * (f (k - m))ᴴ) i j))
        (fun i j : QubitIdx N ↦ (Δ * Δᴴ) i j)
      rw [Pi.hasSum]; intro i; rw [Pi.hasSum]; intro j
      have hsum_c : ∀ c : QubitIdx N,
          HasSum (fun k : ℕ ↦ ∑ m ∈ Finset.range (k + 1), f m i c * star (f (k - m) j c))
            (Δ i c * star (Δ j c)) := by
        intro c
        have ha : HasSum (fun m : ℕ ↦ f m i c) (Δ i c) := hent_has i c
        have hb : HasSum (fun m : ℕ ↦ star (f m j c)) (star (Δ j c)) := (hent_has j c).star
        have ha_abs : Summable (fun m : ℕ ↦ ‖f m i c‖) := hf_summ_norm i c
        have hb_abs : Summable (fun m : ℕ ↦ ‖star (f m j c)‖) := by simpa using hf_summ_norm j c
        have hanti := hasSum_cauchy_product_complex_bg ha hb ha_abs hb_abs
        refine hanti.congr_fun fun k ↦ ?_
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun m n ↦ f m i c * star (f n j c)) k]
      have htot := hasSum_sum (s := Finset.univ) (fun c _ ↦ hsum_c c)
      refine htot.congr_fun fun k ↦ ?_
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro c _
      rw [← Finset.sum_subset (s₁ := Finset.Ico 1 k) (s₂ := Finset.range (k + 1))
        (fun m hm ↦ Finset.mem_range.mpr (by rw [Finset.mem_Ico] at hm; omega))]
      intro m hm hnot
      rw [Finset.mem_range] at hm
      by_cases hm0 : m = 0
      · subst hm0; simp [f, shellDelta]
      · have hmk : m = k := by rw [Finset.mem_Ico] at hnot; omega
        subst hmk; simp [f, shellDelta]
    have hsum_all := hasSum_sum (s := Finset.univ) fun x _ ↦
      hasSum_sum (s := Finset.univ) fun α _ ↦ hterm x α
    exact hsum_all.const_smul ((1 / 8 : ℝ) : ℂ)
  let Φ : QubitOp N →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun A ↦ (M * A).trace.re
        map_add' := fun A B ↦ by rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
        map_smul' := fun r A ↦ by
          simp only [RingHom.id_apply, smul_eq_mul]
          rw [show (r : ℝ) • A = ((r : ℝ) : ℂ) • A from rfl, Matrix.mul_smul, Matrix.trace_smul,
            smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring }
  exact hmat.map Φ Φ.continuous

private lemma supportedOn_conjTranspose_mem {N : ℕ} {U : Finset (Fin N)} {A : QubitOp N}
    (hA : A ∈ supportedOn U) : Aᴴ ∈ supportedOn U := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨a, ha, rfl⟩
    have hherm : (pauliString a)ᴴ = pauliString a := by
      unfold pauliString; rw [kronOp_conjTranspose]; congr 1; funext y; exact pauliMat_herm (a y)
    rw [hherm]
    exact pauliString_mem_supportedOn a ha
  · rw [Matrix.conjTranspose_zero]; exact (supportedOn U).zero_mem
  · intro x y _ _ hx hy; rw [Matrix.conjTranspose_add]; exact (supportedOn U).add_mem hx hy
  · intro c x _ hx; rw [Matrix.conjTranspose_smul]; exact (supportedOn U).smul_mem _ hx

private lemma subset_causalUnionOp {N : ℕ} (U : Finset (Fin N)) :
    ∀ {m : ℕ} (f : Fin m → Finset (Fin N)), U ⊆ causalUnionOp U f
  | 0, _ => by simp [causalUnionOp]
  | m + 1, f => by
    intro y hy; unfold causalUnionOp
    exact Finset.mem_union_right _ (subset_causalUnionOp U (Fin.tail f) hy)

/-- **Explicit `(1 + k(r - 1))`-Local Decomposition and Site-Strength Bound for `bgShell H β k`**:
For every `k ≥ 2`, `bgShell H β k = ∑ Z ∈ E_k, xOp_k Z` where every `Z ∈ E_k` is nonempty with
`Z.card ≤ 1 + k * (r - 1)`, `xOp_k Z ∈ supportedOn Z`, and for every site `y : Fin N`:
`∑ Z ∈ E_k.filter (y ∈ ·), opNorm (xOp_k Z) ≤ (3 / 4) * k * (k - 1) * (β * r * Jsite / 2) ^ k`. -/
theorem bgShell_local_decomp {N r : ℕ} (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hE_card : ∀ Z ∈ E, Z.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hh_supp : ∀ Z, h Z ∈ supportedOn Z)
    {Jsite : ℝ} (hJ : 0 ≤ Jsite)
    (hH_site : ∀ x : Fin N, ∑ Z ∈ E.filter (fun Z ↦ x ∈ Z), opNorm (h Z) ≤ Jsite)
    {β : ℝ} (hβ0 : 0 ≤ β) {k : ℕ} (hk : 2 ≤ k) :
    ∃ (E_k : Finset (Finset (Fin N))) (xOp_k : Finset (Fin N) → QubitOp N),
      (∀ Z ∈ E_k, Z.Nonempty ∧ Z.card ≤ 1 + k * (r - 1)) ∧
      (∀ Z, xOp_k Z ∈ supportedOn Z) ∧
      ∑ Z ∈ E_k, xOp_k Z = bgShell (∑ Z ∈ E, h Z) β k ∧
      (∀ y : Fin N, ∑ Z ∈ E_k.filter (fun Z ↦ y ∈ Z), opNorm (xOp_k Z) ≤
        (3 / 4 : ℝ) * (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (β * (r : ℝ) * Jsite) ^ k) := by
  classical
  set H := ∑ Z ∈ E, h Z
  let E_k : Finset (Finset (Fin N)) :=
    Finset.univ.filter (fun Z : Finset (Fin N) ↦ Z.Nonempty ∧ Z.card ≤ 1 + k * (r - 1))
  -- For each `m ∈ Ico 1 k`, expand `shellDelta β x α m` over causal sequences.
  let cSeq (x : Fin N) (m : ℕ) : Finset (Fin m → Finset (Fin N)) :=
    (Fintype.piFinset fun _ : Fin m ↦ E).filter (isCausalSeqOp {x})
  let coeff (m : ℕ) : ℂ := (((β / 2 : ℝ) : ℂ) ^ m / (m.factorial : ℂ))
  let pairOp (x : Fin N) (α : Fin 3) (m : ℕ)
      (f₁ : Fin m → Finset (Fin N)) (f₂ : Fin (k - m) → Finset (Fin N)) : QubitOp N :=
    ((1 / 8 : ℝ) : ℂ) • ((coeff m • iterComm h f₁ (pauliSite x α.succ)) *
      (coeff (k - m) • iterComm h f₂ (pauliSite x α.succ))ᴴ)
  let xOp_k : Finset (Fin N) → QubitOp N := fun Z ↦
    ∑ x : Fin N, ∑ α : Fin 3, ∑ m ∈ Finset.Ico 1 k,
      ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
        if causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ = Z then pairOp x α m f₁ f₂ else 0
  have hmem_Ek : ∀ (x : Fin N) (m : ℕ), m ∈ Finset.Ico 1 k →
      ∀ f₁ ∈ cSeq x m, ∀ f₂ ∈ cSeq x (k - m),
        causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ ∈ E_k := by
    intro x m hm f₁ hf₁ f₂ hf₂
    rw [Finset.mem_Ico] at hm
    have h1 : x ∈ causalUnionOp {x} f₁ := subset_causalUnionOp {x} f₁ (Finset.mem_singleton_self x)
    have h2 : x ∈ causalUnionOp {x} f₂ := subset_causalUnionOp {x} f₂ (Finset.mem_singleton_self x)
    have hcard1 : (causalUnionOp {x} f₁).card ≤ 1 + m * (r - 1) := by
      have := card_causalUnion_le (by omega : 1 ≤ r) E hE_card {x} f₁
        (fun j ↦ Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf₁).1 j)
        (Finset.mem_filter.mp hf₁).2
      simpa using this
    have hcard2 : (causalUnionOp {x} f₂).card ≤ 1 + (k - m) * (r - 1) := by
      have := card_causalUnion_le (by omega : 1 ≤ r) E hE_card {x} f₂
        (fun j ↦ Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf₂).1 j)
        (Finset.mem_filter.mp hf₂).2
      simpa using this
    have hinter : 1 ≤ (causalUnionOp {x} f₁ ∩ causalUnionOp {x} f₂).card :=
      Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨h1, h2⟩⟩
    have hunion_card := Finset.card_union_add_card_inter (causalUnionOp {x} f₁) (causalUnionOp {x} f₂)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, Finset.mem_union_left _ h1⟩, ?_⟩
    have hkm : m + (k - m) = k := by omega
    have hmul : m * (r - 1) + (k - m) * (r - 1) = k * (r - 1) := by rw [← Nat.add_mul, hkm]
    omega
  refine ⟨E_k, xOp_k, fun Z hZ ↦ (Finset.mem_filter.mp hZ).2, ?_, ?_, ?_⟩
  · -- Support check: `xOp_k Z ∈ supportedOn Z`
    intro Z
    dsimp only [xOp_k]
    refine Submodule.sum_mem _ fun x _ ↦ Submodule.sum_mem _ fun α _ ↦
      Submodule.sum_mem _ fun m _ ↦ Submodule.sum_mem _ fun f₁ _ ↦
      Submodule.sum_mem _ fun f₂ _ ↦ ?_
    split_ifs with heq
    · subst heq
      dsimp only [pairOp]
      refine (supportedOn _).smul_mem _ ?_
      have h1 : coeff m • iterComm h f₁ (pauliSite x α.succ) ∈ supportedOn (causalUnionOp {x} f₁) :=
        (supportedOn _).smul_mem _ (iterComm_mem_supportedOn h hh_supp (pauliSite_mem_supportedOn x α) f₁)
      have h2 : coeff (k - m) • iterComm h f₂ (pauliSite x α.succ) ∈ supportedOn (causalUnionOp {x} f₂) :=
        (supportedOn _).smul_mem _ (iterComm_mem_supportedOn h hh_supp (pauliSite_mem_supportedOn x α) f₂)
      have h1' : coeff m • iterComm h f₁ (pauliSite x α.succ) ∈
          supportedOn (causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂) :=
        supportedOn_mono Finset.subset_union_left h1
      have h2' : (coeff (k - m) • iterComm h f₂ (pauliSite x α.succ))ᴴ ∈
          supportedOn (causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂) :=
        supportedOn_mono Finset.subset_union_right (supportedOn_conjTranspose_mem h2)
      exact supportedOn_mul_mem h1' h2'
    · exact (supportedOn Z).zero_mem
  · -- Sum equals `bgShell H β k`
    dsimp only [xOp_k]
    rw [Finset.sum_comm]
    have hswap : ∀ x : Fin N, ∑ Z ∈ E_k, ∑ α : Fin 3, ∑ m ∈ Finset.Ico 1 k,
        ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
          (if causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ = Z then pairOp x α m f₁ f₂ else 0) =
        ∑ α : Fin 3, ∑ m ∈ Finset.Ico 1 k, ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
          pairOp x α m f₁ f₂ := by
      intro x
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro α _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro m hm
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro f₁ hf₁
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro f₂ hf₂
      rw [Finset.sum_ite_eq E_k (causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂),
        if_pos (hmem_Ek x m hm f₁ hf₁ f₂ hf₂)]
    simp_rw [hswap]
    unfold bgShell
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl; intro α _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl; intro m hm
    rw [Finset.mem_Ico] at hm
    have hm1 : 1 ≤ m := hm.1
    have hkm1 : 1 ≤ k - m := by omega
    have hd1 : shellDelta (H := H) β x α m =
        ∑ f₁ ∈ cSeq x m, coeff m • iterComm h f₁ (pauliSite x α.succ) := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      dsimp only [shellDelta, coeff, H]
      rw [adPowMat_eq_sum_causal E h hh_supp (pauliSite_mem_supportedOn x α) (m' + 1), Finset.smul_sum]
    have hd2 : shellDelta (H := H) β x α (k - m) =
        ∑ f₂ ∈ cSeq x (k - m), coeff (k - m) • iterComm h f₂ (pauliSite x α.succ) := by
      obtain ⟨m', hm'⟩ : ∃ m', k - m = m' + 1 := ⟨k - m - 1, by omega⟩
      rw [hm']
      dsimp only [shellDelta, coeff, H]
      rw [adPowMat_eq_sum_causal E h hh_supp (pauliSite_mem_supportedOn x α) (m' + 1), Finset.smul_sum]
    rw [hd1, hd2, Matrix.conjTranspose_sum, Finset.sum_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl; intro f₁ _
    rw [Finset.mul_sum, Finset.smul_sum]
  · -- Site-strength bound for every `y : Fin N`
    intro y
    have hnorm_pair : ∀ (x : Fin N) (α : Fin 3) (m : ℕ), m ≤ k →
        ∀ (f₁ : Fin m → Finset (Fin N)) (f₂ : Fin (k - m) → Finset (Fin N)),
        opNorm (pairOp x α m f₁ f₂) ≤
          (1 / 8 : ℝ) * (β ^ k / ((m.factorial : ℝ) * ((k - m).factorial : ℝ))) *
            (∏ j : Fin m, opNorm (h (f₁ j))) * (∏ j : Fin (k - m), opNorm (h (f₂ j))) := by
      intro x α m hmk f₁ f₂
      dsimp only [pairOp, coeff]
      rw [opNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      have hmul := opNorm_mul_le
        (((((β / 2 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) • iterComm h f₁ (pauliSite x α.succ)))
        (((((β / 2 : ℝ) : ℂ) ^ (k - m) / ((k - m).factorial : ℂ)) • iterComm h f₂ (pauliSite x α.succ))ᴴ)
      have hprod1_nn : 0 ≤ ∏ j : Fin m, opNorm (h (f₁ j)) := Finset.prod_nonneg fun _ _ ↦ opNorm_nonneg _
      have hprod2_nn : 0 ≤ ∏ j : Fin (k - m), opNorm (h (f₂ j)) := Finset.prod_nonneg fun _ _ ↦ opNorm_nonneg _
      have h1 : opNorm (((((β / 2 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) • iterComm h f₁ (pauliSite x α.succ))) ≤
          β ^ m / (m.factorial : ℝ) * ∏ j : Fin m, opNorm (h (f₁ j)) := by
        rw [opNorm_smul, norm_div, norm_pow,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ β / 2),
          Complex.norm_natCast]
        have hic := le_trans (opNorm_iterComm_le h (pauliSite x α.succ) f₁)
          (mul_le_mul_of_nonneg_left (opNorm_pauliSite_le x α) (mul_nonneg (pow_nonneg (by norm_num) _) hprod1_nn))
        rw [mul_one] at hic
        calc (β / 2) ^ m / (m.factorial : ℝ) * opNorm (iterComm h f₁ (pauliSite x α.succ))
            ≤ (β / 2) ^ m / (m.factorial : ℝ) * ((2 : ℝ) ^ m * ∏ j : Fin m, opNorm (h (f₁ j))) :=
              mul_le_mul_of_nonneg_left hic (by positivity)
          _ = β ^ m / (m.factorial : ℝ) * ∏ j : Fin m, opNorm (h (f₁ j)) := by
              have h2 : (β / 2) ^ m * (2 : ℝ) ^ m = β ^ m := by rw [← mul_pow]; congr 1; ring
              calc (β / 2) ^ m / (m.factorial : ℝ) * ((2 : ℝ) ^ m * ∏ j : Fin m, opNorm (h (f₁ j)))
                  = ((β / 2) ^ m * (2 : ℝ) ^ m) / (m.factorial : ℝ) * ∏ j : Fin m, opNorm (h (f₁ j)) := by ring
                _ = β ^ m / (m.factorial : ℝ) * ∏ j : Fin m, opNorm (h (f₁ j)) := by rw [h2]
      have h2 : opNorm (((((β / 2 : ℝ) : ℂ) ^ (k - m) / ((k - m).factorial : ℂ)) • iterComm h f₂ (pauliSite x α.succ))ᴴ) ≤
          β ^ (k - m) / ((k - m).factorial : ℝ) * ∏ j : Fin (k - m), opNorm (h (f₂ j)) := by
        rw [opNorm_conjTranspose, opNorm_smul, norm_div, norm_pow,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ β / 2),
          Complex.norm_natCast]
        have hic := le_trans (opNorm_iterComm_le h (pauliSite x α.succ) f₂)
          (mul_le_mul_of_nonneg_left (opNorm_pauliSite_le x α) (mul_nonneg (pow_nonneg (by norm_num) _) hprod2_nn))
        rw [mul_one] at hic
        calc (β / 2) ^ (k - m) / ((k - m).factorial : ℝ) * opNorm (iterComm h f₂ (pauliSite x α.succ))
            ≤ (β / 2) ^ (k - m) / ((k - m).factorial : ℝ) * ((2 : ℝ) ^ (k - m) * ∏ j : Fin (k - m), opNorm (h (f₂ j))) :=
              mul_le_mul_of_nonneg_left hic (by positivity)
          _ = β ^ (k - m) / ((k - m).factorial : ℝ) * ∏ j : Fin (k - m), opNorm (h (f₂ j)) := by
              have h2 : (β / 2) ^ (k - m) * (2 : ℝ) ^ (k - m) = β ^ (k - m) := by
                rw [← mul_pow]; congr 1; ring
              calc (β / 2) ^ (k - m) / ((k - m).factorial : ℝ) * ((2 : ℝ) ^ (k - m) * ∏ j : Fin (k - m), opNorm (h (f₂ j)))
                  = ((β / 2) ^ (k - m) * (2 : ℝ) ^ (k - m)) / ((k - m).factorial : ℝ) *
                      ∏ j : Fin (k - m), opNorm (h (f₂ j)) := by ring
                _ = β ^ (k - m) / ((k - m).factorial : ℝ) * ∏ j : Fin (k - m), opNorm (h (f₂ j)) := by rw [h2]
      have h1_nn : 0 ≤ β ^ m / (m.factorial : ℝ) * ∏ j : Fin m, opNorm (h (f₁ j)) :=
        mul_nonneg (by positivity) hprod1_nn
      have hprod := le_trans hmul (mul_le_mul h1 h2 (opNorm_nonneg _) h1_nn)
      have hpow : β ^ m * β ^ (k - m) = β ^ k := by
        rw [← pow_add, Nat.add_sub_of_le hmk]
      calc (1 / 8 : ℝ) * opNorm (((((β / 2 : ℝ) : ℂ) ^ m / (m.factorial : ℂ)) • iterComm h f₁ (pauliSite x α.succ)) *
            ((((β / 2 : ℝ) : ℂ) ^ (k - m) / ((k - m).factorial : ℂ)) • iterComm h f₂ (pauliSite x α.succ))ᴴ)
          ≤ (1 / 8 : ℝ) * ((β ^ m / (m.factorial : ℝ) * ∏ j : Fin m, opNorm (h (f₁ j))) *
              (β ^ (k - m) / ((k - m).factorial : ℝ) * ∏ j : Fin (k - m), opNorm (h (f₂ j)))) :=
            mul_le_mul_of_nonneg_left hprod (by norm_num)
        _ = (1 / 8 : ℝ) * ((β ^ m * β ^ (k - m)) / ((m.factorial : ℝ) * ((k - m).factorial : ℝ))) *
              (∏ j : Fin m, opNorm (h (f₁ j))) * (∏ j : Fin (k - m), opNorm (h (f₂ j))) := by ring
        _ = (1 / 8 : ℝ) * (β ^ k / ((m.factorial : ℝ) * ((k - m).factorial : ℝ))) *
              (∏ j : Fin m, opNorm (h (f₁ j))) * (∏ j : Fin (k - m), opNorm (h (f₂ j))) := by rw [hpow]
    -- Bound `∑ Z ∈ E_k.filter (y ∈ ·), opNorm (xOp_k Z)` by pulling triangle inequality inside and collapsing `Z`.
    have hstep1 : ∑ Z ∈ E_k.filter (fun Z ↦ y ∈ Z), opNorm (xOp_k Z) ≤
        ∑ m ∈ Finset.Ico 1 k, ∑ α : Fin 3, ∑ x : Fin N,
          ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
            if y ∈ causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ then opNorm (pairOp x α m f₁ f₂) else 0 := by
      have htri : ∀ Z ∈ E_k.filter (fun Z ↦ y ∈ Z),
          opNorm (xOp_k Z) ≤ ∑ x : Fin N, ∑ α : Fin 3, ∑ m ∈ Finset.Ico 1 k,
            ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
              if causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ = Z then opNorm (pairOp x α m f₁ f₂) else 0 := by
        intro Z _
        dsimp only [xOp_k]
        refine le_trans (opNorm_sum_le _ _) (Finset.sum_le_sum fun x _ ↦ ?_)
        refine le_trans (opNorm_sum_le _ _) (Finset.sum_le_sum fun α _ ↦ ?_)
        refine le_trans (opNorm_sum_le _ _) (Finset.sum_le_sum fun m _ ↦ ?_)
        refine le_trans (opNorm_sum_le _ _) (Finset.sum_le_sum fun f₁ _ ↦ ?_)
        refine le_trans (opNorm_sum_le _ _) (Finset.sum_le_sum fun f₂ _ ↦ ?_)
        split_ifs
        · exact le_rfl
        · simp [opNorm, opToCLM]
      refine le_trans (Finset.sum_le_sum htri) ?_
      -- Swap `Z` all the way inside and collapse `∑ Z ∈ E_k.filter (y ∈ ·), if U = Z then ... else 0`.
      rw [Finset.sum_comm]
      have hcollapse : ∀ x : Fin N,
          ∑ Z ∈ E_k.filter (fun Z ↦ y ∈ Z), ∑ α : Fin 3, ∑ m ∈ Finset.Ico 1 k,
            ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
              (if causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ = Z then opNorm (pairOp x α m f₁ f₂) else 0) =
          ∑ α : Fin 3, ∑ m ∈ Finset.Ico 1 k, ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
            if y ∈ causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ then opNorm (pairOp x α m f₁ f₂) else 0 := by
        intro x
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro α _
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro m hm
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro f₁ hf₁
        rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro f₂ hf₂
        rw [Finset.sum_ite_eq (E_k.filter (fun Z ↦ y ∈ Z)) (causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂)]
        simp only [Finset.mem_filter, hmem_Ek x m hm f₁ hf₁ f₂ hf₂, true_and]
      simp_rw [hcollapse]
      rw [Finset.sum_comm]
      have hswap2 : (∑ α : Fin 3, ∑ x : Fin N, ∑ m ∈ Finset.Ico 1 k,
            ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
              if y ∈ causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ then opNorm (pairOp x α m f₁ f₂) else 0) =
          ∑ m ∈ Finset.Ico 1 k, ∑ α : Fin 3, ∑ x : Fin N,
            ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
              if y ∈ causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ then opNorm (pairOp x α m f₁ f₂) else 0 := by
        calc _ = ∑ α : Fin 3, ∑ m ∈ Finset.Ico 1 k, ∑ x : Fin N,
              ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
                if y ∈ causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ then opNorm (pairOp x α m f₁ f₂) else 0 := by
              apply Finset.sum_congr rfl; intro α _; exact Finset.sum_comm
          _ = _ := Finset.sum_comm
      rw [hswap2]
    -- Bound each `m ∈ Ico 1 k` using `fwdCausalSum_r_minus_1_le` and `revCausalSum_le`!
    have hfwd_bound : ∀ (n : ℕ) (x : Fin N),
        fwdCausalSum E (fun Z ↦ opNorm (h Z)) n {x} ≤ (n.factorial : ℝ) * ((r : ℝ) * Jsite) ^ n := by
      intro n x
      have hf := fwdCausalSum_r_minus_1_le (by omega : 1 ≤ r) E hE_card
        (fun Z ↦ opNorm (h Z)) (fun _ _ ↦ opNorm_nonneg _) hJ hH_site n {x}
      have hprod : ∏ j ∈ Finset.range n, (((({x} : Finset (Fin N)).card : ℝ) + (j : ℝ) * ((r - 1 : ℕ) : ℝ))) ≤
          (n.factorial : ℝ) * (r : ℝ) ^ n := by
        have hterm_le : ∀ j : ℕ,
            ((({x} : Finset (Fin N)).card : ℝ) + (j : ℝ) * ((r - 1 : ℕ) : ℝ)) ≤ ((j + 1 : ℕ) : ℝ) * (r : ℝ) := by
          intro j
          have hr1 : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.sub_le r 1
          have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
          simp only [Finset.card_singleton, Nat.cast_one, Nat.cast_add]
          nlinarith [Nat.cast_nonneg (α := ℝ) j]
        have haux : ∀ m : ℕ, ∏ j ∈ Finset.range m, ((1 : ℝ) + (j : ℝ) * ((r - 1 : ℕ) : ℝ)) ≤
            (m.factorial : ℝ) * (r : ℝ) ^ m := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul, pow_succ]
            have hstep_m : (1 : ℝ) + (m : ℝ) * ((r - 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (r : ℝ) := by
              simpa using hterm_le m
            have h1 := mul_le_mul ihm hstep_m (by positivity) (by positivity)
            linarith [show (m.factorial : ℝ) * (r : ℝ) ^ m * (((m + 1 : ℕ) : ℝ) * (r : ℝ)) =
              ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) * ((r : ℝ) ^ m * (r : ℝ)) by ring]
        simpa using haux n
      calc fwdCausalSum E (fun Z ↦ opNorm (h Z)) n {x}
          ≤ (∏ j ∈ Finset.range n, ((({x} : Finset (Fin N)).card : ℝ) + (j : ℝ) * ((r - 1 : ℕ) : ℝ))) * Jsite ^ n := hf
        _ ≤ ((n.factorial : ℝ) * (r : ℝ) ^ n) * Jsite ^ n := mul_le_mul_of_nonneg_right hprod (pow_nonneg hJ n)
        _ = (n.factorial : ℝ) * ((r : ℝ) * Jsite) ^ n := by rw [mul_pow]; ring
    have hm_bound : ∀ m ∈ Finset.Ico 1 k,
        (∑ α : Fin 3, ∑ x : Fin N, ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
          if y ∈ causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ then opNorm (pairOp x α m f₁ f₂) else 0) ≤
        (3 / 4 : ℝ) * (k : ℝ) * (β * (r : ℝ) * Jsite) ^ k := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      set w : Finset (Fin N) → ℝ := fun Z ↦ opNorm (h Z)
      set fac : ℝ := (1 / 8 : ℝ) * (β ^ k / ((m.factorial : ℝ) * ((k - m).factorial : ℝ)))
      have hfac_nn : 0 ≤ fac := by dsimp only [fac]; positivity
      have hper_α : ∀ α : Fin 3,
          (∑ x : Fin N, ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
            if y ∈ causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ then opNorm (pairOp x α m f₁ f₂) else 0) ≤
          fac * (((m + 1).factorial : ℝ) * ((k - m).factorial : ℝ) * ((r : ℝ) * Jsite) ^ k +
                 ((k - m + 1).factorial : ℝ) * (m.factorial : ℝ) * ((r : ℝ) * Jsite) ^ k) := by
        intro α
        have hsplit_y : ∀ (x : Fin N) (f₁ : Fin m → Finset (Fin N)) (f₂ : Fin (k - m) → Finset (Fin N)),
            (if y ∈ causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ then opNorm (pairOp x α m f₁ f₂) else 0) ≤
            fac * ((if y ∈ causalUnionOp {x} f₁ then (∏ j, w (f₁ j)) * (∏ j, w (f₂ j)) else 0) +
                   (if y ∈ causalUnionOp {x} f₂ then (∏ j, w (f₁ j)) * (∏ j, w (f₂ j)) else 0)) := by
          intro x f₁ f₂
          have hp : opNorm (pairOp x α m f₁ f₂) ≤ fac * ((∏ j : Fin m, w (f₁ j)) * (∏ j : Fin (k - m), w (f₂ j))) := by
            simpa only [fac, w, mul_assoc] using hnorm_pair x α m hm.2.le f₁ f₂
          have hwn : 0 ≤ (∏ j : Fin m, w (f₁ j)) * (∏ j : Fin (k - m), w (f₂ j)) :=
            mul_nonneg (Finset.prod_nonneg fun _ _ ↦ opNorm_nonneg _) (Finset.prod_nonneg fun _ _ ↦ opNorm_nonneg _)
          by_cases h1 : y ∈ causalUnionOp {x} f₁ <;> by_cases h2 : y ∈ causalUnionOp {x} f₂
          · simp only [Finset.mem_union, h1, h2, or_self, ↓reduceIte]; nlinarith
          · simp only [Finset.mem_union, h1, h2, or_false, ↓reduceIte, add_zero]; linarith
          · simp only [Finset.mem_union, h1, h2, false_or, ↓reduceIte, zero_add]; linarith
          · simp only [Finset.mem_union, h1, h2, or_self, ↓reduceIte, add_zero, mul_zero]; exact le_rfl
        have hle1 :
            (∑ x : Fin N, ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
              if y ∈ causalUnionOp {x} f₁ ∪ causalUnionOp {x} f₂ then opNorm (pairOp x α m f₁ f₂) else 0) ≤
            ∑ x : Fin N, ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
              fac * ((if y ∈ causalUnionOp {x} f₁ then (∏ j, w (f₁ j)) * (∏ j, w (f₂ j)) else 0) +
                     (if y ∈ causalUnionOp {x} f₂ then (∏ j, w (f₁ j)) * (∏ j, w (f₂ j)) else 0)) :=
          Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun f₁ _ ↦
            Finset.sum_le_sum fun f₂ _ ↦ hsplit_y x f₁ f₂
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hle1
        rw [← mul_add] at hle1
        have hA : (∑ x : Fin N, ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
              if y ∈ causalUnionOp {x} f₁ then (∏ j, w (f₁ j)) * (∏ j, w (f₂ j)) else 0) ≤
            ((m + 1).factorial : ℝ) * ((k - m).factorial : ℝ) * ((r : ℝ) * Jsite) ^ k := by
          have hrew : (∑ x : Fin N, ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
                if y ∈ causalUnionOp {x} f₁ then (∏ j, w (f₁ j)) * (∏ j, w (f₂ j)) else 0) =
              ∑ x : Fin N, (∑ f₁ ∈ (cSeq x m).filter (fun f₁ ↦ y ∈ causalUnionOp {x} f₁), ∏ j, w (f₁ j)) *
                fwdCausalSum E w (k - m) {x} := by
            apply Finset.sum_congr rfl; intro x _
            have hinner : ∀ f₁ ∈ cSeq x m,
                (∑ f₂ ∈ cSeq x (k - m), if y ∈ causalUnionOp {x} f₁ then (∏ j, w (f₁ j)) * ∏ j, w (f₂ j) else 0) =
                if y ∈ causalUnionOp {x} f₁ then (∏ j, w (f₁ j)) * fwdCausalSum E w (k - m) {x} else 0 := by
              intro f₁ _
              by_cases h1 : y ∈ causalUnionOp {x} f₁
              · simp only [h1, ↓reduceIte, ← Finset.mul_sum]; rfl
              · simp only [h1, ↓reduceIte, Finset.sum_const_zero]
            rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_mul]
          rw [hrew]
          have h1 : ∑ x : Fin N, (∑ f₁ ∈ (cSeq x m).filter (fun f₁ ↦ y ∈ causalUnionOp {x} f₁), ∏ j, w (f₁ j)) *
                fwdCausalSum E w (k - m) {x} ≤
              ∑ x : Fin N, (∑ f₁ ∈ (cSeq x m).filter (fun f₁ ↦ y ∈ causalUnionOp {x} f₁), ∏ j, w (f₁ j)) *
                (((k - m).factorial : ℝ) * ((r : ℝ) * Jsite) ^ (k - m)) := by
            apply Finset.sum_le_sum; intro x _
            exact mul_le_mul_of_nonneg_left (hfwd_bound (k - m) x)
              (Finset.sum_nonneg fun _ _ ↦ Finset.prod_nonneg fun _ _ ↦ opNorm_nonneg _)
          rw [← Finset.sum_mul] at h1
          have hrev := revCausalSum_le (by omega : 1 ≤ r) E hE_card w (fun _ _ ↦ opNorm_nonneg _)
            hJ hH_site m y
          have hpow : ((r : ℝ) * Jsite) ^ m * ((r : ℝ) * Jsite) ^ (k - m) = ((r : ℝ) * Jsite) ^ k := by
            rw [← pow_add, Nat.add_sub_of_le hm.2.le]
          calc _ ≤ (((m + 1).factorial : ℝ) * ((r : ℝ) * Jsite) ^ m) *
                  (((k - m).factorial : ℝ) * ((r : ℝ) * Jsite) ^ (k - m)) :=
                le_trans h1 (mul_le_mul_of_nonneg_right hrev (by positivity))
            _ = ((m + 1).factorial : ℝ) * ((k - m).factorial : ℝ) *
                  (((r : ℝ) * Jsite) ^ m * ((r : ℝ) * Jsite) ^ (k - m)) := by ring
            _ = ((m + 1).factorial : ℝ) * ((k - m).factorial : ℝ) * ((r : ℝ) * Jsite) ^ k := by rw [hpow]
        have hB : (∑ x : Fin N, ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
              if y ∈ causalUnionOp {x} f₂ then (∏ j, w (f₁ j)) * (∏ j, w (f₂ j)) else 0) ≤
            ((k - m + 1).factorial : ℝ) * (m.factorial : ℝ) * ((r : ℝ) * Jsite) ^ k := by
          have hrew : (∑ x : Fin N, ∑ f₁ ∈ cSeq x m, ∑ f₂ ∈ cSeq x (k - m),
                if y ∈ causalUnionOp {x} f₂ then (∏ j, w (f₁ j)) * (∏ j, w (f₂ j)) else 0) =
              ∑ x : Fin N, fwdCausalSum E w m {x} *
                (∑ f₂ ∈ (cSeq x (k - m)).filter (fun f₂ ↦ y ∈ causalUnionOp {x} f₂), ∏ j, w (f₂ j)) := by
            apply Finset.sum_congr rfl; intro x _
            have hinner : ∀ f₁ ∈ cSeq x m,
                (∑ f₂ ∈ cSeq x (k - m), if y ∈ causalUnionOp {x} f₂ then (∏ j, w (f₁ j)) * ∏ j, w (f₂ j) else 0) =
                (∏ j, w (f₁ j)) * ∑ f₂ ∈ (cSeq x (k - m)).filter (fun f₂ ↦ y ∈ causalUnionOp {x} f₂), ∏ j, w (f₂ j) := by
              intro f₁ _
              rw [Finset.mul_sum, Finset.sum_filter]
              apply Finset.sum_congr rfl; intro f₂ _
              split_ifs <;> ring
            rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]; rfl
          rw [hrew]
          have h1 : ∑ x : Fin N, fwdCausalSum E w m {x} *
                (∑ f₂ ∈ (cSeq x (k - m)).filter (fun f₂ ↦ y ∈ causalUnionOp {x} f₂), ∏ j, w (f₂ j)) ≤
              ∑ x : Fin N, ((m.factorial : ℝ) * ((r : ℝ) * Jsite) ^ m) *
                (∑ f₂ ∈ (cSeq x (k - m)).filter (fun f₂ ↦ y ∈ causalUnionOp {x} f₂), ∏ j, w (f₂ j)) := by
            apply Finset.sum_le_sum; intro x _
            exact mul_le_mul_of_nonneg_right (hfwd_bound m x)
              (Finset.sum_nonneg fun _ _ ↦ Finset.prod_nonneg fun _ _ ↦ opNorm_nonneg _)
          rw [← Finset.mul_sum] at h1
          have hrev := revCausalSum_le (by omega : 1 ≤ r) E hE_card w (fun _ _ ↦ opNorm_nonneg _)
            hJ hH_site (k - m) y
          have hpow : ((r : ℝ) * Jsite) ^ m * ((r : ℝ) * Jsite) ^ (k - m) = ((r : ℝ) * Jsite) ^ k := by
            rw [← pow_add, Nat.add_sub_of_le hm.2.le]
          calc _ ≤ ((m.factorial : ℝ) * ((r : ℝ) * Jsite) ^ m) *
                  (((k - m + 1).factorial : ℝ) * ((r : ℝ) * Jsite) ^ (k - m)) :=
                le_trans h1 (mul_le_mul_of_nonneg_left hrev (by positivity))
            _ = ((k - m + 1).factorial : ℝ) * (m.factorial : ℝ) *
                  (((r : ℝ) * Jsite) ^ m * ((r : ℝ) * Jsite) ^ (k - m)) := by ring
            _ = ((k - m + 1).factorial : ℝ) * (m.factorial : ℝ) * ((r : ℝ) * Jsite) ^ k := by rw [hpow]
        exact le_trans hle1 (mul_le_mul_of_nonneg_left (add_le_add hA hB) hfac_nn)
      have hsum3 := Finset.sum_le_sum fun α (_ : α ∈ Finset.univ) ↦ hper_α α
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum3
      refine le_trans hsum3 ?_
      have hmf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
      have hkmf : (0 : ℝ) < ((k - m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k - m)
      have hfac1 : ((m + 1).factorial : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
      have hfac2 : ((k - m + 1).factorial : ℝ) = ((k - m + 1 : ℕ) : ℝ) * ((k - m).factorial : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
      have hsum_m : ((m + 1 : ℕ) : ℝ) + ((k - m + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
        have : m + 1 + (k - m + 1) ≤ 2 * k := by omega
        exact_mod_cast this
      have hpow_comb : β ^ k * ((r : ℝ) * Jsite) ^ k = (β * (r : ℝ) * Jsite) ^ k := by
        rw [← mul_pow]; congr 1; ring
      dsimp only [fac]
      rw [hfac1, hfac2, Nat.cast_ofNat]
      have halg : (3 : ℝ) * ((1 / 8 : ℝ) * (β ^ k / ((m.factorial : ℝ) * ((k - m).factorial : ℝ))) *
          (((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) * ((k - m).factorial : ℝ) * ((r : ℝ) * Jsite) ^ k +
           ((k - m + 1 : ℕ) : ℝ) * ((k - m).factorial : ℝ) * (m.factorial : ℝ) * ((r : ℝ) * Jsite) ^ k)) =
          (3 / 8 : ℝ) * (((m + 1 : ℕ) : ℝ) + ((k - m + 1 : ℕ) : ℝ)) * (β * (r : ℝ) * Jsite) ^ k := by
        rw [← hpow_comb]; field_simp [hmf.ne', hkmf.ne']
      rw [halg]
      nlinarith [pow_nonneg (by positivity : 0 ≤ β * (r : ℝ) * Jsite) k]
    refine le_trans hstep1 (le_trans (Finset.sum_le_sum hm_bound) ?_)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    ring_nf; exact le_rfl

/-- Explicit constant `bgShellBoundConst β r Jsite` for the summed thermal background shell
series `∑' k ≥ 2, (1 / Λ₀'(k))` and `opNorm (thermalBackgroundOp hH β) / N`. -/
noncomputable def bgDecouplingC2 (r s₀ : ℕ) (C_O : ℝ) : ℝ :=
  4 * Real.sqrt 2 * (2 * Real.log (C_O * (2 : ℝ) ^ (s₀ + 1)) + 1) * (12 * Real.exp 1 * (r : ℝ))

set_option maxHeartbeats 800000 in
/-- **Proposition 6.4(2) (Unconditional Concrete High-Temperature Entropic Background Decoupling,
Eq. 6.7 — Zero `hcum` Hypothesis)**:
For any `N ≥ 1`, `r`-local Hermitian Hamiltonian `H = ∑ Z ∈ E, h Z` (`r ≥ 2`, site strength
`≤ Jsite`), `β ∈ [0, highTempBetaWC r Jsite]`, and `s₀`-local Hermitian observable `O` with
`gibbsWightmanNormSq G O = 1` and `opNorm O ≤ C_O` (`1 ≤ C_O`), for ALL `t : ℝ`:
1. `|shiftedThermalSizeIII hH β (heisenbergEvol hH (t : ℂ) O)| ≤ bgDecouplingC2 r s₀ C_O * √N`,
2. `((G.ρβ * thermalBackgroundOp hH β).trace).re ≤ N`,
3. **Eq. (6.7)**:
   `mssThermalSize G (heisenbergEvol hH (t : ℂ) O) ≤
     otocI hH β (heisenbergEvol hH (t : ℂ) O) +
     2 * √(otocI hH β (heisenbergEvol hH (t : ℂ) O)) * √(N + bgDecouplingC2 r s₀ C_O * √N) +
     bgDecouplingC2 r s₀ C_O * √N`. -/
theorem prop_6_4_part2_unconditional {N r s₀ : ℕ}
    (hN : 1 ≤ N) (hr : 2 ≤ r)
    (E : Finset (Finset (Fin N))) (hE_ne : ∀ Z ∈ E, Z.Nonempty) (hE_card : ∀ Z ∈ E, Z.card ≤ r)
    (h : Finset (Fin N) → QubitOp N) (hh_supp : ∀ Z, h Z ∈ supportedOn Z)
    (hH : (∑ Z ∈ E, h Z).IsHermitian)
    {Jsite : ℝ} (hJ : 0 < Jsite)
    (hH_site : ∀ x : Fin N, ∑ Z ∈ E.filter (fun Z ↦ x ∈ Z), opNorm (h Z) ≤ Jsite)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ highTempBetaWC r Jsite)
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
  have h6r : (36 : ℝ) ≤ (6 : ℝ) ^ r := by
    calc (36 : ℝ) = (6 : ℝ) ^ 2 := by norm_num
      _ ≤ (6 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr
  have hβ_cum : β ≤ 1 / (8 * Real.exp 2 * (r : ℝ) * Jsite) := by
    refine le_trans hβ ?_
    unfold highTempBetaWC
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hmul : (8 : ℝ) ≤ 4 * (6 : ℝ) ^ r := by linarith
    have hpos_f : 0 < Real.exp 2 * (r : ℝ) * Jsite := by positivity
    nlinarith
  have hβ_q : β * Real.exp 1 * (r : ℝ) * Jsite ≤ 1 / 288 := by
    have h1 : β * (4 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r * Jsite) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hβ (by positivity : 0 ≤ 4 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r * Jsite)
      unfold highTempBetaWC at this
      rwa [one_div_mul_cancel (by positivity)] at this
    have he1_gt2 : (2 : ℝ) < Real.exp 1 := by
      have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0); linarith
    have he2_eq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h2 : 288 * (β * Real.exp 1 * (r : ℝ) * Jsite) ≤
        β * (4 * Real.exp 2 * (r : ℝ) * (6 : ℝ) ^ r * Jsite) := by
      rw [he2_eq]
      have hprod : (288 : ℝ) * Real.exp 1 ≤ 4 * (Real.exp 1 * Real.exp 1) * (6 : ℝ) ^ r := by
        have hstep1 : (288 : ℝ) ≤ 4 * Real.exp 1 * (6 : ℝ) ^ r := by nlinarith
        nlinarith [Real.exp_pos 1]
      have hnn : 0 ≤ β * (r : ℝ) * Jsite := by positivity
      calc 288 * (β * Real.exp 1 * (r : ℝ) * Jsite)
          = (288 * Real.exp 1) * (β * (r : ℝ) * Jsite) := by ring
        _ ≤ (4 * (Real.exp 1 * Real.exp 1) * (6 : ℝ) ^ r) * (β * (r : ℝ) * Jsite) :=
            mul_le_mul_of_nonneg_right hprod hnn
        _ = β * (4 * (Real.exp 1 * Real.exp 1) * (r : ℝ) * (6 : ℝ) ^ r * Jsite) := by ring
    linarith
  -- Step 1: Bound `gibbsRelEntropy (rhoO_op hH β O) hH β ≤ 2 * Real.log (C_O * 2 ^ (s₀ + 1))`.
  have hD_le : gibbsRelEntropy (rhoO_op_isHermitian hH β O) hH β ≤
      2 * Real.log (C_O * (2 : ℝ) ^ (s₀ + 1)) := by
    have hrel := rhoO_op_relEntropy_le_two_log_opNorm hH β O hOnorm
    -- Bound `opNorm (heisenbergEvol hH (I * β / 4) O) ≤ C_O * 2 ^ (s₀ + 1)` via `heisenbergEvol_concrete_norm_bound`.
    have hz_small : 2 * ‖Complex.I * ((β / 4 : ℝ) : ℂ)‖ * (r : ℝ) * Jsite ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ β / 4)]
      have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith [hβ_q]
    have hbd := heisenbergEvol_concrete_norm_bound (by omega : 1 ≤ r) E hE_card h hh_supp hH hJ.le
      hH_site hO_supp (Complex.I * ((β / 4 : ℝ) : ℂ)) (by linarith)
    set q := 2 * ‖Complex.I * ((β / 4 : ℝ) : ℂ)‖ * (r : ℝ) * Jsite
    have hq_nn : 0 ≤ q := by dsimp only [q]; positivity
    -- `∑' k, (k + p).choose p * (1/2)^k = 2^(p + 1)` (bound termwise by `(2^k * 2^p) * ...`? Better:
    -- `(k + p).choose p ≤ 2^(k + p)` and `q ≤ 1/4` gives `∑ (k+p).choose p * q^k ≤ 2^p * ∑ (1/2)^k = 2^(p+1)`!)
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
      -- Since `gibbsWightmanNormSq G O = 1`, `O ≠ 0`, so `heisenbergEvol ... O ≠ 0`!
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
  -- Step 2: Bound each shell `k ≥ 2` and sum!
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
          (if 2 ≤ k then ((k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k) else 0) := by
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
            12 * Real.exp 1 * (r : ℝ) * ((k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k) := by
          rw [one_div_one_div]
          have hkm1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
          have hqpow : (Real.exp 1) ^ k * (β * (r : ℝ) * Jsite) ^ k ≤ (1 / 288 : ℝ) ^ k := by
            rw [← mul_pow]
            refine pow_le_pow_left₀ (by positivity) ?_ k
            linarith [hβ_q]
          calc 16 * (kr : ℝ) * Real.exp (1 + (kr : ℝ) / (r : ℝ)) * g_k
              ≤ 16 * ((k : ℝ) * (r : ℝ)) * (Real.exp 1 * (Real.exp 1) ^ k) * g_k := by gcongr
            _ = 12 * Real.exp 1 * (r : ℝ) * ((k : ℝ) ^ 2 * ((k - 1 : ℕ) : ℝ)) *
                  ((Real.exp 1) ^ k * (β * (r : ℝ) * Jsite) ^ k) := by dsimp only [g_k]; ring
            _ ≤ 12 * Real.exp 1 * (r : ℝ) * ((k : ℝ) ^ 2 * (k : ℝ)) * (1 / 288 : ℝ) ^ k := by gcongr
            _ = 12 * Real.exp 1 * (r : ℝ) * ((k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k) := by ring
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
                (12 * Real.exp 1 * (r : ℝ) * ((k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k)) * Real.sqrt (N : ℝ) := by
              have hnn1 : 0 ≤ gibbsRelEntropy (rhoO_op_isHermitian hH β O) hH β + 1 := by
                linarith [gibbsRelEntropy_nonneg_psd (rhoO_op_isHermitian hH β O) hH
                  (rhoO_op_eigenvalues_nonneg hH β O) hrho_tr β]
              gcongr
          _ = (4 * Real.sqrt 2 * D_bd * (12 * Real.exp 1 * (r : ℝ))) * Real.sqrt (N : ℝ) *
                ((k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k) := by ring
    · rw [if_neg hk, mul_zero]
      have hk01 : k = 0 ∨ k = 1 := by omega
      rcases hk01 with rfl | rfl
      · simp [bgShell_zero]
      · simp [bgShell_one]
  -- Step 3: Elementary geometric tail bound `∑' k ≥ 2, k^3 * (1/288)^k ≤ 1`.
  have hgeom_le1 : Summable (fun k : ℕ ↦ if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k else 0) ∧
      (∑' k : ℕ, if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k else 0) ≤ 1 := by
    have hdom : ∀ k : ℕ, (if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k else 0) ≤ (1 / 2 : ℝ) ^ k / 4 := by
      intro k
      split_ifs with hk
      · -- `k^3 ≤ 8^k` for all `k` (in fact `k ≤ 2^k` so `k^3 ≤ 8^k`), hence `k^3 * (1/288)^k ≤ (8/288)^k = (1/36)^k ≤ (1/2)^k / 4`!
        have hk2 : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast Nat.lt_two_pow_self.le
        have hk3 : (k : ℝ) ^ 3 ≤ (8 : ℝ) ^ k := by
          calc (k : ℝ) ^ 3 ≤ ((2 : ℝ) ^ k) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg k) hk2 3
            _ = (8 : ℝ) ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        have h36 : (1 / 36 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ k / 4 := by
          obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
          rw [pow_add, pow_add]
          have h1 : (1 / 36 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
          have h2 : (1 / 36 : ℝ) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 / 4 := by norm_num
          calc (1 / 36 : ℝ) ^ m * (1 / 36 : ℝ) ^ 2
              ≤ (1 / 2 : ℝ) ^ m * ((1 / 2 : ℝ) ^ 2 / 4) := mul_le_mul h1 h2 (by norm_num) (by positivity)
            _ = (1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ 2 / 4 := by ring
        calc (k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k
            ≤ (8 : ℝ) ^ k * (1 / 288 : ℝ) ^ k := mul_le_mul_of_nonneg_right hk3 (by positivity)
          _ = (1 / 36 : ℝ) ^ k := by rw [← mul_pow]; norm_num
          _ ≤ (1 / 2 : ℝ) ^ k / 4 := h36
      · positivity
    have hsg : Summable (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k / 4) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).div_const 4
    have hsumm : Summable (fun k : ℕ ↦ if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k else 0) :=
      Summable.of_nonneg_of_le (fun k ↦ by split_ifs <;> positivity) hdom hsg
    refine ⟨hsumm, ?_⟩
    calc ∑' k : ℕ, (if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k else 0)
        ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k / 4 := hsumm.tsum_le_tsum hdom hsg
      _ = (∑' k : ℕ, (1 / 2 : ℝ) ^ k) / 4 := tsum_div_const
      _ = 2 / 4 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
      _ ≤ 1 := by norm_num
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
            (if 2 ≤ k then ((k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k) else 0) :=
          hsumm_abs.tsum_le_tsum hshell_bound (hgeom_le1.1.mul_left _)
      _ = (4 * Real.sqrt 2 * D_bd * (12 * Real.exp 1 * (r : ℝ))) * Real.sqrt (N : ℝ) *
            ∑' k : ℕ, (if 2 ≤ k then ((k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k) else 0) := tsum_mul_left
      _ ≤ (4 * Real.sqrt 2 * D_bd * (12 * Real.exp 1 * (r : ℝ))) * Real.sqrt (N : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hgeom_le1.2 (by positivity)
      _ = bgDecouplingC2 r s₀ C_O * Real.sqrt (N : ℝ) := by dsimp only [bgDecouplingC2, D_bd]; ring
  -- Step 4: Bound `((G.ρβ * thermalBackgroundOp hH β).trace).re ≤ N`.
  have hbg_le : ((G.ρβ * thermalBackgroundOp hH β).trace).re ≤ (N : ℝ) := by
    have hhas := hasSum_trace_bgShell hH β G.ρβ
    rw [← hhas.tsum_eq]
    have hterm_bg : ∀ k : ℕ, (G.ρβ * bgShell (∑ Z ∈ E, h Z) β k).trace.re ≤
        (N : ℝ) * (if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k else 0) := by
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
        have hq1 : β * (r : ℝ) * Jsite ≤ 1 / 288 := by
          have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
          have hnn : 0 ≤ β * (r : ℝ) * Jsite := by positivity
          calc β * (r : ℝ) * Jsite = (β * (r : ℝ) * Jsite) * 1 := by ring
            _ ≤ (β * (r : ℝ) * Jsite) * Real.exp 1 := mul_le_mul_of_nonneg_left he1 hnn
            _ = β * Real.exp 1 * (r : ℝ) * Jsite := by ring
            _ ≤ 1 / 288 := hβ_q
        calc (3 / 4 : ℝ) * (k : ℝ) * ((k - 1 : ℕ) : ℝ) * (β * (r : ℝ) * Jsite) ^ k
            ≤ 1 * (k : ℝ) * (k : ℝ) * (1 / 288 : ℝ) ^ k := by
              have hp : (β * (r : ℝ) * Jsite) ^ k ≤ (1 / 288 : ℝ) ^ k :=
                pow_le_pow_left₀ (by positivity) hq1 k
              gcongr; norm_num
          _ ≤ (k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k := by
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
        ≤ ∑' k : ℕ, (N : ℝ) * (if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k else 0) :=
          hsumm_bg.tsum_le_tsum hterm_bg (hgeom_le1.1.mul_left _)
      _ = (N : ℝ) * ∑' k : ℕ, (if 2 ≤ k then (k : ℝ) ^ 3 * (1 / 288 : ℝ) ^ k else 0) := tsum_mul_left
      _ ≤ (N : ℝ) * 1 := mul_le_mul_of_nonneg_left hgeom_le1.2 (Nat.cast_nonneg N)
      _ = (N : ℝ) := mul_one _
  -- Step 5: Combine with Proposition 6.4(1) (`prop_6_4_part1_shifted_eq_6_4`) to get Eq. (6.7)!
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

end ThermalBackgroundShells

end KrylovChaos
