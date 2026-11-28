/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.DoubleWellTunneling
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Proposition 9.1(3): Exact `doubleWellTridiag` Eigenstates Wired into Eq. (9.3)

Constructs the two lowest distinct-parity normalized eigenstates `|φ_+⟩`, `|φ_-⟩` directly from
the `D × D` symmetric tridiagonal double-well matrix `doubleWellTridiag D E_B` (`D ≥ 4`, `E_B > 2`)
and proves Proposition 9.1(3) (Eq. 9.3) end-to-end without abstract limit hypotheses:
1. `doubleWellTridiag_exists_even_odd_ground_states`: extracts normalized even and odd eigenstates
   `φ_+, φ_- : Fin D → ℝ` with `φ_± 0 > 0`, `E_± ∈ [-(E_B - 2)⁻¹, 0]`, and `E_+ ≠ E_-`.
2. `doubleWellPsi0`, `doubleWellPsiEvol`, `doubleWellKrylovK`, `doubleWellQExp`,
   `doubleWellDeltaQ`, `doubleWellSigma0`: defines `|ψ₀(E_B)⟩ = (|φ_+⟩ + |φ_-⟩) / √2`, its
   unitary evolution `|ψ(t)⟩ = e^{-i ℒ t} |ψ₀⟩`, `Q = diag(0, 1, …, D - 1)`, `σ₀(E_B) = √Var_{ψ₀}(Q)`,
   `ΔQ(t_*)`, and 2D Krylov complexity `K(t_*)` at `t_*(E_B) = π / |E_- - E_+|`.
3. `doubleWellPsiEvol_schrodinger_ode`: verifies `d/dt |ψ(t)⟩ = -i ℒ |ψ(t)⟩` and `|ψ(0)⟩ = |ψ₀⟩`.
4. `prop_9_1_part3_doubleWell_end_to_end_eq_9_3`: proves directly from `lemma_B_1_eigenvec_decay_eq_B2_B3`
   and `tendsto_doubleWellDecayQ_zero` that `K(t_*) = 1`, `σ₀(E_B) → 0`, `ΔQ(t_*(E_B)) → D - 1`,
   and `ΔQ(t_*) / (K(t_*) + σ₀ * √K(t_*)) → D - 1` as `E_B → ∞`.
-/

namespace KrylovChaos

open Matrix Filter Topology

section DoubleWellEigenstates

/-- Spectral decomposition helper: `doubleWellTridiag D E_B = U * diag(λ) * Uᵀ`. -/
private lemma doubleWellTridiag_spectral {D : ℕ} (E_B : ℝ) :
    let hL := doubleWellTridiag_isHermitian D E_B
    let U : Matrix (Fin D) (Fin D) ℝ := (hL.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℝ)
    U * Uᵀ = 1 ∧ Uᵀ * U = 1 ∧
    doubleWellTridiag D E_B = U * Matrix.diagonal hL.eigenvalues * Uᵀ := by
  intro hL U
  have hU1 : U * Uᵀ = 1 := by
    have h : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hL.eigenvectorUnitary.2
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hU2 : Uᵀ * U = 1 := by
    have h : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hL.eigenvectorUnitary.2
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hspec : doubleWellTridiag D E_B = U * Matrix.diagonal hL.eigenvalues * Uᵀ := by
    have hs := hL.spectral_theorem
    simpa [U, Matrix.conjTranspose_eq_transpose_of_trivial, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def] using hs
  exact ⟨hU1, hU2, hspec⟩

/-- Symmetry of the parity reflection matrix `parityMat D`. -/
private lemma parityMat_transpose (D : ℕ) : (parityMat D)ᵀ = parityMat D := by
  ext i j
  simp only [Matrix.transpose_apply, parityMat, Matrix.of_apply]
  by_cases h : j.val + i.val + 1 = D
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

/-- Dot-product invariance under parity reflection `parityMat D`. -/
private lemma dotProduct_parityMat_mulVec {D : ℕ} (u v : Fin D → ℝ) :
    dotProduct (parityMat D *ᵥ u) v = dotProduct u (parityMat D *ᵥ v) := by
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  have hsym : parityMat D j i = parityMat D i j := by
    have := congrFun (congrFun (parityMat_transpose D) i) j
    simpa [Matrix.transpose_apply] using this
  rw [hsym]; ring

/-- Even and odd vectors are orthogonal. -/
private lemma dotProduct_eq_zero_of_opposite_parity {D : ℕ} (u v : Fin D → ℝ)
    (hu : parityMat D *ᵥ u = u) (hv : parityMat D *ᵥ v = -v) :
    dotProduct u v = 0 := by
  have h1 : dotProduct u v = dotProduct (parityMat D *ᵥ u) v := by rw [hu]
  rw [dotProduct_parityMat_mulVec, hv, dotProduct_neg] at h1
  linarith

/-- Normalized symmetric boundary test vector `u₊ = (e_0 + e_{D-1}) / √2`. -/
private noncomputable def dwEvenTest {D : ℕ} (hD : 4 ≤ D) : Fin D → ℝ :=
  fun i ↦ if i.val = 0 ∨ i.val = D - 1 then (Real.sqrt 2)⁻¹ else 0

/-- Normalized antisymmetric boundary test vector `u₋ = (e_0 - e_{D-1}) / √2`. -/
private noncomputable def dwOddTest {D : ℕ} (hD : 4 ≤ D) : Fin D → ℝ :=
  fun i ↦ if i.val = 0 then (Real.sqrt 2)⁻¹ else if i.val = D - 1 then -(Real.sqrt 2)⁻¹ else 0

private lemma dwEvenTest_props {D : ℕ} (hD : 4 ≤ D) (E_B : ℝ) :
    parityMat D *ᵥ dwEvenTest hD = dwEvenTest hD ∧
    dotProduct (dwEvenTest hD) (dwEvenTest hD) = 1 ∧
    dotProduct (dwEvenTest hD) (doubleWellTridiag D E_B *ᵥ dwEvenTest hD) = 0 := by
  have hD2 : 2 ≤ D := by omega
  have h0_ne : (⟨0, by omega⟩ : Fin D) ≠ ⟨D - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; dsimp at this; omega
  have hsq2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← inv_mul_eq_iff_eq_mul₀ (by positivity)]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (Real.sqrt 2 * Real.sqrt 2)⁻¹ := by
      rw [mul_inv]
    rw [this, h2]; ring
  refine ⟨?_, ?_, ?_⟩
  · ext i
    rw [parityMat_mulVec]
    unfold dwEvenTest revFin
    dsimp only
    by_cases h0 : i.val = 0
    · rw [if_pos (Or.inr (by omega)), if_pos (Or.inl h0)]
    · by_cases h1 : i.val = D - 1
      · rw [if_pos (Or.inl (by omega)), if_pos (Or.inr h1)]
      · rw [if_neg (by omega), if_neg (by omega)]
  · unfold dotProduct
    rw [← Finset.sum_subset (s₁ := {⟨0, by omega⟩, ⟨D - 1, by omega⟩}) (Finset.subset_univ _)]
    · rw [Finset.sum_pair h0_ne]
      unfold dwEvenTest
      simp only [true_or, or_true, ↓reduceIte]
      linarith
    · intro i _ hnot
      have hi0 : i.val ≠ 0 := fun h ↦ hnot (by simp [Fin.ext_iff, h])
      have hi1 : i.val ≠ D - 1 := fun h ↦ hnot (by simp [Fin.ext_iff, h])
      unfold dwEvenTest
      rw [if_neg (by omega), mul_zero]
  · rw [doubleWellTridiag_quadForm hD2 E_B (dwEvenTest hD)]
    have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)),
        dwEvenTest hD i ^ 2 = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      have hnot := (Finset.mem_filter.mp hi).2
      unfold dwEvenTest; rw [if_neg hnot]; norm_num
    have h2 : ∑ j : Fin (D - 1), dwEvenTest hD ⟨j.val, by omega⟩ *
        dwEvenTest hD ⟨j.val + 1, by omega⟩ = 0 := by
      apply Finset.sum_eq_zero; intro j _
      unfold dwEvenTest
      by_cases hj0 : j.val = 0
      · have hne : ¬(j.val + 1 = 0 ∨ j.val + 1 = D - 1) := by omega
        rw [if_neg hne, mul_zero]
      · by_cases hj1 : j.val = D - 1
        · omega
        · have hne : ¬(j.val = 0 ∨ j.val = D - 1) := by omega
          rw [if_neg hne, zero_mul]
    rw [h1, h2]; ring

private lemma dwOddTest_props {D : ℕ} (hD : 4 ≤ D) (E_B : ℝ) :
    parityMat D *ᵥ dwOddTest hD = -(dwOddTest hD) ∧
    dotProduct (dwOddTest hD) (dwOddTest hD) = 1 ∧
    dotProduct (dwOddTest hD) (doubleWellTridiag D E_B *ᵥ dwOddTest hD) = 0 := by
  have hD2 : 2 ≤ D := by omega
  have h0_ne : (⟨0, by omega⟩ : Fin D) ≠ ⟨D - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; dsimp at this; omega
  have hsq2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (Real.sqrt 2 * Real.sqrt 2)⁻¹ := by
      rw [mul_inv]
    rw [this, h2]; ring
  refine ⟨?_, ?_, ?_⟩
  · ext i
    rw [parityMat_mulVec, Pi.neg_apply]
    unfold dwOddTest revFin
    dsimp only
    by_cases h0 : i.val = 0
    · rw [if_neg (by omega), if_pos (by omega), if_pos h0]
    · by_cases h1 : i.val = D - 1
      · rw [if_pos (by omega), if_neg h0, if_pos h1, neg_neg]
      · rw [if_neg (by omega), if_neg (by omega), if_neg h0, if_neg h1, neg_zero]
  · unfold dotProduct
    rw [← Finset.sum_subset (s₁ := {⟨0, by omega⟩, ⟨D - 1, by omega⟩}) (Finset.subset_univ _)]
    · rw [Finset.sum_pair h0_ne]
      unfold dwOddTest
      simp only [↓reduceIte, show D - 1 ≠ 0 by omega, neg_mul, mul_neg, neg_neg]
      linarith
    · intro i _ hnot
      have hi0 : i.val ≠ 0 := fun h ↦ hnot (by simp [Fin.ext_iff, h])
      have hi1 : i.val ≠ D - 1 := fun h ↦ hnot (by simp [Fin.ext_iff, h])
      unfold dwOddTest
      rw [if_neg hi0, if_neg hi1, mul_zero]
  · rw [doubleWellTridiag_quadForm hD2 E_B (dwOddTest hD)]
    have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin D ↦ ¬(i.val = 0 ∨ i.val = D - 1)),
        dwOddTest hD i ^ 2 = 0 := by
      apply Finset.sum_eq_zero; intro i hi
      have hnot := (Finset.mem_filter.mp hi).2
      unfold dwOddTest
      rw [if_neg (by tauto), if_neg (by tauto)]; norm_num
    have h2 : ∑ j : Fin (D - 1), dwOddTest hD ⟨j.val, by omega⟩ *
        dwOddTest hD ⟨j.val + 1, by omega⟩ = 0 := by
      apply Finset.sum_eq_zero; intro j _
      unfold dwOddTest
      split_ifs <;> try omega
      all_goals ring
    rw [h1, h2]; ring

/-- Package for the two lowest distinct-parity normalized eigenstates of `doubleWellTridiag D E_B`. -/
structure DoubleWellGroundPair (D : ℕ) (hD : 4 ≤ D) (E_B : ℝ) where
  φp : Fin D → ℝ
  φm : Fin D → ℝ
  Ep : ℝ
  Em : ℝ
  heig_p : doubleWellTridiag D E_B *ᵥ φp = Ep • φp
  heig_m : doubleWellTridiag D E_B *ᵥ φm = Em • φm
  hpar_p : parityMat D *ᵥ φp = φp
  hpar_m : parityMat D *ᵥ φm = -φm
  hnorm_p : ∑ j : Fin D, φp j ^ 2 = 1
  hnorm_m : ∑ j : Fin D, φm j ^ 2 = 1
  hpos_p : 0 < φp ⟨0, by omega⟩
  hpos_m : 0 < φm ⟨0, by omega⟩
  hEp_le : Ep ≤ 0
  hEm_le : Em ≤ 0
  hEp_ge : -(1 / (E_B - 2)) ≤ Ep
  hEm_ge : -(1 / (E_B - 2)) ≤ Em
  hne : Ep ≠ Em

/-- **Existence of Distinct-Parity Ground Eigenstates of `doubleWellTridiag D E_B`**:
For every `D ≥ 4` and `E_B > 2`, extracts normalized even (`φ₊`) and odd (`φ₋`) eigenstates
directly from the spectral decomposition of `doubleWellTridiag D E_B`, with `φ_± 0 > 0`,
`E_± ∈ [-(E_B - 2)⁻¹, 0]`, and `E_+ ≠ E_-`. -/
theorem doubleWellTridiag_exists_even_odd_ground_states {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ}
    (hEB : 2 < E_B) : Nonempty (DoubleWellGroundPair D hD E_B) := by
  have hD2 : 2 ≤ D := by omega
  let hL := doubleWellTridiag_isHermitian D E_B
  let U : Matrix (Fin D) (Fin D) ℝ := (hL.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℝ)
  rcases doubleWellTridiag_spectral (D := D) E_B with ⟨hU1, hU2, hspec⟩
  let e : Fin D → Fin D → ℝ := fun k i ↦ U i k
  have heig : ∀ k : Fin D, doubleWellTridiag D E_B *ᵥ e k = hL.eigenvalues k • e k := by
    intro k
    have hmul : doubleWellTridiag D E_B * U = U * Matrix.diagonal hL.eigenvalues := by
      conv_lhs => rw [hspec]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hU2, Matrix.mul_one]
    ext i
    have h1 := congrFun (congrFun hmul i) k
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte] at h1
    simpa [Matrix.mulVec, dotProduct, e, Pi.smul_apply, smul_eq_mul, mul_comm] using h1
  have hnorm_e : ∀ k : Fin D, ∑ i : Fin D, e k i ^ 2 = 1 := by
    intro k
    have h1 := congrFun (congrFun hU2 k) k
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
    simp only [Matrix.transpose_apply] at h1
    have h2 : ∑ i : Fin D, e k i ^ 2 = ∑ i : Fin D, U i k * U i k := by
      apply Finset.sum_congr rfl; intro i _; dsimp only [e]; ring
    rw [h2, h1]
  have hne_e : ∀ k : Fin D, e k ≠ 0 := by
    intro k h0
    have h := hnorm_e k
    rw [h0] at h; simp at h
  -- Helper: from a normalized test vector `u` of fixed parity `s ∈ {+1, -1}` with `⟨u, L u⟩ = 0`,
  -- extract an eigenindex `k` of the same parity with `λ_k ≤ 0`.
  have extract_eigen : ∀ (u : Fin D → ℝ) (s : ℝ), (s = 1 ∨ s = -1) →
      parityMat D *ᵥ u = s • u →
      dotProduct u u = 1 →
      dotProduct u (doubleWellTridiag D E_B *ᵥ u) = 0 →
      ∃ k : Fin D, parityMat D *ᵥ e k = s • e k ∧ hL.eigenvalues k ≤ 0 := by
    intro u s hs hpar_u hu_norm hu_ray
    let c : Fin D → ℝ := Uᵀ *ᵥ u
    have hc_eq : ∀ k : Fin D, c k = dotProduct (e k) u := by
      intro k; simp [c, e, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    have hdot_mulVec : ∀ (M : Matrix (Fin D) (Fin D) ℝ) (x y : Fin D → ℝ),
        dotProduct (M *ᵥ x) y = dotProduct x (Mᵀ *ᵥ y) := by
      intro M x y
      simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    have hc_norm : ∑ k : Fin D, c k ^ 2 = 1 := by
      have hdot : dotProduct c c = dotProduct u u := by
        dsimp only [c]
        rw [hdot_mulVec, Matrix.transpose_transpose, Matrix.mulVec_mulVec, hU1, Matrix.one_mulVec]
      rw [hu_norm] at hdot
      simpa [dotProduct, sq] using hdot
    have hc_ray : ∑ k : Fin D, hL.eigenvalues k * c k ^ 2 = 0 := by
      have h1 : dotProduct u (doubleWellTridiag D E_B *ᵥ u) =
          dotProduct c (Matrix.diagonal hL.eigenvalues *ᵥ c) := by
        conv_lhs => rw [hspec]
        dsimp only [c]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_comm u,
          hdot_mulVec, dotProduct_comm]
      rw [hu_ray] at h1
      have h2 : dotProduct c (Matrix.diagonal hL.eigenvalues *ᵥ c) =
          ∑ k : Fin D, hL.eigenvalues k * c k ^ 2 := by
        unfold dotProduct
        apply Finset.sum_congr rfl; intro k _
        simp [Matrix.mulVec_diagonal]; ring
      linarith
    have hc_zero_opp : ∀ k : Fin D, parityMat D *ᵥ e k ≠ s • e k → c k = 0 := by
      intro k hne_par
      have hpar_k := doubleWellTridiag_eigenvec_parity hD2 E_B (hL.eigenvalues k) (e k) (heig k) (hne_e k)
      rw [hc_eq k]
      rcases hs with rfl | rfl
      · rcases hpar_k with hp | hm
        · exfalso; apply hne_par; simpa using hp
        · exact (dotProduct_eq_zero_of_opposite_parity u (e k) (by simpa using hpar_u) hm).symm.trans
            (by rw [dotProduct_comm]) ▸ (by rw [dotProduct_comm]; exact dotProduct_eq_zero_of_opposite_parity u (e k) (by simpa using hpar_u) hm)
      · rcases hpar_k with hp | hm
        · exact dotProduct_eq_zero_of_opposite_parity (e k) u hp (by simpa using hpar_u)
        · exfalso; apply hne_par; simpa using hm
    by_contra hall
    push_neg at hall
    have hpos_sum : 0 < ∑ k : Fin D, hL.eigenvalues k * c k ^ 2 := by
      have hex_nz : ∃ k : Fin D, c k ≠ 0 := by
        by_contra h0; push_neg at h0
        have : ∑ k : Fin D, c k ^ 2 = 0 := Finset.sum_eq_zero fun k _ ↦ by rw [h0 k]; norm_num
        linarith
      rcases hex_nz with ⟨k₀, hk₀⟩
      have hpar_k0 : parityMat D *ᵥ e k₀ = s • e k₀ := by
        by_contra hne_p; exact hk₀ (hc_zero_opp k₀ hne_p)
      have hlam_pos : 0 < hL.eigenvalues k₀ := hall k₀ hpar_k0
      have hterm_pos : 0 < hL.eigenvalues k₀ * c k₀ ^ 2 := mul_pos hlam_pos (sq_pos_of_ne_zero hk₀)
      have hnonneg : ∀ k : Fin D, 0 ≤ hL.eigenvalues k * c k ^ 2 := by
        intro k
        by_cases hpk : parityMat D *ᵥ e k = s • e k
        · exact mul_nonneg (hall k hpk).le (sq_nonneg _)
        · rw [hc_zero_opp k hpk]; norm_num
      have hle := Finset.single_le_sum (fun k _ ↦ hnonneg k) (Finset.mem_univ k₀)
      linarith
    linarith
  rcases dwEvenTest_props hD E_B with ⟨he_par, he_norm, he_ray⟩
  rcases dwOddTest_props hD E_B with ⟨ho_par, ho_norm, ho_ray⟩
  rcases extract_eigen (dwEvenTest hD) 1 (Or.inl rfl) (by simpa using he_par) he_norm he_ray with
    ⟨kp, hkp_par, hkp_le⟩
  rcases extract_eigen (dwOddTest hD) (-1) (Or.inr rfl) (by simpa using ho_par) ho_norm ho_ray with
    ⟨km, hkm_par, hkm_le⟩
  -- Orient both eigenvectors so `φ 0 > 0` (using Sturm non-vanishing at site `0`).
  have hkp0_ne : e kp ⟨0, by omega⟩ ≠ 0 := fun h0 ↦
    hne_e kp (doubleWellTridiag_sturm_zero hD2 E_B (hL.eigenvalues kp) (e kp) (heig kp) h0)
  have hkm0_ne : e km ⟨0, by omega⟩ ≠ 0 := fun h0 ↦
    hne_e km (doubleWellTridiag_sturm_zero hD2 E_B (hL.eigenvalues km) (e km) (heig km) h0)
  let sp : ℝ := if 0 < e kp ⟨0, by omega⟩ then 1 else -1
  let sm : ℝ := if 0 < e km ⟨0, by omega⟩ then 1 else -1
  have hsp_sq : sp ^ 2 = 1 := by dsimp only [sp]; split_ifs <;> norm_num
  have hsm_sq : sm ^ 2 = 1 := by dsimp only [sm]; split_ifs <;> norm_num
  let φp : Fin D → ℝ := sp • e kp
  let φm : Fin D → ℝ := sm • e km
  have hφp_eig : doubleWellTridiag D E_B *ᵥ φp = hL.eigenvalues kp • φp := by
    dsimp only [φp]; rw [Matrix.mulVec_smul, heig kp, smul_comm]
  have hφm_eig : doubleWellTridiag D E_B *ᵥ φm = hL.eigenvalues km • φm := by
    dsimp only [φm]; rw [Matrix.mulVec_smul, heig km, smul_comm]
  have hφp_par : parityMat D *ᵥ φp = φp := by
    dsimp only [φp]; rw [Matrix.mulVec_smul, hkp_par]; simp
  have hφm_par : parityMat D *ᵥ φm = -φm := by
    dsimp only [φm]; rw [Matrix.mulVec_smul, hkm_par]; simp
  have hφp_norm : ∑ j : Fin D, φp j ^ 2 = 1 := by
    have : ∑ j : Fin D, φp j ^ 2 = sp ^ 2 * ∑ j : Fin D, e kp j ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; simp [φp]; ring
    rw [this, hsp_sq, hnorm_e kp, mul_one]
  have hφm_norm : ∑ j : Fin D, φm j ^ 2 = 1 := by
    have : ∑ j : Fin D, φm j ^ 2 = sm ^ 2 * ∑ j : Fin D, e km j ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; simp [φm]; ring
    rw [this, hsm_sq, hnorm_e km, mul_one]
  have hφp_pos : 0 < φp ⟨0, by omega⟩ := by
    dsimp only [φp, sp, Pi.smul_apply, smul_eq_mul]
    split_ifs with h
    · linarith
    · have hlt : e kp ⟨0, by omega⟩ < 0 := lt_of_le_of_ne (not_lt.mp h) hkp0_ne
      linarith
  have hφm_pos : 0 < φm ⟨0, by omega⟩ := by
    dsimp only [φm, sm, Pi.smul_apply, smul_eq_mul]
    split_ifs with h
    · linarith
    · have hlt : e km ⟨0, by omega⟩ < 0 := lt_of_le_of_ne (not_lt.mp h) hkm0_ne
      linarith
  have hEp_ge : -(1 / (E_B - 2)) ≤ hL.eigenvalues kp := by
    have hray := (doubleWellTridiag_rayleigh_bounds hD hEB φp).2.2
    have hdot : dotProduct φp φp = 1 := by
      simpa [dotProduct, sq] using hφp_norm
    have hlhs : dotProduct φp (doubleWellTridiag D E_B *ᵥ φp) = hL.eigenvalues kp := by
      rw [hφp_eig, dotProduct_smul, smul_eq_mul, hdot, mul_one]
    rw [hlhs, hdot, mul_one] at hray
    exact hray
  have hEm_ge : -(1 / (E_B - 2)) ≤ hL.eigenvalues km := by
    have hray := (doubleWellTridiag_rayleigh_bounds hD hEB φm).2.2
    have hdot : dotProduct φm φm = 1 := by
      simpa [dotProduct, sq] using hφm_norm
    have hlhs : dotProduct φm (doubleWellTridiag D E_B *ᵥ φm) = hL.eigenvalues km := by
      rw [hφm_eig, dotProduct_smul, smul_eq_mul, hdot, mul_one]
    rw [hlhs, hdot, mul_one] at hray
    exact hray
  have hne : hL.eigenvalues kp ≠ hL.eigenvalues km := by
    intro heq
    have hφp_ne : φp ≠ 0 := by intro h; rw [h] at hφp_pos; simp at hφp_pos
    have hφm_ne : φm ≠ 0 := by intro h; rw [h] at hφm_pos; simp at hφm_pos
    have hφm_eig' : doubleWellTridiag D E_B *ᵥ φm = hL.eigenvalues kp • φm := by
      rw [heq]; exact hφm_eig
    obtain ⟨c, hc⟩ := doubleWellTridiag_eigenspace_simple hD2 E_B (hL.eigenvalues kp)
      φp φm hφp_eig hφm_eig' hφm_ne
    have hpar_eq : parityMat D *ᵥ φp = -φp := by
      rw [hc, Matrix.mulVec_smul, hφm_par, smul_neg]
    have hzero : φp = 0 := by
      ext i
      have h1 := congrFun hpar_eq i
      have h2 := congrFun hφp_par i
      simp only [Pi.neg_apply] at h1
      linarith
    exact hφp_ne hzero
  exact ⟨{
    φp := φp, φm := φm, Ep := hL.eigenvalues kp, Em := hL.eigenvalues km
    heig_p := hφp_eig, heig_m := hφm_eig
    hpar_p := hφp_par, hpar_m := hφm_par
    hnorm_p := hφp_norm, hnorm_m := hφm_norm
    hpos_p := hφp_pos, hpos_m := hφm_pos
    hEp_le := hkp_le, hEm_le := hkm_le
    hEp_ge := hEp_ge, hEm_ge := hEm_ge
    hne := hne
  }⟩

/-- Chosen distinct-parity ground-state pair for `D ≥ 4`, `E_B > 2`. -/
noncomputable def doubleWellGround {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    DoubleWellGroundPair D hD E_B :=
  Classical.choice (doubleWellTridiag_exists_even_odd_ground_states hD hEB)

end DoubleWellEigenstates

section DoubleWellKrylovDynamics

/-- Initial localized state `|ψ₀(E_B)⟩ = (|φ_+⟩ + |φ_-⟩) / √2 ∈ ℂ^D`. -/
noncomputable def doubleWellPsi0 {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    Fin D → ℂ :=
  let P := doubleWellGround hD hEB
  fun j ↦ (((P.φp j + P.φm j) / Real.sqrt 2 : ℝ) : ℂ)

/-- Unitary Schrödinger evolution `|ψ(t)⟩ = e^{-i ℒ t} |ψ₀⟩` in the 2D invariant subspace
`span{|φ_+⟩, |φ_-⟩} ⊆ ℂ^D`. -/
noncomputable def doubleWellPsiEvol {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B)
    (t : ℝ) : Fin D → ℂ :=
  let P := doubleWellGround hD hEB
  fun j ↦ (Complex.exp (-Complex.I * (P.Ep : ℂ) * (t : ℂ)) * (P.φp j : ℂ) +
    Complex.exp (-Complex.I * (P.Em : ℂ) * (t : ℂ)) * (P.φm j : ℂ)) / (Real.sqrt 2 : ℂ)

/-- Tunneling time `t_*(E_B) = π / |E_- - E_+|`. -/
noncomputable def doubleWellTunnelTime {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) : ℝ :=
  let P := doubleWellGround hD hEB
  Real.pi / |P.Em - P.Ep|

/-- Exact 2D Krylov complexity `K(t) = sin²((E_- - E_+) t / 2)` on `span{|K₀⟩, |K₁⟩} ⊆ ℂ^D`. -/
noncomputable def doubleWellKrylovK {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) (t : ℝ) : ℝ :=
  let P := doubleWellGround hD hEB
  Real.sin ((P.Em - P.Ep) * t / 2) ^ 2

/-- Expectation value `⟨ψ|Q|ψ⟩ = ∑ j, j * ‖ψ j‖²` of the position operator `Q = diag(0, …, D - 1)`. -/
noncomputable def doubleWellQExp {D : ℕ} (ψ : Fin D → ℂ) : ℝ :=
  ∑ j : Fin D, (j.val : ℝ) * ‖ψ j‖ ^ 2

/-- Expectation value `⟨ψ|Q²|ψ⟩ = ∑ j, j² * ‖ψ j‖²`. -/
noncomputable def doubleWellQ2Exp {D : ℕ} (ψ : Fin D → ℂ) : ℝ :=
  ∑ j : Fin D, (j.val : ℝ) ^ 2 * ‖ψ j‖ ^ 2

/-- Initial variance `σ₀(E_B)² = Var_{ψ₀}(Q) = ⟨Q²⟩_{ψ₀} - ⟨Q⟩_{ψ₀}²` and `σ₀(E_B) = √Var_{ψ₀}(Q)`. -/
noncomputable def doubleWellSigma0 {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) : ℝ :=
  Real.sqrt (doubleWellQ2Exp (doubleWellPsi0 hD hEB) -
    doubleWellQExp (doubleWellPsi0 hD hEB) ^ 2)

/-- Tunneling displacement `ΔQ(t) = ⟨ψ(t)|Q|ψ(t)⟩ - ⟨ψ₀|Q|ψ₀⟩`. -/
noncomputable def doubleWellDeltaQ {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) (t : ℝ) : ℝ :=
  doubleWellQExp (doubleWellPsiEvol hD hEB t) - doubleWellQExp (doubleWellPsi0 hD hEB)

/-- **Schrödinger ODE Verification**: `|ψ(t)⟩ = doubleWellPsiEvol hD hEB t` satisfies
`|ψ(0)⟩ = |ψ₀⟩` and `d/dt |ψ(t)⟩ = -i ℒ |ψ(t)⟩` componentwise on `ℂ^D`. -/
theorem doubleWellPsiEvol_schrodinger_ode {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    doubleWellPsiEvol hD hEB 0 = doubleWellPsi0 hD hEB ∧
    ∀ (t : ℝ) (j : Fin D),
      HasDerivAt (fun s : ℝ ↦ doubleWellPsiEvol hD hEB s j)
        ((-Complex.I) * ((doubleWellTridiag D E_B).map (Complex.ofReal) *ᵥ
          doubleWellPsiEvol hD hEB t) j) t := by
  let P := doubleWellGround hD hEB
  refine ⟨?_, fun t j ↦ ?_⟩
  · ext j
    simp only [doubleWellPsiEvol, doubleWellPsi0, P, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_mul, Complex.ofReal_div, Complex.ofReal_add]
  · -- Compute `(ℒ_ℂ *ᵥ ψ(t)) j` from `ℒ *ᵥ φ_± = E_± • φ_±`.
    have hL_apply : ((doubleWellTridiag D E_B).map Complex.ofReal *ᵥ
        doubleWellPsiEvol hD hEB t) j =
        ((P.Ep : ℂ) * Complex.exp (-Complex.I * (P.Ep : ℂ) * (t : ℂ)) * (P.φp j : ℂ) +
         (P.Em : ℂ) * Complex.exp (-Complex.I * (P.Em : ℂ) * (t : ℂ)) * (P.φm j : ℂ)) /
          (Real.sqrt 2 : ℂ) := by
      have hp_j : ∑ k : Fin D, ((doubleWellTridiag D E_B j k : ℝ) : ℂ) * (P.φp k : ℂ) =
          (P.Ep : ℂ) * (P.φp j : ℂ) := by
        have h := congrFun P.heig_p j
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
        exact_mod_cast h
      have hm_j : ∑ k : Fin D, ((doubleWellTridiag D E_B j k : ℝ) : ℂ) * (P.φm k : ℂ) =
          (P.Em : ℂ) * (P.φm j : ℂ) := by
        have h := congrFun P.heig_m j
        simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
        exact_mod_cast h
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, doubleWellPsiEvol, P]
      have hsplit : ∑ k : Fin D, (doubleWellTridiag D E_B j k : ℂ) *
          ((Complex.exp (-Complex.I * (P.Ep : ℂ) * (t : ℂ)) * (P.φp k : ℂ) +
            Complex.exp (-Complex.I * (P.Em : ℂ) * (t : ℂ)) * (P.φm k : ℂ)) /
            (Real.sqrt 2 : ℂ)) =
          (Complex.exp (-Complex.I * (P.Ep : ℂ) * (t : ℂ)) *
              (∑ k : Fin D, (doubleWellTridiag D E_B j k : ℂ) * (P.φp k : ℂ)) +
           Complex.exp (-Complex.I * (P.Em : ℂ) * (t : ℂ)) *
              (∑ k : Fin D, (doubleWellTridiag D E_B j k : ℂ) * (P.φm k : ℂ))) /
            (Real.sqrt 2 : ℂ) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl; intro k _; ring
      rw [hsplit, hp_j, hm_j]; ring
    rw [hL_apply]
    have hdp : HasDerivAt (fun s : ℝ ↦ Complex.exp (-Complex.I * (P.Ep : ℂ) * (s : ℂ)))
        ((-Complex.I * (P.Ep : ℂ)) * Complex.exp (-Complex.I * (P.Ep : ℂ) * (t : ℂ))) t := by
      have hlin : HasDerivAt (fun s : ℝ ↦ -Complex.I * (P.Ep : ℂ) * (s : ℂ))
          (-Complex.I * (P.Ep : ℂ) * 1) t :=
        (Complex.ofRealCLM.hasDerivAt).const_mul (-Complex.I * (P.Ep : ℂ))
      simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.cexp
    have hdm : HasDerivAt (fun s : ℝ ↦ Complex.exp (-Complex.I * (P.Em : ℂ) * (s : ℂ)))
        ((-Complex.I * (P.Em : ℂ)) * Complex.exp (-Complex.I * (P.Em : ℂ) * (t : ℂ))) t := by
      have hlin : HasDerivAt (fun s : ℝ ↦ -Complex.I * (P.Em : ℂ) * (s : ℂ))
          (-Complex.I * (P.Em : ℂ) * 1) t :=
        (Complex.ofRealCLM.hasDerivAt).const_mul (-Complex.I * (P.Em : ℂ))
      simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.cexp
    have hsum := (hdp.mul_const (P.φp j : ℂ)).add (hdm.mul_const (P.φm j : ℂ))
    have hdiv := hsum.div_const (Real.sqrt 2 : ℂ)
    refine hdiv.congr_deriv ?_
    ring

/-- **Exact 2D Krylov Complexity at `t_* = π / |E_- - E_+|`**: `K(t_*) = 1`. -/
theorem doubleWellKrylovK_at_tunnelTime {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    doubleWellKrylovK hD hEB (doubleWellTunnelTime hD hEB) = 1 := by
  set P := doubleWellGround hD hEB
  change Real.sin ((P.Em - P.Ep) * (Real.pi / |P.Em - P.Ep|) / 2) ^ 2 = 1
  have hne : P.Em - P.Ep ≠ 0 := sub_ne_zero.mpr P.hne.symm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [abs_of_neg hlt]
    have harg : (P.Em - P.Ep) * (Real.pi / -(P.Em - P.Ep)) / 2 = -(Real.pi / 2) := by
      field_simp [hne]; ring
    rw [harg, Real.sin_neg, Real.sin_pi_div_two]; norm_num
  · rw [abs_of_pos hgt]
    have harg : (P.Em - P.Ep) * (Real.pi / (P.Em - P.Ep)) / 2 = Real.pi / 2 := by
      field_simp [hne]
    rw [harg, Real.sin_pi_div_two]; norm_num

/-- At `t = t_*`, the probability distribution of `|ψ(t_*)⟩` is the exact parity reflection
of `|ψ₀⟩`: `‖ψ(t_*) j‖² = ‖ψ₀ (revFin j)‖²`. -/
lemma doubleWellPsiEvol_normSq_at_tunnelTime {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B)
    (j : Fin D) :
    ‖doubleWellPsiEvol hD hEB (doubleWellTunnelTime hD hEB) j‖ ^ 2 =
      ‖doubleWellPsi0 hD hEB (revFin j)‖ ^ 2 := by
  let P := doubleWellGround hD hEB
  have hne : P.Em - P.Ep ≠ 0 := sub_ne_zero.mpr P.hne.symm
  have hexp_rel : Complex.exp (-Complex.I * (P.Em : ℂ) * (doubleWellTunnelTime hD hEB : ℂ)) =
      -Complex.exp (-Complex.I * (P.Ep : ℂ) * (doubleWellTunnelTime hD hEB : ℂ)) := by
    have hdiff : -Complex.I * (P.Em : ℂ) * (doubleWellTunnelTime hD hEB : ℂ) =
        -Complex.I * (P.Ep : ℂ) * (doubleWellTunnelTime hD hEB : ℂ) +
        (-Complex.I * ((P.Em - P.Ep) * doubleWellTunnelTime hD hEB : ℝ)) := by
      push_cast; ring
    rw [hdiff, Complex.exp_add]
    have hprod : (P.Em - P.Ep) * doubleWellTunnelTime hD hEB = Real.pi ∨
        (P.Em - P.Ep) * doubleWellTunnelTime hD hEB = -Real.pi := by
      change (P.Em - P.Ep) * (Real.pi / |P.Em - P.Ep|) = Real.pi ∨
        (P.Em - P.Ep) * (Real.pi / |P.Em - P.Ep|) = -Real.pi
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · right; rw [abs_of_neg hlt]; field_simp [hne]; ring
      · left; rw [abs_of_pos hgt]; field_simp [hne]
    rcases hprod with hp | hm
    · rw [hp]
      have h1 : Complex.exp (-Complex.I * (Real.pi : ℂ)) = -1 := by
        rw [show -Complex.I * (Real.pi : ℂ) = -(Real.pi * Complex.I) by ring,
          Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
      rw [h1]; ring
    · rw [hm]
      have h1 : Complex.exp (-Complex.I * ((-Real.pi : ℝ) : ℂ)) = -1 := by
        rw [Complex.ofReal_neg, show -Complex.I * -(Real.pi : ℂ) = Real.pi * Complex.I by ring,
          Complex.exp_pi_mul_I]
      rw [h1]; ring
  have hpar_p_j : P.φp (revFin j) = P.φp j := by
    have h := congrFun P.hpar_p j
    rwa [parityMat_mulVec] at h
  have hpar_m_j : P.φm (revFin j) = -P.φm j := by
    have h := congrFun P.hpar_m j
    rwa [parityMat_mulVec, Pi.neg_apply] at h
  have hpsi_eq : doubleWellPsiEvol hD hEB (doubleWellTunnelTime hD hEB) j =
      Complex.exp (-Complex.I * (P.Ep : ℂ) * (doubleWellTunnelTime hD hEB : ℂ)) *
        doubleWellPsi0 hD hEB (revFin j) := by
    unfold doubleWellPsiEvol doubleWellPsi0
    dsimp only [P]
    rw [hexp_rel, hpar_p_j, hpar_m_j]
    push_cast; ring
  rw [hpsi_eq, norm_mul]
  have hunit : ‖Complex.exp (-Complex.I * (P.Ep : ℂ) * (doubleWellTunnelTime hD hEB : ℂ))‖ = 1 := by
    rw [show -Complex.I * (P.Ep : ℂ) * (doubleWellTunnelTime hD hEB : ℂ) =
      ((-(P.Ep * doubleWellTunnelTime hD hEB) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hunit, one_mul]

/-- Normalization of `|ψ₀⟩`: `∑ j, ‖ψ₀ j‖² = 1`. -/
lemma doubleWellPsi0_normSq_sum {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    ∑ j : Fin D, ‖doubleWellPsi0 hD hEB j‖ ^ 2 = 1 := by
  let P := doubleWellGround hD hEB
  have horth : dotProduct P.φp P.φm = 0 :=
    dotProduct_eq_zero_of_opposite_parity P.φp P.φm P.hpar_p P.hpar_m
  have hterm : ∀ j : Fin D, ‖doubleWellPsi0 hD hEB j‖ ^ 2 =
      (P.φp j ^ 2 + P.φm j ^ 2 + 2 * (P.φp j * P.φm j)) / 2 := by
    intro j
    unfold doubleWellPsi0
    dsimp only [P]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by norm_num)]
    ring
  simp_rw [hterm, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hdot : ∑ j : Fin D, P.φp j * P.φm j = 0 := horth
  rw [P.hnorm_p, P.hnorm_m, hdot]; norm_num

/-- Exact tunneling displacement identity: `ΔQ(t_*) = (D - 1) - 2 ⟨Q⟩_{ψ₀}`. -/
lemma doubleWellDeltaQ_at_tunnelTime {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    doubleWellDeltaQ hD hEB (doubleWellTunnelTime hD hEB) =
      ((D : ℝ) - 1) - 2 * doubleWellQExp (doubleWellPsi0 hD hEB) := by
  unfold doubleWellDeltaQ doubleWellQExp
  simp_rw [doubleWellPsiEvol_normSq_at_tunnelTime hD hEB]
  -- Reindex `j ↦ revFin j`.
  have hbij : ∑ j : Fin D, (j.val : ℝ) * ‖doubleWellPsi0 hD hEB (revFin j)‖ ^ 2 =
      ∑ j : Fin D, ((D : ℝ) - 1 - (j.val : ℝ)) * ‖doubleWellPsi0 hD hEB j‖ ^ 2 := by
    refine Fintype.sum_equiv (Function.Involutive.toPerm (revFin (D := D)) revFin_revFin) _ _ fun j ↦ ?_
    simp only [Function.Involutive.toPerm_apply, revFin_revFin]
    congr 1
    have hj : j.val ≤ D - 1 := by omega
    have hD1 : 1 ≤ D := by omega
    have hcast : ((D - 1 - j.val : ℕ) : ℝ) = (D : ℝ) - 1 - (j.val : ℝ) := by
      rw [Nat.cast_sub hj, Nat.cast_sub hD1, Nat.cast_one]
    exact hcast
  rw [hbij]
  have hsub : ∑ j : Fin D, ((D : ℝ) - 1 - (j.val : ℝ)) * ‖doubleWellPsi0 hD hEB j‖ ^ 2 =
      ((D : ℝ) - 1) * (∑ j : Fin D, ‖doubleWellPsi0 hD hEB j‖ ^ 2) -
      ∑ j : Fin D, (j.val : ℝ) * ‖doubleWellPsi0 hD hEB j‖ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [hsub, doubleWellPsi0_normSq_sum hD hEB, mul_one]
  ring

/-- Boundary amplitude localization from Lemma B.1 Eq. (B.3):
for any normalized eigenstate `v` of `doubleWellTridiag D E_B` with `E ≤ 0` and `v 0 > 0`,
`1 / (2 * (1 + 2 * q² / (1 - q²))) ≤ (v 0)² ≤ 1 / 2`. -/
private lemma eigenvec_zero_sq_bounds {D : ℕ} (hD : 4 ≤ D) {E_B E : ℝ} (hEB : 2 < E_B)
    (hE : E ≤ 0) (v : Fin D → ℝ)
    (heig : doubleWellTridiag D E_B *ᵥ v = E • v)
    (hpar : parityMat D *ᵥ v = v ∨ parityMat D *ᵥ v = -v)
    (hnorm : ∑ j : Fin D, v j ^ 2 = 1) :
    let q := doubleWellDecayQ E_B
    1 / (2 * (1 + 2 * (q ^ 2 / (1 - q ^ 2)))) ≤ v ⟨0, by omega⟩ ^ 2 ∧
    v ⟨0, by omega⟩ ^ 2 ≤ 1 / 2 := by
  intro q
  rcases doubleWellDecayQ_props hEB with ⟨hq_pos, hq_lt1, _, _⟩
  have h1mq : 0 < 1 - q ^ 2 := by nlinarith
  have hB3 := (lemma_B_1_eigenvec_decay_eq_B2_B3 hD hEB hE v heig hnorm).2
  have hden_pos : 0 < 2 * (1 + 2 * (q ^ 2 / (1 - q ^ 2))) := by positivity
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ hden_pos]
    nlinarith
  · have hD1_eq : v ⟨D - 1, by omega⟩ ^ 2 = v ⟨0, by omega⟩ ^ 2 := by
      rcases hpar with h | h
      · have h1 := congrFun h ⟨0, by omega⟩
        rw [parityMat_mulVec] at h1
        have hr : revFin (⟨0, by omega⟩ : Fin D) = ⟨D - 1, by omega⟩ := by
          ext; simp [revFin]
        rw [hr] at h1; rw [h1]
      · have h1 := congrFun h ⟨0, by omega⟩
        rw [parityMat_mulVec, Pi.neg_apply] at h1
        have hr : revFin (⟨0, by omega⟩ : Fin D) = ⟨D - 1, by omega⟩ := by
          ext; simp [revFin]
        rw [hr] at h1; rw [h1, neg_sq]
    have h0_ne : (⟨0, by omega⟩ : Fin D) ≠ ⟨D - 1, by omega⟩ := by
      intro h; have := congrArg Fin.val h; dsimp at this; omega
    have hle : v ⟨0, by omega⟩ ^ 2 + v ⟨D - 1, by omega⟩ ^ 2 ≤ ∑ j : Fin D, v j ^ 2 := by
      calc v ⟨0, by omega⟩ ^ 2 + v ⟨D - 1, by omega⟩ ^ 2
          = ∑ j ∈ ({⟨0, by omega⟩, ⟨D - 1, by omega⟩} : Finset (Fin D)), v j ^ 2 := by
            rw [Finset.sum_pair h0_ne]
        _ ≤ ∑ j : Fin D, v j ^ 2 := Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
    linarith

/-- Quantitative tail bound on `∑_{j ≠ 0} ‖ψ₀ j‖²` in terms of `q = doubleWellDecayQ E_B`. -/
lemma doubleWellPsi0_tail_le {D : ℕ} (hD : 4 ≤ D) {E_B : ℝ} (hEB : 2 < E_B) :
    let q := doubleWellDecayQ E_B
    ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0), ‖doubleWellPsi0 hD hEB j‖ ^ 2 ≤
      4 * (q ^ 2 / (1 - q ^ 2)) + 4 * (D : ℝ) * q ^ 2 := by
  intro q
  let P := doubleWellGround hD hEB
  rcases doubleWellDecayQ_props hEB with ⟨hq_pos, hq_lt1, _, _⟩
  have h1mq : 0 < 1 - q ^ 2 := by nlinarith
  have hBp := lemma_B_1_eigenvec_decay_eq_B2_B3 hD hEB P.hEp_le P.φp P.heig_p P.hnorm_p
  have hBm := lemma_B_1_eigenvec_decay_eq_B2_B3 hD hEB P.hEm_le P.φm P.heig_m P.hnorm_m
  have hsqp := eigenvec_zero_sq_bounds hD hEB P.hEp_le P.φp P.heig_p (Or.inl P.hpar_p) P.hnorm_p
  have hsqm := eigenvec_zero_sq_bounds hD hEB P.hEm_le P.φm P.heig_m (Or.inr P.hpar_m) P.hnorm_m
  -- Split `{j | j.val ≠ 0}` into `{D - 1}` and interior `{j | j.val ≠ 0 ∧ j.val ≠ D - 1}`.
  let jD : Fin D := ⟨D - 1, by omega⟩
  have hjD_mem : jD ∈ Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, jD]; omega
  rw [← Finset.add_sum_erase _ _ hjD_mem]
  -- 1. Bound `‖ψ₀ (D - 1)‖² = (φp 0 - φm 0)² / 2 ≤ 4 * q² / (1 - q²)`.
  have hD_term : ‖doubleWellPsi0 hD hEB jD‖ ^ 2 ≤ 4 * (q ^ 2 / (1 - q ^ 2)) := by
    have hpp : P.φp jD = P.φp ⟨0, by omega⟩ := by
      have h := congrFun P.hpar_p ⟨0, by omega⟩
      rw [parityMat_mulVec] at h
      have hr : revFin (⟨0, by omega⟩ : Fin D) = jD := by ext; simp [revFin, jD]
      rwa [hr] at h
    have hpm : P.φm jD = -P.φm ⟨0, by omega⟩ := by
      have h := congrFun P.hpar_m ⟨0, by omega⟩
      rw [parityMat_mulVec, Pi.neg_apply] at h
      have hr : revFin (⟨0, by omega⟩ : Fin D) = jD := by ext; simp [revFin, jD]
      rwa [hr] at h
    have hnorm_jD : ‖doubleWellPsi0 hD hEB jD‖ ^ 2 =
        (P.φp ⟨0, by omega⟩ - P.φm ⟨0, by omega⟩) ^ 2 / 2 := by
      unfold doubleWellPsi0; dsimp only [P]
      rw [hpp, hpm, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
        Real.sq_sqrt (by norm_num)]
      ring
    rw [hnorm_jD]
    have hab_sq : (P.φp ⟨0, by omega⟩ - P.φm ⟨0, by omega⟩) ^ 2 ≤
        |P.φp ⟨0, by omega⟩ ^ 2 - P.φm ⟨0, by omega⟩ ^ 2| := by
      have h1 : |P.φp ⟨0, by omega⟩ - P.φm ⟨0, by omega⟩| ≤
          P.φp ⟨0, by omega⟩ + P.φm ⟨0, by omega⟩ := by
        rw [abs_le]; constructor <;> linarith [P.hpos_p, P.hpos_m]
      calc (P.φp ⟨0, by omega⟩ - P.φm ⟨0, by omega⟩) ^ 2
          = |P.φp ⟨0, by omega⟩ - P.φm ⟨0, by omega⟩| *
            |P.φp ⟨0, by omega⟩ - P.φm ⟨0, by omega⟩| := by rw [← sq_abs, sq]
        _ ≤ |P.φp ⟨0, by omega⟩ - P.φm ⟨0, by omega⟩| *
            (P.φp ⟨0, by omega⟩ + P.φm ⟨0, by omega⟩) :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |P.φp ⟨0, by omega⟩ - P.φm ⟨0, by omega⟩| *
            |P.φp ⟨0, by omega⟩ + P.φm ⟨0, by omega⟩| := by
            have hsum_abs : |P.φp ⟨0, by omega⟩ + P.φm ⟨0, by omega⟩| =
                P.φp ⟨0, by omega⟩ + P.φm ⟨0, by omega⟩ :=
              abs_of_pos (by linarith [P.hpos_p, P.hpos_m])
            rw [hsum_abs]
        _ = |(P.φp ⟨0, by omega⟩ - P.φm ⟨0, by omega⟩) *
            (P.φp ⟨0, by omega⟩ + P.φm ⟨0, by omega⟩)| := (abs_mul _ _).symm
        _ = |P.φp ⟨0, by omega⟩ ^ 2 - P.φm ⟨0, by omega⟩ ^ 2| := by ring_nf
    have hp_gap : 1 / 2 - P.φp ⟨0, by omega⟩ ^ 2 ≤ q ^ 2 / (1 - q ^ 2) := by
      have h1 := hBp.2
      have h2 := hsqp.2
      have hq_nn : 0 ≤ q ^ 2 / (1 - q ^ 2) := by positivity
      nlinarith
    have hm_gap : 1 / 2 - P.φm ⟨0, by omega⟩ ^ 2 ≤ q ^ 2 / (1 - q ^ 2) := by
      have h1 := hBm.2
      have h2 := hsqm.2
      have hq_nn : 0 ≤ q ^ 2 / (1 - q ^ 2) := by positivity
      nlinarith
    have habs_le : |P.φp ⟨0, by omega⟩ ^ 2 - P.φm ⟨0, by omega⟩ ^ 2| ≤ q ^ 2 / (1 - q ^ 2) := by
      rw [abs_le]; constructor <;> linarith [hsqp.2, hsqm.2, hp_gap, hm_gap]
    have hq_nn : 0 ≤ q ^ 2 / (1 - q ^ 2) := by positivity
    linarith
  -- 2. Bound each interior term `‖ψ₀ j‖² ≤ 4 q²`.
  have hint_term : ∀ j ∈ (Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0)).erase jD,
      ‖doubleWellPsi0 hD hEB j‖ ^ 2 ≤ 4 * q ^ 2 := by
    intro j hj
    have hj_neD : j ≠ jD := (Finset.mem_erase.mp hj).1
    have hj_ne0 : j.val ≠ 0 := (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2
    have hj_lt : j.val < D - 1 := by
      have : j.val ≠ D - 1 := fun h ↦ hj_neD (Fin.ext h)
      omega
    have hqj1 : q ^ j.val ≤ q := by
      have h1 : 1 ≤ j.val := by omega
      calc q ^ j.val ≤ q ^ 1 := pow_le_pow_of_le_one hq_pos.le hq_lt1.le h1
        _ = q := pow_one q
    have hqj2 : q ^ (D - 1 - j.val) ≤ q := by
      have h1 : 1 ≤ D - 1 - j.val := by omega
      calc q ^ (D - 1 - j.val) ≤ q ^ 1 := pow_le_pow_of_le_one hq_pos.le hq_lt1.le h1
        _ = q := pow_one q
    have hfp : |P.φp j| ≤ |P.φp ⟨0, by omega⟩| * (2 * q) := by
      calc |P.φp j| ≤ |P.φp ⟨0, by omega⟩| * (q ^ j.val + q ^ (D - 1 - j.val)) := hBp.1 j
        _ ≤ |P.φp ⟨0, by omega⟩| * (2 * q) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have hfm : |P.φm j| ≤ |P.φm ⟨0, by omega⟩| * (2 * q) := by
      calc |P.φm j| ≤ |P.φm ⟨0, by omega⟩| * (q ^ j.val + q ^ (D - 1 - j.val)) := hBm.1 j
        _ ≤ |P.φm ⟨0, by omega⟩| * (2 * q) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have hfp_sq : P.φp j ^ 2 ≤ 2 * q ^ 2 := by
      have h1 : P.φp j ^ 2 ≤ (|P.φp ⟨0, by omega⟩| * (2 * q)) ^ 2 := by
        rw [← sq_abs (P.φp j)]
        exact pow_le_pow_left₀ (abs_nonneg _) hfp 2
      have h2 : (|P.φp ⟨0, by omega⟩| * (2 * q)) ^ 2 = 4 * P.φp ⟨0, by omega⟩ ^ 2 * q ^ 2 := by
        rw [mul_pow, sq_abs]; ring
      nlinarith [hsqp.2, sq_nonneg q]
    have hfm_sq : P.φm j ^ 2 ≤ 2 * q ^ 2 := by
      have h1 : P.φm j ^ 2 ≤ (|P.φm ⟨0, by omega⟩| * (2 * q)) ^ 2 := by
        rw [← sq_abs (P.φm j)]
        exact pow_le_pow_left₀ (abs_nonneg _) hfm 2
      have h2 : (|P.φm ⟨0, by omega⟩| * (2 * q)) ^ 2 = 4 * P.φm ⟨0, by omega⟩ ^ 2 * q ^ 2 := by
        rw [mul_pow, sq_abs]; ring
      nlinarith [hsqm.2, sq_nonneg q]
    unfold doubleWellPsi0; dsimp only [P]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (by norm_num)]
    have hcs : (P.φp j + P.φm j) ^ 2 ≤ 2 * (P.φp j ^ 2 + P.φm j ^ 2) := by
      nlinarith [sq_nonneg (P.φp j - P.φm j)]
    linarith
  have hsum_int : ∑ j ∈ (Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0)).erase jD,
      ‖doubleWellPsi0 hD hEB j‖ ^ 2 ≤ 4 * (D : ℝ) * q ^ 2 := by
    calc ∑ j ∈ (Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0)).erase jD,
          ‖doubleWellPsi0 hD hEB j‖ ^ 2
        ≤ ∑ _j ∈ (Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0)).erase jD, (4 * q ^ 2) :=
          Finset.sum_le_sum hint_term
      _ = (((Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0)).erase jD).card : ℝ) * (4 * q ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (D : ℝ) * (4 * q ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : ((Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0)).erase jD).card ≤ D := by
            calc ((Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0)).erase jD).card
                ≤ (Finset.univ : Finset (Fin D)).card :=
                  Finset.card_le_card (Finset.subset_univ _)
              _ = D := Fintype.card_fin D
          exact_mod_cast hcard
      _ = 4 * (D : ℝ) * q ^ 2 := by ring
  linarith

/-- **Proposition 9.1(3) — Exact `doubleWellTridiag` End-to-End Limit (Eq. 9.3)**:
For any `D ≥ 4`, directly from the normalized even/odd ground eigenstates of
`doubleWellTridiag D E_B` (with ZERO abstract limit hypotheses):
1. `K(t_*(E_B)) = 1` for all `E_B > 2`,
2. `σ₀(E_B) → 0` as `E_B → ∞`,
3. `ΔQ(t_*(E_B)) → D - 1` as `E_B → ∞`,
4. `ΔQ(t_*(E_B)) / (K(t_*(E_B)) + σ₀(E_B) * √K(t_*(E_B))) → D - 1` as `E_B → ∞` (Eq. 9.3). -/
theorem prop_9_1_part3_doubleWell_end_to_end_eq_9_3 {D : ℕ} (hD : 4 ≤ D) :
    let K_fn : ℝ → ℝ := fun E_B ↦
      if h : 2 < E_B then doubleWellKrylovK hD h (doubleWellTunnelTime hD h) else 1
    let σ₀_fn : ℝ → ℝ := fun E_B ↦
      if h : 2 < E_B then doubleWellSigma0 hD h else 0
    let ΔQ_fn : ℝ → ℝ := fun E_B ↦
      if h : 2 < E_B then doubleWellDeltaQ hD h (doubleWellTunnelTime hD h) else 0
    (∀ E_B : ℝ, 2 < E_B → K_fn E_B = 1) ∧
    Tendsto σ₀_fn atTop (nhds 0) ∧
    Tendsto ΔQ_fn atTop (nhds ((D : ℝ) - 1)) ∧
    Tendsto (fun E_B : ℝ ↦ ΔQ_fn E_B / (K_fn E_B + σ₀_fn E_B * Real.sqrt (K_fn E_B)))
      atTop (nhds ((D : ℝ) - 1)) := by
  intro K_fn σ₀_fn ΔQ_fn
  have hK_eq : ∀ E_B : ℝ, 2 < E_B → K_fn E_B = 1 := by
    intro E_B hEB
    simp only [K_fn, dif_pos hEB]
    exact doubleWellKrylovK_at_tunnelTime hD hEB
  have hK_lim : Tendsto K_fn atTop (nhds 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with E_B hEB
    exact (hK_eq E_B hEB).symm
  -- Tail upper bound `B(E_B) = 4 * (q² / (1 - q²)) + 4 * D * q² → 0`.
  let B_fn : ℝ → ℝ := fun E_B ↦
    4 * (doubleWellDecayQ E_B ^ 2 / (1 - doubleWellDecayQ E_B ^ 2)) +
    4 * (D : ℝ) * doubleWellDecayQ E_B ^ 2
  have hB_lim : Tendsto B_fn atTop (nhds 0) := by
    have hq0 := tendsto_doubleWellDecayQ_zero
    have hq2 : Tendsto (fun E_B ↦ doubleWellDecayQ E_B ^ 2) atTop (nhds 0) := by
      simpa using hq0.pow 2
    have h1mq2 : Tendsto (fun E_B ↦ 1 - doubleWellDecayQ E_B ^ 2) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hq2
    have hdiv : Tendsto (fun E_B ↦ doubleWellDecayQ E_B ^ 2 / (1 - doubleWellDecayQ E_B ^ 2))
        atTop (nhds 0) := by
      have h := hq2.div h1mq2 one_ne_zero
      simpa only [zero_div] using h
    have h1 : Tendsto (fun E_B ↦ 4 * (doubleWellDecayQ E_B ^ 2 / (1 - doubleWellDecayQ E_B ^ 2)))
        atTop (nhds 0) := by
      simpa using hdiv.const_mul 4
    have h2 : Tendsto (fun E_B ↦ 4 * (D : ℝ) * doubleWellDecayQ E_B ^ 2) atTop (nhds 0) := by
      simpa using hq2.const_mul (4 * (D : ℝ))
    simpa [B_fn] using h1.add h2
  -- Show `⟨Q⟩_{ψ₀} → 0`.
  let Q0_fn : ℝ → ℝ := fun E_B ↦
    if h : 2 < E_B then doubleWellQExp (doubleWellPsi0 hD h) else 0
  have hQ0_lim : Tendsto Q0_fn atTop (nhds 0) := by
    have hB_mul : Tendsto (fun E_B ↦ (D : ℝ) * B_fn E_B) atTop (nhds 0) := by
      simpa using hB_lim.const_mul (D : ℝ)
    refine squeeze_zero' ?_ ?_ hB_mul
    · filter_upwards [eventually_gt_atTop (2 : ℝ)] with E_B hEB
      simp only [Q0_fn, dif_pos hEB, doubleWellQExp]
      exact Finset.sum_nonneg fun j _ ↦ by positivity
    · filter_upwards [eventually_gt_atTop (2 : ℝ)] with E_B hEB
      simp only [Q0_fn, dif_pos hEB, doubleWellQExp]
      have h0_zero : ∑ j : Fin D, (j.val : ℝ) * ‖doubleWellPsi0 hD hEB j‖ ^ 2 =
          ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0),
            (j.val : ℝ) * ‖doubleWellPsi0 hD hEB j‖ ^ 2 := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin D ↦ j.val ≠ 0)]
        have hrem : ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬j.val ≠ 0),
            (j.val : ℝ) * ‖doubleWellPsi0 hD hEB j‖ ^ 2 = 0 := by
          apply Finset.sum_eq_zero; intro j hj
          have h0 : j.val = 0 := by have := (Finset.mem_filter.mp hj).2; omega
          simp [h0]
        linarith
      rw [h0_zero]
      calc ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0),
            (j.val : ℝ) * ‖doubleWellPsi0 hD hEB j‖ ^ 2
          ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0),
              (D : ℝ) * ‖doubleWellPsi0 hD hEB j‖ ^ 2 := by
            apply Finset.sum_le_sum; intro j _
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact_mod_cast j.isLt.le
        _ = (D : ℝ) * ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0),
              ‖doubleWellPsi0 hD hEB j‖ ^ 2 := (Finset.mul_sum _ _ _).symm
        _ ≤ (D : ℝ) * B_fn E_B :=
            mul_le_mul_of_nonneg_left (doubleWellPsi0_tail_le hD hEB) (by positivity)
  -- Show `σ₀(E_B) → 0` via `0 ≤ σ₀(E_B) ≤ √(D² * B_fn E_B) → 0`.
  have hσ₀_lim : Tendsto σ₀_fn atTop (nhds 0) := by
    have hupper : Tendsto (fun E_B ↦ Real.sqrt ((D : ℝ) ^ 2 * B_fn E_B)) atTop (nhds 0) := by
      have h1 : Tendsto (fun E_B ↦ (D : ℝ) ^ 2 * B_fn E_B) atTop (nhds 0) := by
        simpa using hB_lim.const_mul ((D : ℝ) ^ 2)
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      simpa only [Function.comp_def, Real.sqrt_zero] using h2
    refine squeeze_zero' ?_ ?_ hupper
    · filter_upwards [eventually_gt_atTop (2 : ℝ)] with E_B hEB
      simp only [σ₀_fn, dif_pos hEB, doubleWellSigma0]
      exact Real.sqrt_nonneg _
    · filter_upwards [eventually_gt_atTop (2 : ℝ)] with E_B hEB
      simp only [σ₀_fn, dif_pos hEB, doubleWellSigma0]
      apply Real.sqrt_le_sqrt
      have hsq_nn : 0 ≤ doubleWellQExp (doubleWellPsi0 hD hEB) ^ 2 := sq_nonneg _
      have hQ2_le : doubleWellQ2Exp (doubleWellPsi0 hD hEB) ≤ (D : ℝ) ^ 2 * B_fn E_B := by
        unfold doubleWellQ2Exp
        have h0_zero : ∑ j : Fin D, (j.val : ℝ) ^ 2 * ‖doubleWellPsi0 hD hEB j‖ ^ 2 =
            ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0),
              (j.val : ℝ) ^ 2 * ‖doubleWellPsi0 hD hEB j‖ ^ 2 := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin D ↦ j.val ≠ 0)]
          have hrem : ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ ¬j.val ≠ 0),
              (j.val : ℝ) ^ 2 * ‖doubleWellPsi0 hD hEB j‖ ^ 2 = 0 := by
            apply Finset.sum_eq_zero; intro j hj
            have h0 : j.val = 0 := by have := (Finset.mem_filter.mp hj).2; omega
            simp [h0]
          linarith
        rw [h0_zero]
        calc ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0),
              (j.val : ℝ) ^ 2 * ‖doubleWellPsi0 hD hEB j‖ ^ 2
            ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0),
                (D : ℝ) ^ 2 * ‖doubleWellPsi0 hD hEB j‖ ^ 2 := by
              apply Finset.sum_le_sum; intro j _
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast j.isLt.le) 2
          _ = (D : ℝ) ^ 2 * ∑ j ∈ Finset.univ.filter (fun j : Fin D ↦ j.val ≠ 0),
                ‖doubleWellPsi0 hD hEB j‖ ^ 2 := (Finset.mul_sum _ _ _).symm
          _ ≤ (D : ℝ) ^ 2 * B_fn E_B :=
              mul_le_mul_of_nonneg_left (doubleWellPsi0_tail_le hD hEB) (by positivity)
      linarith
  -- Show `ΔQ(t_*(E_B)) → D - 1`.
  have hΔQ_lim : Tendsto ΔQ_fn atTop (nhds ((D : ℝ) - 1)) := by
    have h1 : Tendsto (fun E_B ↦ ((D : ℝ) - 1) - 2 * Q0_fn E_B) atTop (nhds ((D : ℝ) - 1)) := by
      simpa using tendsto_const_nhds.sub (hQ0_lim.const_mul 2)
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with E_B hEB
    simp only [ΔQ_fn, Q0_fn, dif_pos hEB]
    exact (doubleWellDeltaQ_at_tunnelTime hD hEB).symm
  exact ⟨hK_eq, hσ₀_lim, hΔQ_lim,
    prop_9_1_part3_exact_D_limit_eq_9_3 D ΔQ_fn K_fn σ₀_fn hΔQ_lim hK_lim hσ₀_lim⟩

end DoubleWellKrylovDynamics

end KrylovChaos
