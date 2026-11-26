/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import KrylovChaos.QubitAlgebra
import KrylovChaos.ManyBodySetup
import KrylovChaos.OperatorBridges
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Concrete Wightman Projectors, Loewner Dominance & Operator-Level Lemma 4.2 (Section 4)

Constructs concrete finite-dimensional Hilbert–Schmidt / Wightman orthogonal projectors on `QubitOp N`:
1. `0 ⪯ S ⪯ N • 1`: proves `0 ≤ Re ⟨M, totalSizeOp M⟩_HS ≤ N * hsNormSq M` for every `M : QubitOp N`
   via self-adjointness and idempotence of `partialTraceSite x`.
2. **Operator-Level Lemma 4.2 (`lemma_4_2_operator_thermal_size_truncation`, Eq. 4.3)**:
   Proves the thermal-size truncation inequality directly for an operator split `O = A_M + R_M`
   on `QubitOp N` via Cauchy–Schwarz for the positive-semidefinite superoperator `totalSizeOp`.
3. **Concrete Wightman Orthogonal Projectors `Π_s^{(β)}` & Loewner Dominance**:
   Uses the Frobenius EuclideanSpace equivalence `toHSOp : QubitOp N ≃ₗ[ℂ] HSOp N` and Mathlib's
   `Submodule.starProjection` to define `wightmanProj` and prove the exact Loewner ordering
   `‖P_{W₁} v‖² ≤ ‖P_{W₂} v‖²` whenever `W₁ ≤ W₂`, instantiated on `P_{K_k} ⪯ Π_{s₀ + (r-1)k}^{(β)}`.
-/

namespace KrylovChaos

open Matrix

section OperatorSizeBounds

private lemma hsNormSq_nn {N : ℕ} (M : QubitOp N) : 0 ≤ hsNormSq M := by
  unfold hsNormSq hsInner
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_nonneg _

/-- `partialTraceSite x` is self-adjoint in the Hilbert–Schmidt inner product:
`⟨A, E_x(B)⟩_HS = ⟨E_x(A), B⟩_HS`. -/
theorem partialTraceSite_selfAdjoint {N : ℕ} (x : Fin N) (A B : QubitOp N) :
    hsInner A (partialTraceSite x B) = hsInner (partialTraceSite x A) B := by
  unfold partialTraceSite hsInner
  have hL : Matrix.trace (Aᴴ * ((1 / 4 : ℂ) • ∑ α : Fin 4, pauliSite x α * B * pauliSite x α)) =
      (1 / 4 : ℂ) * ∑ α : Fin 4, Matrix.trace (Aᴴ * (pauliSite x α * B * pauliSite x α)) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum]; rfl
  have hR : Matrix.trace (((1 / 4 : ℂ) • ∑ α : Fin 4, pauliSite x α * A * pauliSite x α)ᴴ * B) =
      (1 / 4 : ℂ) * ∑ α : Fin 4, Matrix.trace ((pauliSite x α * A * pauliSite x α)ᴴ * B) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum, Matrix.smul_mul, Matrix.trace_smul,
        Matrix.sum_mul, Matrix.trace_sum]
    have hstar : star (1 / 4 : ℂ) = (1 / 4 : ℂ) := by simp
    rw [hstar]; rfl
  rw [hL, hR]
  congr 1
  apply Finset.sum_congr rfl; intro α _
  have hph : (pauliSite x α)ᴴ = pauliSite x α := pauliSite_herm x α
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hph]
  calc Matrix.trace (Aᴴ * (pauliSite x α * B * pauliSite x α))
      = Matrix.trace ((Aᴴ * pauliSite x α * B) * pauliSite x α) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (pauliSite x α * (Aᴴ * pauliSite x α * B)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (pauliSite x α * Aᴴ * pauliSite x α * B) := by simp only [Matrix.mul_assoc]

/-- Single-site Pauli averaging is idempotent: `E_x (E_x A) = E_x A`. -/
theorem partialTraceSite_idempotent {N : ℕ} (x : Fin N) (A : QubitOp N) :
    partialTraceSite x (partialTraceSite x A) = partialTraceSite x A := by
  have hconj : ∀ (α β : Fin 4),
      pauliSite x α * (pauliSite x β * A * pauliSite x β) * pauliSite x α =
        pauliSite x (pauliMulIdx α β) * A * pauliSite x (pauliMulIdx α β) := by
    intro α β
    have hmul : pauliSite x α * pauliSite x β =
        (pauliMulPhase α β) • pauliSite x (pauliMulIdx α β) := by
      unfold pauliSite
      rw [pauliString_mul]
      congr 1
      · rw [Finset.prod_eq_single x]
        · simp
        · intro y _ hne; simp [hne, pauliMulPhase]
        · intro hx; exact absurd (Finset.mem_univ x) hx
      · congr 1; funext y
        by_cases hy : y = x
        · subst hy; simp
        · simp [hy, pauliMulIdx]
    have hmulR : pauliSite x β * pauliSite x α =
        (star (pauliMulPhase α β)) • pauliSite x (pauliMulIdx α β) := by
      have h := congrArg Matrix.conjTranspose hmul
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, pauliSite_herm, pauliSite_herm,
          pauliSite_herm] at h
      exact h
    have hphase : pauliMulPhase α β * star (pauliMulPhase α β) = 1 := by
      fin_cases α <;> fin_cases β <;> simp [pauliMulPhase]
    calc pauliSite x α * (pauliSite x β * A * pauliSite x β) * pauliSite x α
        = (pauliSite x α * pauliSite x β) * A * (pauliSite x β * pauliSite x α) := by
          simp only [Matrix.mul_assoc]
      _ = ((pauliMulPhase α β) • pauliSite x (pauliMulIdx α β)) * A *
            ((star (pauliMulPhase α β)) • pauliSite x (pauliMulIdx α β)) := by rw [hmul, hmulR]
      _ = (pauliMulPhase α β * star (pauliMulPhase α β)) •
            (pauliSite x (pauliMulIdx α β) * A * pauliSite x (pauliMulIdx α β)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; ring_nf
      _ = pauliSite x (pauliMulIdx α β) * A * pauliSite x (pauliMulIdx α β) := by
          rw [hphase, one_smul]
  unfold partialTraceSite
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum,
    smul_smul]
  simp_rw [hconj]
  have hbij : ∀ α : Fin 4,
      (∑ β : Fin 4, pauliSite x (pauliMulIdx α β) * A * pauliSite x (pauliMulIdx α β)) =
      ∑ γ : Fin 4, pauliSite x γ * A * pauliSite x γ := by
    intro α
    refine Finset.sum_bij (fun β _ ↦ pauliMulIdx α β) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ (fun _ _ ↦ rfl)
    · intro β₁ _ β₂ _ h
      fin_cases α <;> fin_cases β₁ <;> fin_cases β₂ <;> simp_all [pauliMulIdx]
    · intro γ _
      refine ⟨pauliMulIdx α γ, Finset.mem_univ _, ?_⟩
      fin_cases α <;> fin_cases γ <;> simp [pauliMulIdx]
  simp_rw [hbij]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1; norm_num

/-- **Exact Operator Bounds `0 ⪯ S ⪯ N • 1`** on concrete `QubitOp N`:
for every `M : QubitOp N`, `0 ≤ Re ⟨M, S M⟩_HS ≤ N * ‖M‖_HS²`. -/
theorem totalSizeOp_bounds {N : ℕ} (M : QubitOp N) :
    0 ≤ (hsInner M (totalSizeOp M)).re ∧
    (hsInner M (totalSizeOp M)).re ≤ (N : ℝ) * hsNormSq M := by
  constructor
  · rw [← eq_2_8_hs_commutator_size_identity M]
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg; intro x _
    apply Finset.sum_nonneg; intro α _
    exact hsNormSq_nn _
  · unfold totalSizeOp hsInner
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
    have hsite : ∀ x : Fin N, (Matrix.trace (Mᴴ * siteSizeOp x M)).re ≤ hsNormSq M := by
      intro x
      unfold siteSizeOp
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
      have hpos : 0 ≤ (Matrix.trace (Mᴴ * partialTraceSite x M)).re := by
        have h1 : hsInner M (partialTraceSite x M) =
            hsInner (partialTraceSite x M) (partialTraceSite x M) := by
          calc hsInner M (partialTraceSite x M)
              = hsInner M (partialTraceSite x (partialTraceSite x M)) := by
                rw [partialTraceSite_idempotent]
            _ = hsInner (partialTraceSite x M) (partialTraceSite x M) :=
                partialTraceSite_selfAdjoint x M _
        change (hsInner M (partialTraceSite x M)).re ≥ 0
        rw [h1]
        exact hsNormSq_nn _
      have hM : (Matrix.trace (Mᴴ * M)).re = hsNormSq M := rfl
      linarith
    calc ∑ x : Fin N, (Matrix.trace (Mᴴ * siteSizeOp x M)).re
        ≤ ∑ _x : Fin N, hsNormSq M := Finset.sum_le_sum fun x _ ↦ hsite x
      _ = (N : ℝ) * hsNormSq M := by simp

/-- Symmetry of the Hilbert–Schmidt size form: `Re ⟨A, S B⟩_HS = Re ⟨B, S A⟩_HS`. -/
theorem totalSizeOp_symm_re {N : ℕ} (A B : QubitOp N) :
    (hsInner A (totalSizeOp B)).re = (hsInner B (totalSizeOp A)).re := by
  have hsite : ∀ x : Fin N,
      (hsInner A (siteSizeOp x B)).re = (hsInner B (siteSizeOp x A)).re := by
    intro x
    have hsa : hsInner A (siteSizeOp x B) = hsInner (siteSizeOp x A) B := by
      unfold siteSizeOp hsInner
      rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.conjTranspose_sub, Matrix.sub_mul,
          Matrix.trace_sub]
      congr 1
      exact partialTraceSite_selfAdjoint x A B
    rw [hsa]
    have hconj : hsInner (siteSizeOp x A) B = star (hsInner B (siteSizeOp x A)) := by
      unfold hsInner
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [hconj, Complex.star_def, Complex.conj_re]
  unfold totalSizeOp hsInner
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun x _ ↦ hsite x

/-- Cauchy–Schwarz for the positive-semidefinite superoperator `totalSizeOp`:
`(Re ⟨A, S B⟩_HS)² ≤ Re ⟨A, S A⟩_HS * Re ⟨B, S B⟩_HS`. -/
theorem totalSizeOp_cauchy_schwarz {N : ℕ} (A B : QubitOp N) :
    ((hsInner A (totalSizeOp B)).re) ^ 2 ≤
      (hsInner A (totalSizeOp A)).re * (hsInner B (totalSizeOp B)).re := by
  set a := (hsInner A (totalSizeOp A)).re
  set b := (hsInner A (totalSizeOp B)).re
  set c := (hsInner B (totalSizeOp B)).re
  have hquad : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t + c := by
    intro t
    have hnn := (totalSizeOp_bounds ((t : ℂ) • A + B)).1
    have hlin : totalSizeOp ((t : ℂ) • A + B) = (t : ℂ) • totalSizeOp A + totalSizeOp B := by
      unfold totalSizeOp siteSizeOp partialTraceSite
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Finset.sum_add_distrib, ← Finset.smul_sum, smul_add, smul_sub, smul_comm (1 / 4 : ℂ) (t : ℂ)]
      abel
    rw [hlin] at hnn
    have hexp : (hsInner ((t : ℂ) • A + B) ((t : ℂ) • totalSizeOp A + totalSizeOp B)).re =
        a * t ^ 2 + 2 * b * t + c := by
      unfold hsInner
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
          Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
          Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul]
      simp only [Complex.add_re, smul_eq_mul, Complex.star_def, Complex.conj_ofReal,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      have hsym := totalSizeOp_symm_re A B
      change t * (t * a) + t * b + (t * (hsInner B (totalSizeOp A)).re + c) =
        a * t ^ 2 + 2 * b * t + c
      rw [← hsym]; ring
    linarith
  have ha : 0 ≤ a := (totalSizeOp_bounds A).1
  by_cases ha0 : a = 0
  · have hb0 : b = 0 := by
      by_contra hne
      have h := hquad (-(c + 1) / (2 * b))
      have h2b : 2 * b ≠ 0 := mul_ne_zero two_ne_zero hne
      have hsimp : a * (-(c + 1) / (2 * b)) ^ 2 + 2 * b * (-(c + 1) / (2 * b)) + c = -1 := by
        rw [ha0]; field_simp [h2b]; ring
      linarith
    rw [ha0, hb0]; norm_num
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h := hquad (-b / a)
    have hsimp : a * (-b / a) ^ 2 + 2 * b * (-b / a) + c = c - b ^ 2 / a := by
      field_simp [hapos.ne']; ring
    rw [hsimp] at h
    have h1 : b ^ 2 / a ≤ c := by linarith
    exact (div_le_iff₀ hapos).mp h1 |> fun h2 ↦ by linarith

/-- **Operator-Level Lemma 4.2 (Thermal-Size Truncation Inequality, Eq. 4.3)**:
Directly on concrete `QubitOp N`, for any operator split `O = A_M + R_M` with
`‖A_M‖_{β,W}² ≤ 1`, `‖R_M‖_{β,W}² ≤ δ`, and static bound
`mssThermalSize G A_M ≤ Λ_M * ‖A_M‖_{β,W}²` (`Λ_M ≥ 0`), proves from first principles
(using `totalSizeOp_bounds` and `totalSizeOp_cauchy_schwarz`) that
`mssThermalSize G O ≤ Λ_M + 2 √(N (Λ_M + B_bg) δ) + N δ`, where `B_bg = Re ⟨ρ^{1/2}, S ρ^{1/2}⟩_HS`. -/
theorem lemma_4_2_operator_thermal_size_truncation {N : ℕ} (G : GibbsData N)
    (O A_M R_M : QubitOp N) (Λ_M δ : ℝ)
    (hsplit : O = A_M + R_M)
    (hΛ : 0 ≤ Λ_M) (hδ : 0 ≤ δ)
    (hA_norm : hsNormSq (jBeta G.ρQuarter A_M) ≤ 1)
    (hR_norm : hsNormSq (jBeta G.ρQuarter R_M) ≤ δ)
    (hstat : (hsInner (jBeta G.ρQuarter A_M) (totalSizeOp (jBeta G.ρQuarter A_M))).re -
        (hsInner G.ρHalf (totalSizeOp G.ρHalf)).re ≤ Λ_M * hsNormSq (jBeta G.ρQuarter A_M)) :
    let Bbg := (hsInner G.ρHalf (totalSizeOp G.ρHalf)).re
    mssThermalSize G O ≤ Λ_M + 2 * Real.sqrt ((N : ℝ) * (Λ_M + Bbg) * δ) + (N : ℝ) * δ := by
  intro Bbg
  set MA := jBeta G.ρQuarter A_M
  set MR := jBeta G.ρQuarter R_M
  have hJO : jBeta G.ρQuarter O = MA + MR := by
    simp only [MA, MR, jBeta, hsplit, Matrix.mul_add, Matrix.add_mul]
  have hSadd : totalSizeOp (MA + MR) = totalSizeOp MA + totalSizeOp MR := by
    unfold totalSizeOp siteSizeOp partialTraceSite
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib, smul_add, add_sub_add_comm]
  have hexpand : (hsInner (jBeta G.ρQuarter O) (totalSizeOp (jBeta G.ρQuarter O))).re =
      (hsInner MA (totalSizeOp MA)).re + 2 * (hsInner MA (totalSizeOp MR)).re +
      (hsInner MR (totalSizeOp MR)).re := by
    rw [hJO, hSadd]
    have hsym := totalSizeOp_symm_re MA MR
    unfold hsInner at hsym ⊢
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        Matrix.trace_add, Matrix.trace_add, Matrix.trace_add]
    simp only [Complex.add_re]
    linarith
  have hA_le : (hsInner MA (totalSizeOp MA)).re ≤ Λ_M + Bbg := by
    have : Λ_M * hsNormSq MA ≤ Λ_M * 1 := mul_le_mul_of_nonneg_left hA_norm hΛ
    linarith
  have hR_le : (hsInner MR (totalSizeOp MR)).re ≤ (N : ℝ) * δ := by
    calc (hsInner MR (totalSizeOp MR)).re
        ≤ (N : ℝ) * hsNormSq MR := (totalSizeOp_bounds MR).2
      _ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_left hR_norm (Nat.cast_nonneg N)
  have hCS : (hsInner MA (totalSizeOp MR)).re ≤ Real.sqrt ((N : ℝ) * (Λ_M + Bbg) * δ) := by
    have hcs := totalSizeOp_cauchy_schwarz MA MR
    have hA_nn := (totalSizeOp_bounds MA).1
    have hR_nn := (totalSizeOp_bounds MR).1
    have hprod : (hsInner MA (totalSizeOp MA)).re * (hsInner MR (totalSizeOp MR)).re ≤
        (N : ℝ) * (Λ_M + Bbg) * δ := by
      have h1 : (hsInner MA (totalSizeOp MA)).re * (hsInner MR (totalSizeOp MR)).re ≤
          (Λ_M + Bbg) * ((N : ℝ) * δ) :=
        mul_le_mul hA_le hR_le hR_nn (by linarith [hA_nn])
      linarith
    have hsq : ((hsInner MA (totalSizeOp MR)).re) ^ 2 ≤ (N : ℝ) * (Λ_M + Bbg) * δ :=
      le_trans hcs hprod
    calc (hsInner MA (totalSizeOp MR)).re
        ≤ |((hsInner MA (totalSizeOp MR)).re)| := le_abs_self _
      _ = Real.sqrt (((hsInner MA (totalSizeOp MR)).re) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((N : ℝ) * (Λ_M + Bbg) * δ) := Real.sqrt_le_sqrt hsq
  unfold mssThermalSize
  rw [hexpand]
  linarith

end OperatorSizeBounds

section ConcreteWightmanProjectors

/-- Concrete Hilbert–Schmidt Euclidean space `HSOp N` isometric to `(QubitOp N, hsInner)`. -/
abbrev HSOp (N : ℕ) := EuclideanSpace ℂ ((Fin N → Fin 2) × (Fin N → Fin 2))

/-- Linear equivalence flattening `QubitOp N` into `HSOp N`. -/
noncomputable def toHSOp (N : ℕ) : QubitOp N ≃ₗ[ℂ] HSOp N where
  toFun M := WithLp.toLp 2 (fun p ↦ M p.1 p.2)
  invFun v := Matrix.of (fun r c ↦ v (r, c))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Linear map `toHSOp ∘ jBeta G.ρQuarter : QubitOp N →ₗ[ℂ] HSOp N` embedding the Wightman
space isometrically into `HSOp N`. -/
noncomputable def wightmanEmbed {N : ℕ} (G : GibbsData N) : QubitOp N →ₗ[ℂ] HSOp N where
  toFun A := toHSOp N (jBeta G.ρQuarter A)
  map_add' A B := by
    simp only [jBeta, Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c A := by
    simp only [jBeta, Matrix.mul_smul, Matrix.smul_mul, map_smul, RingHom.id_apply]

/-- Concrete Wightman filtration subspace `W_s^{(β)} := (toHSOp ∘ 𝒥_β)(V_s) ≤ HSOp N`. -/
noncomputable def wightmanFiltrationSubspace {N : ℕ} (G : GibbsData N) (s : ℕ) :
    Submodule ℂ (HSOp N) :=
  (filtrationSubmodule N s).map (wightmanEmbed G)

/-- Concrete Wightman orthogonal projector `Π_s^{(β)}` onto `W_s^{(β)}` in `HSOp N`. -/
noncomputable def wightmanProj {N : ℕ} (G : GibbsData N) (s : ℕ) :
    HSOp N →L[ℂ] HSOp N :=
  (wightmanFiltrationSubspace G s).starProjection

/-- **Exact Loewner Ordering of Orthogonal Projectors**:
Whenever `W₁ ≤ W₂` are subspaces of `HSOp N`, for every `v : HSOp N`,
`‖P_{W₁} v‖² ≤ ‖P_{W₂} v‖²`. -/
theorem loewner_proj_mono {N : ℕ} {W₁ W₂ : Submodule ℂ (HSOp N)} (hle : W₁ ≤ W₂)
    (v : HSOp N) :
    ‖W₁.starProjection v‖ ^ 2 ≤ ‖W₂.starProjection v‖ ^ 2 := by
  have horth : @inner ℂ (HSOp N) _
      (W₁.starProjection v) (W₂.starProjection v - W₁.starProjection v) = 0 := by
    have hmem1 : W₁.starProjection v ∈ W₁ := Submodule.starProjection_apply_mem W₁ v
    have hsub : W₂.starProjection v - W₁.starProjection v =
        (v - W₁.starProjection v) - (v - W₂.starProjection v) := by abel
    rw [hsub, inner_sub_right]
    have h_o1 : v - W₁.starProjection v ∈ W₁ᗮ :=
      Submodule.sub_starProjection_mem_orthogonal v
    have h_o2 : v - W₂.starProjection v ∈ W₂ᗮ :=
      Submodule.sub_starProjection_mem_orthogonal v
    have h1z : @inner ℂ (HSOp N) _ (W₁.starProjection v) (v - W₁.starProjection v) = 0 :=
      (Submodule.mem_orthogonal W₁ _).mp h_o1 _ hmem1
    have h2z : @inner ℂ (HSOp N) _ (W₁.starProjection v) (v - W₂.starProjection v) = 0 :=
      (Submodule.mem_orthogonal W₂ _).mp h_o2 _ (hle hmem1)
    rw [h1z, h2z, sub_self]
  have hpyth : ‖W₂.starProjection v‖ ^ 2 =
      ‖W₁.starProjection v‖ ^ 2 + ‖W₂.starProjection v - W₁.starProjection v‖ ^ 2 := by
    have hdecomp : W₂.starProjection v =
        W₁.starProjection v + (W₂.starProjection v - W₁.starProjection v) := by abel
    have hmul := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (W₁.starProjection v) (W₂.starProjection v - W₁.starProjection v) horth
    rw [← hdecomp] at hmul
    simp only [sq]
    exact hmul
  nlinarith [sq_nonneg ‖W₂.starProjection v - W₁.starProjection v‖]

/-- **Concrete Proposition 4.1 (Loewner Dominance `P_{K_k} ⪯ Π_{s₀ + (r-1)k}^{(β)}`)**:
For any `r`-local Hamiltonian `ham : LocalHamiltonian N r` (`r ≥ 1`), any `s₀`-local seed
`A ∈ filtrationSubmodule N s₀`, and any Krylov depth `k`, the Krylov subspace
`K_k = span { wightmanEmbed G (ad_H^j A) | j ≤ k }` is contained in `W_{s₀ + (r-1)k}^{(β)}`,
so its orthogonal projector is Loewner-dominated by `Π_{s₀ + (r-1)k}^{(β)}`. -/
theorem prop_4_1_loewner_dominance {N r s₀ : ℕ} (hr : 1 ≤ r)
    (G : GibbsData N) (ham : LocalHamiltonian N r) (A : QubitOp N)
    (hA : A ∈ filtrationSubmodule N s₀) (k : ℕ) (v : HSOp N) :
    let Kk : Submodule ℂ (HSOp N) :=
      Submodule.span ℂ {w | ∃ j ≤ k, w = wightmanEmbed G (iterMatCommQubit ham.totalOp j A)}
    ‖Kk.starProjection v‖ ^ 2 ≤
      ‖wightmanProj G (s₀ + (r - 1) * k) v‖ ^ 2 := by
  intro Kk
  apply loewner_proj_mono
  apply Submodule.span_le.mpr
  rintro w ⟨j, hj, rfl⟩
  refine ⟨iterMatCommQubit ham.totalOp j A, ?_, rfl⟩
  have hmem := prop_4_1_concrete_qubit_filtration hr ham A hA j
  have hle : s₀ + (r - 1) * j ≤ s₀ + (r - 1) * k :=
    Nat.add_le_add_left (Nat.mul_le_mul_left (r - 1) hj) s₀
  exact filtrationSubmodule_mono N hle hmem

end ConcreteWightmanProjectors

end KrylovChaos
