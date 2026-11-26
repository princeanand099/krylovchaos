/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.CausalNormBounds
import KrylovChaos.WightmanProjectors
import KrylovChaos.JacobiSemigroup
import KrylovChaos.SpectralMeasure
import KrylovChaos.BimodalExact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# End-to-End Concrete Operator Instantiations (Lemma 2.1 on `QubitOp N` & Theorem 1.1(b))

Unifies the concrete `N`-qubit operator algebra (`QubitOp N`) with the Banach-algebra
machinery (`CausalNormBounds`) and operator-level truncation (`WightmanProjectors`):
1. **Concrete Operator-Norm Representation `QubitOpCLM N`**:
   lifts `QubitOp N` to `EuclideanSpace ℂ (Fin N → Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin N → Fin 2)`
   with `[NormOneClass (QubitOpCLM N)]` (since `2^N ≥ 1` for all `N : ℕ`).
2. **Concrete `LocalInteractionDecomp (QubitOpCLM N) N r`** (`qubitLocalInteractionDecomp`):
   proves disjoint-support commutativity (`supportedSubmodule_comm_zero`) and support-union
   closure (`supportedSubmodule_comm_union`) directly on `QubitOp N`, instantiating
   `CausalNormBounds.lemma_2_1_single_site_exp_bound` (Eq. 2.4) and
   `CausalNormBounds.lemma_2_1_r_local_exp_bound` (Eq. 2.5) directly on `N`-qubit
   `r`-local Hamiltonians in exact operator norm `‖·‖_∞`.
3. **End-to-End Theorem 1.1(b) (`theorem_1_1b_end_to_end`)**:
   invokes `WightmanProjectors.lemma_4_2_operator_thermal_size_truncation` directly inside
   the proof to bound `mssThermalSize G O` from the Krylov tail `q ≤ exp(-θ M + A)` and
   static hypothesis `(H1)`.
-/

namespace KrylovChaos

open scoped Matrix

section QubitOperatorNormDecomp

/-- Concrete `N`-qubit Hilbert space `ℋ_N = (ℂ^2)^{⊗ N}` as `EuclideanSpace ℂ (Fin N → Fin 2)`. -/
abbrev QubitHilb (N : ℕ) := EuclideanSpace ℂ (Fin N → Fin 2)

/-- Concrete `N`-qubit operator algebra equipped with the exact Hilbert-space operator norm `‖·‖_∞`. -/
abbrev QubitOpCLM (N : ℕ) := QubitHilb N →L[ℂ] QubitHilb N

instance instNontrivialQubitHilb (N : ℕ) : Nontrivial (QubitHilb N) := by
  refine ⟨0, EuclideanSpace.single (fun _ ↦ 0) 1, ?_⟩
  intro h
  have := congrFun (congrArg WithLp.ofLp h) (fun _ ↦ 0)
  simp at this

instance instNormOneClassQubitOpCLM (N : ℕ) : NormOneClass (QubitOpCLM N) :=
  ⟨ContinuousLinearMap.norm_id⟩

/-- Lift a matrix `A : QubitOp N` to a bounded linear operator `QubitOpCLM N`. -/
noncomputable def qubitOpToCLM {N : ℕ} (A : QubitOp N) : QubitOpCLM N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ WithLp.toLp 2 (fun i ↦ ∑ j, A i j * v j)
      map_add' := fun u v ↦ by ext i; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v ↦ by ext i; simp [Finset.mul_sum, mul_left_comm] }

lemma qubitOpToCLM_zero (N : ℕ) : qubitOpToCLM (0 : QubitOp N) = 0 := by
  apply ContinuousLinearMap.ext; intro v; ext i; simp [qubitOpToCLM]

lemma qubitOpToCLM_sub {N : ℕ} (A B : QubitOp N) :
    qubitOpToCLM (A - B) = qubitOpToCLM A - qubitOpToCLM B := by
  apply ContinuousLinearMap.ext; intro v; ext i
  simp [qubitOpToCLM, sub_mul, Finset.sum_sub_distrib]

lemma qubitOpToCLM_mul {N : ℕ} (A B : QubitOp N) :
    qubitOpToCLM (A * B) = qubitOpToCLM A * qubitOpToCLM B := by
  apply ContinuousLinearMap.ext; intro v; ext i
  simp only [qubitOpToCLM, ContinuousLinearMap.mul_apply, LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  ring

/-- Submodule of `QubitOp N` consisting of operators supported on `U ⊆ Fin N`:
the `ℂ`-linear span of Pauli strings `pauliString a` whose support is contained in `U`. -/
def supportedSubmodule (N : ℕ) (U : Finset (Fin N)) : Submodule ℂ (QubitOp N) :=
  Submodule.span ℂ ((fun a : Fin N → Fin 4 ↦ pauliString a) ''
    {a : Fin N → Fin 4 | ∀ x : Fin N, a x ≠ 0 → x ∈ U})

/-- Two Pauli strings with disjoint supports commute. -/
lemma pauliString_comm_zero_of_disjoint {N : ℕ} {U₁ U₂ : Finset (Fin N)}
    (hdisj : Disjoint U₁ U₂) {a b : Fin N → Fin 4}
    (ha : ∀ x, a x ≠ 0 → x ∈ U₁) (hb : ∀ x, b x ≠ 0 → x ∈ U₂) :
    pauliString a * pauliString b - pauliString b * pauliString a = 0 := by
  have heq : pauliString a * pauliString b = pauliString b * pauliString a := by
    unfold pauliString
    rw [kronOp_mul, kronOp_mul]
    congr 1; funext x
    by_cases hax : a x = 0
    · rw [hax]; simp [pauliMat]
    · have hx1 : x ∈ U₁ := ha x hax
      have hbx : b x = 0 := by
        by_contra hne
        exact Finset.disjoint_left.mp hdisj hx1 (hb x hne)
      rw [hbx]; simp [pauliMat]
  rw [heq, sub_self]

/-- Product of two Pauli strings supported on `U₁` and `U₂` lies in `supportedSubmodule N (U₂ ∪ U₁)`. -/
lemma pauliString_mul_mem_union {N : ℕ} {U₁ U₂ : Finset (Fin N)}
    {a b : Fin N → Fin 4}
    (ha : ∀ x, a x ≠ 0 → x ∈ U₁) (hb : ∀ x, b x ≠ 0 → x ∈ U₂) :
    pauliString a * pauliString b ∈ supportedSubmodule N (U₂ ∪ U₁) := by
  -- Site-by-site Pauli multiplication: `pauliMat α * pauliMat β = c • pauliMat γ`
  have hsite : ∀ x : Fin N, ∃ (c : ℂ) (γ : Fin 4),
      pauliMat (a x) * pauliMat (b x) = c • pauliMat γ ∧
      (γ ≠ 0 → x ∈ U₂ ∪ U₁) := by
    intro x
    by_cases hax : a x = 0
    · refine ⟨1, b x, by rw [hax]; simp [pauliMat], fun hne ↦ Finset.mem_union_left _ (hb x hne)⟩
    · by_cases hbx : b x = 0
      · refine ⟨1, a x, by rw [hbx]; simp [pauliMat], fun hne ↦ Finset.mem_union_right _ (ha x hne)⟩
      · have hx : x ∈ U₂ ∪ U₁ := Finset.mem_union_right _ (ha x hax)
        -- Both `a x` and `b x` are in `{1, 2, 3}`
        generalize a x = α; generalize b x = β
        fin_cases α <;> fin_cases β
        all_goals
          first
          | exact ⟨1, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I], fun _ ↦ hx⟩
          | exact ⟨1, 1, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I], fun _ ↦ hx⟩
          | exact ⟨1, 2, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I], fun _ ↦ hx⟩
          | exact ⟨1, 3, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I], fun _ ↦ hx⟩
          | exact ⟨Complex.I, 3, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I], fun _ ↦ hx⟩
          | exact ⟨-Complex.I, 3, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I], fun _ ↦ hx⟩
          | exact ⟨Complex.I, 1, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I], fun _ ↦ hx⟩
          | exact ⟨-Complex.I, 1, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I], fun _ ↦ hx⟩
          | exact ⟨Complex.I, 2, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I], fun _ ↦ hx⟩
          | exact ⟨-Complex.I, 2, by ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMat, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I], fun _ ↦ hx⟩
  choose c γ hmul hsupp using hsite
  have hprod : pauliString a * pauliString b = (∏ x : Fin N, c x) • pauliString γ := by
    unfold pauliString
    rw [kronOp_mul]
    ext r s
    simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro x _
    rw [hmul x, Matrix.smul_apply, smul_eq_mul]
  rw [hprod]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, hsupp, rfl⟩)

/-- Disjoint-support operators in `QubitOp N` commute. -/
theorem supportedSubmodule_comm_zero {N : ℕ} {U₁ U₂ : Finset (Fin N)}
    (hdisj : Disjoint U₁ U₂) {A B : QubitOp N}
    (hA : A ∈ supportedSubmodule N U₁) (hB : B ∈ supportedSubmodule N U₂) :
    A * B - B * A = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨a, ha, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hB
    · rintro _ ⟨b, hb, rfl⟩
      exact pauliString_comm_zero_of_disjoint hdisj ha hb
    · simp
    · intro x y _ _ hx hy
      calc pauliString a * (x + y) - (x + y) * pauliString a
          = (pauliString a * x - x * pauliString a) + (pauliString a * y - y * pauliString a) := by
              simp only [Matrix.mul_add, Matrix.add_mul]; abel
        _ = 0 := by rw [hx, hy, add_zero]
    · intro c x _ hx
      calc pauliString a * (c • x) - (c • x) * pauliString a
          = c • (pauliString a * x - x * pauliString a) := by
              simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        _ = 0 := by rw [hx, smul_zero]
  · simp
  · intro x y _ _ hx hy
    calc (x + y) * B - B * (x + y)
        = (x * B - B * x) + (y * B - B * y) := by
            simp only [Matrix.add_mul, Matrix.mul_add]; abel
      _ = 0 := by rw [hx, hy, add_zero]
  · intro c x _ hx
    calc (c • x) * B - B * (c • x)
        = c • (x * B - B * x) := by
            simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
      _ = 0 := by rw [hx, smul_zero]

/-- Commutator of operators supported on `U₁` and `U₂` is supported on `U₂ ∪ U₁`. -/
theorem supportedSubmodule_comm_union {N : ℕ} {U₁ U₂ : Finset (Fin N)}
    {A B : QubitOp N}
    (hA : A ∈ supportedSubmodule N U₁) (hB : B ∈ supportedSubmodule N U₂) :
    A * B - B * A ∈ supportedSubmodule N (U₂ ∪ U₁) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨a, ha, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hB
    · rintro _ ⟨b, hb, rfl⟩
      have h1 : pauliString a * pauliString b ∈ supportedSubmodule N (U₂ ∪ U₁) :=
        pauliString_mul_mem_union ha hb
      have h2 : pauliString b * pauliString a ∈ supportedSubmodule N (U₂ ∪ U₁) := by
        rw [Finset.union_comm]; exact pauliString_mul_mem_union hb ha
      exact Submodule.sub_mem _ h1 h2
    · simp [Submodule.zero_mem]
    · intro x y _ _ hx hy
      have heq : pauliString a * (x + y) - (x + y) * pauliString a =
          (pauliString a * x - x * pauliString a) + (pauliString a * y - y * pauliString a) := by
        simp only [Matrix.mul_add, Matrix.add_mul]; abel
      rw [heq]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      have heq : pauliString a * (c • x) - (c • x) * pauliString a =
          c • (pauliString a * x - x * pauliString a) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
      rw [heq]; exact Submodule.smul_mem _ c hx
  · simp [Submodule.zero_mem]
  · intro x y _ _ hx hy
    have heq : (x + y) * B - B * (x + y) = (x * B - B * x) + (y * B - B * y) := by
      simp only [Matrix.add_mul, Matrix.mul_add]; abel
    rw [heq]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    have heq : (c • x) * B - B * (c • x) = c • (x * B - B * x) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    rw [heq]; exact Submodule.smul_mem _ c hx

/-- **Concrete `N`-Qubit `LocalInteractionDecomp` in Exact Operator Norm `‖·‖_∞`**:
Given any finite family of `r`-local interaction terms `term : ι → QubitOp N` supported on
`supp : ι → Finset (Fin N)` (`|supp i| ≤ r`), constructs a `LocalInteractionDecomp (QubitOpCLM N) N r`
so `CausalNormBounds.lemma_2_1_single_site_exp_bound` (Eq. 2.4) and
`CausalNormBounds.lemma_2_1_r_local_exp_bound` (Eq. 2.5) apply directly on `QubitOp N`. -/
noncomputable def qubitLocalInteractionDecomp {N r : ℕ} {ι : Type*} [Fintype ι]
    (term : ι → QubitOp N) (supp : ι → Finset (Fin N))
    (hcard : ∀ i, (supp i).card ≤ r)
    (hsupp : ∀ i, term i ∈ supportedSubmodule N (supp i)) :
    LocalInteractionDecomp (QubitOpCLM N) N r where
  ι := ι
  term := fun i ↦ qubitOpToCLM (term i)
  supp := supp
  supp_card_le := hcard
  SupportedOn := fun U T ↦ ∃ A : QubitOp N, A ∈ supportedSubmodule N U ∧ T = qubitOpToCLM A
  supportedOn_comm_zero := by
    rintro U i _ ⟨A, hA, rfl⟩ hdisj
    rw [← qubitOpToCLM_mul, ← qubitOpToCLM_mul, ← qubitOpToCLM_sub,
      supportedSubmodule_comm_zero hdisj (hsupp i) hA, qubitOpToCLM_zero]
  supportedOn_comm_union := by
    rintro U i _ ⟨A, hA, rfl⟩
    refine ⟨term i * A - A * term i, supportedSubmodule_comm_union (hsupp i) hA, ?_⟩
    rw [← qubitOpToCLM_mul, ← qubitOpToCLM_mul, ← qubitOpToCLM_sub]

end QubitOperatorNormDecomp

section EndToEndTheorem11b

/-- **End-to-End Theorem 1.1(b) (Operator-Level Static-to-Dynamical Thermal-Size Bound)**:
Directly invokes `WightmanProjectors.lemma_4_2_operator_thermal_size_truncation` inside the
proof (no `hH1` scalar-laundering!) to bound `mssThermalSize G O` on concrete `QubitOp N`
from:
- Operator truncation `O = A_M + R_M` (`‖O‖_W = 1`, `‖A_M‖_W² = 1 - q`, `‖R_M‖_W² = q`),
- Krylov tail bound `q ≤ exp(-θ M + A)` (from Theorem 1.1(a) / `JacobiSemigroup`), and
- Static hypothesis `(H1)` `mssThermalSize G A_M ≤ (1 - q) * (C₁ N^δ s_M^η + C₂)`. -/
theorem theorem_1_1b_end_to_end {N : ℕ} (G : GibbsData N)
    (O A_M R_M : QubitOp N) {q θ M A C₁ C₂ δ η s_M : ℝ}
    (hdecomp : O = A_M + R_M)
    (hnormO : (wightmanInner G O O).re = 1)
    (hnormA : (wightmanInner G A_M A_M).re = 1 - q)
    (hnormR : (wightmanInner G R_M R_M).re = q)
    (hq_nn : 0 ≤ q) (hq_le : q ≤ 1)
    (htail : q ≤ Real.exp (-(θ * M) + A))
    (hΛ_nn : 0 ≤ C₁ * (N : ℝ) ^ δ * s_M ^ η + C₂)
    (hH1_static : mssThermalSize G A_M ≤ (1 - q) * (C₁ * (N : ℝ) ^ δ * s_M ^ η + C₂)) :
    mssThermalSize G O ≤
    (C₁ * (N : ℝ) ^ δ * s_M ^ η + C₂) +
      2 * (N : ℝ) * Real.exp ((-(θ * M) + A) / 2) +
      (N : ℝ) * Real.exp (-(θ * M) + A) := by
  have hlem42 := lemma_4_2_operator_thermal_size_truncation G O A_M R_M
    hdecomp hnormO hnormA hnormR hq_nn hq_le hΛ_nn hH1_static
  have hsqrt_le : Real.sqrt q ≤ Real.exp ((-(θ * M) + A) / 2) := by
    have h1 := Real.sqrt_le_sqrt htail
    have h2 : Real.sqrt (Real.exp (-(θ * M) + A)) = Real.exp ((-(θ * M) + A) / 2) := by
      rw [← Real.exp_half]
      have heq : (Real.exp ((-(θ * M) + A) / 2)) ^ 2 = Real.exp (-(θ * M) + A) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      rw [← heq, Real.sqrt_sq (Real.exp_pos _).le]
    linarith
  have hN_nn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hterm1 : 2 * (N : ℝ) * Real.sqrt q ≤ 2 * (N : ℝ) * Real.exp ((-(θ * M) + A) / 2) :=
    mul_le_mul_of_nonneg_left hsqrt_le (by positivity)
  have hterm2 : (N : ℝ) * q ≤ (N : ℝ) * Real.exp (-(θ * M) + A) :=
    mul_le_mul_of_nonneg_left htail hN_nn
  linarith

end EndToEndTheorem11b

end KrylovChaos
