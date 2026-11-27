/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.CausalNormBounds
import KrylovChaos.WightmanProjectors
import KrylovChaos.GibbsConstruction
import KrylovChaos.JacobiSemigroup
import KrylovChaos.SpectralMeasure
import KrylovChaos.BimodalExact
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# End-to-End Concrete Operator Instantiations (Lemma 2.1 on `QubitOp N`, `NormedSpace.exp` Bridge & Theorem 1.1(b))

Unifies the concrete `N`-qubit operator algebra (`QubitOp N`) with the Banach-algebra
machinery (`CausalNormBounds`), spectral Heisenberg evolution (`GibbsConstruction`),
and operator-level truncation (`WightmanProjectors`):
1. **Concrete Operator-Norm Representation `QubitOpCLM N`**:
   lifts `QubitOp N` to `EuclideanSpace ℂ (Fin N → Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin N → Fin 2)`
   with `[NormOneClass (QubitOpCLM N)]` (since `2^N ≥ 1` for all `N : ℕ`).
2. **Item #27 (`NormedSpace.exp` Bridge for `complexPropagator` & `heisenbergEvol`)**:
   proves `qubitOpToCLM (complexPropagator hH z) = NormedSpace.exp ((Complex.I * z) • qubitOpToCLM H)`
   and `qubitOpToCLM (heisenbergEvol hH z O) = NormedSpace.exp ((Complex.I * z) • qubitOpToCLM H) *
   qubitOpToCLM O * NormedSpace.exp (-(Complex.I * z) • qubitOpToCLM H)`, directly wiring
   `CausalNormBounds.exp_conj_eq_tsum_adPow` and `lemma_2_1_*_exp_bound` to `heisenbergEvol hH z O`.
3. **Concrete `LocalInteractionDecomp (QubitOpCLM N) N r`** (`qubitLocalInteractionDecomp`):
   proves disjoint-support commutativity (`supportedSubmodule_comm_zero`) and support-union
   closure (`supportedSubmodule_comm_union`) directly on `QubitOp N` (using the canonical
   `ManyBodySetup.supportedSubmodule`), instantiating
   `CausalNormBounds.lemma_2_1_single_site_exp_bound` (Eq. 2.4) and
   `CausalNormBounds.lemma_2_1_r_local_exp_bound` (Eq. 2.5) directly on `N`-qubit
   `r`-local Hamiltonians in exact operator norm `‖·‖_∞`.
4. **End-to-End Theorem 1.1(b) (`theorem_1_1b_end_to_end`)**:
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

lemma qubitOpToCLM_one (N : ℕ) : qubitOpToCLM (1 : QubitOp N) = 1 := by
  apply ContinuousLinearMap.ext; intro v; ext i
  simp [qubitOpToCLM, Matrix.one_apply]

lemma qubitOpToCLM_add {N : ℕ} (A B : QubitOp N) :
    qubitOpToCLM (A + B) = qubitOpToCLM A + qubitOpToCLM B := by
  apply ContinuousLinearMap.ext; intro v; ext i
  simp [qubitOpToCLM, add_mul, Finset.sum_add_distrib]

lemma qubitOpToCLM_sub {N : ℕ} (A B : QubitOp N) :
    qubitOpToCLM (A - B) = qubitOpToCLM A - qubitOpToCLM B := by
  apply ContinuousLinearMap.ext; intro v; ext i
  simp [qubitOpToCLM, sub_mul, Finset.sum_sub_distrib]

lemma qubitOpToCLM_smul {N : ℕ} (c : ℂ) (A : QubitOp N) :
    qubitOpToCLM (c • A) = c • qubitOpToCLM A := by
  apply ContinuousLinearMap.ext; intro v; ext i
  simp [qubitOpToCLM, Finset.mul_sum, mul_assoc]

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

lemma qubitOpToCLM_pow {N : ℕ} (A : QubitOp N) (k : ℕ) :
    qubitOpToCLM (A ^ k) = (qubitOpToCLM A) ^ k := by
  induction k with
  | zero => simp [qubitOpToCLM_one]
  | succ k ih => rw [pow_succ, pow_succ, qubitOpToCLM_mul, ih]

private lemma hermFunc_smul_id {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (α : ℂ) :
    α • H = hermFunc hH (fun E ↦ α * (E : ℂ)) := by
  conv_lhs => rw [← hermFunc_id hH]
  unfold hermFunc
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1; congr 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

private lemma hermFunc_pow_smul {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (α : ℂ) (k : ℕ) :
    (α • H) ^ k = hermFunc hH (fun E ↦ (α * (E : ℂ)) ^ k) := by
  induction k with
  | zero => simp [hermFunc_one]
  | succ k ih =>
    rw [pow_succ, ih, hermFunc_smul_id hH α, hermFunc_mul]

/-- **Item #27 (Exact `NormedSpace.exp` Bridge for Spectral Exponentials on `QubitOp N`)**:
For ANY Hermitian `H : QubitOp N` and ANY `α : ℂ`:
`qubitOpToCLM (hermFunc hH (fun E ↦ Complex.exp (α * (E : ℂ)))) = NormedSpace.exp (α • qubitOpToCLM H)`. -/
theorem qubitOpToCLM_hermFunc_exp {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (α : ℂ) :
    qubitOpToCLM (hermFunc hH (fun E ↦ Complex.exp (α * (E : ℂ)))) =
      NormedSpace.exp (α • qubitOpToCLM H) := by
  apply ContinuousLinearMap.ext; intro v
  ext i
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  have hsumm : Summable (fun k : ℕ ↦ (k.factorial : ℂ)⁻¹ • (α • qubitOpToCLM H) ^ k) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
      (Real.summable_pow_div_factorial ‖α • qubitOpToCLM H‖)
    intro k
    rw [norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le _ k) (by positivity)
  let Φ : QubitOpCLM N →L[ℂ] ℂ :=
    LinearMap.mkContinuous
      { toFun := fun T ↦ (T v) i
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      ‖v‖
      (fun T ↦ by
        calc ‖(T v) i‖ ≤ ‖T v‖ := PiLp.norm_apply_le (T v) i
          _ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
          _ = ‖v‖ * ‖T‖ := mul_comm _ _)
  have hΦ : ((∑' k : ℕ, (k.factorial : ℂ)⁻¹ • (α • qubitOpToCLM H) ^ k) v) i =
      ∑' k : ℕ, (k.factorial : ℂ)⁻¹ * (((α • qubitOpToCLM H) ^ k) v) i := by
    have h1 := Φ.map_tsum hsumm
    simp only [map_smul, smul_eq_mul] at h1
    exact h1
  rw [hΦ]
  have hclm_herm : ∀ f : ℝ → ℂ, (qubitOpToCLM (hermFunc hH f) v) i =
      ∑ r : QubitIdx N, ∑ m : QubitIdx N,
        (hH.eigenvectorUnitary : QubitOp N) i m * f (hH.eigenvalues m) *
          (hH.eigenvectorUnitary : QubitOp N)ᴴ m r * v r := by
    intro f
    simp only [qubitOpToCLM, hermFunc, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
      AddHom.coe_mk, WithLp.ofLp_toLp, Matrix.mul_apply, Matrix.diagonal_apply, ite_mul,
      mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, Finset.sum_mul]
  have hterm : ∀ k : ℕ,
      (k.factorial : ℂ)⁻¹ * (((α • qubitOpToCLM H) ^ k) v) i =
        ∑ r : QubitIdx N, ∑ m : QubitIdx N,
          ((hH.eigenvectorUnitary : QubitOp N) i m *
            (hH.eigenvectorUnitary : QubitOp N)ᴴ m r * v r) *
            ((α * (hH.eigenvalues m : ℂ)) ^ k / (k.factorial : ℂ)) := by
    intro k
    rw [← qubitOpToCLM_smul, ← qubitOpToCLM_pow, hermFunc_pow_smul hH α k, hclm_herm,
      Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    ring
  simp_rw [hterm]
  have hs_cplx : ∀ z : ℂ, Summable (fun k : ℕ ↦ z ^ k / (k.factorial : ℂ)) := fun z ↦ by
    apply Summable.of_norm
    simpa [norm_div, norm_pow, Complex.norm_natCast] using Real.summable_pow_div_factorial ‖z‖
  rw [Summable.tsum_finsetSum (fun r _ ↦ summable_sum fun m _ ↦
    (hs_cplx (α * (hH.eigenvalues m : ℂ))).mul_left _)]
  rw [hclm_herm]
  apply Finset.sum_congr rfl; intro r _
  rw [Summable.tsum_finsetSum (fun m _ ↦
    (hs_cplx (α * (hH.eigenvalues m : ℂ))).mul_left _)]
  apply Finset.sum_congr rfl; intro m _
  rw [tsum_mul_left, ← NormedSpace.exp_eq_tsum_div, ← Complex.exp_eq_exp_ℂ]
  ring

/-- **Item #27**: `complexPropagator hH z` agrees identically with `NormedSpace.exp ((i z) • H)` in `QubitOpCLM N`. -/
theorem qubitOpToCLM_complexPropagator {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian) (z : ℂ) :
    qubitOpToCLM (complexPropagator hH z) = NormedSpace.exp ((Complex.I * z) • qubitOpToCLM H) :=
  qubitOpToCLM_hermFunc_exp hH (Complex.I * z)

/-- **Item #27**: `heisenbergEvol hH z O` agrees identically with Banach-algebra conjugation
`exp(i z H) * O * exp(-i z H)` in `QubitOpCLM N`. -/
theorem qubitOpToCLM_heisenbergEvol {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (z : ℂ) (O : QubitOp N) :
    qubitOpToCLM (heisenbergEvol hH z O) =
      NormedSpace.exp ((Complex.I * z) • qubitOpToCLM H) * qubitOpToCLM O *
        NormedSpace.exp (-((Complex.I * z) • qubitOpToCLM H)) := by
  unfold heisenbergEvol
  rw [qubitOpToCLM_mul, qubitOpToCLM_mul, qubitOpToCLM_complexPropagator hH z,
    qubitOpToCLM_complexPropagator hH (-z), mul_neg, neg_smul]

/-- **Item #27 (Exact Baker–Campbell–Hausdorff / `ad_H` Power Series for `heisenbergEvol`)**:
Directly wires `GibbsConstruction.heisenbergEvol` to `CausalNormBounds.exp_conj_eq_tsum_adPow`! -/
theorem qubitOpToCLM_heisenbergEvol_eq_tsum_adPow {N : ℕ} {H : QubitOp N} (hH : H.IsHermitian)
    (z : ℂ) (O : QubitOp N) :
    qubitOpToCLM (heisenbergEvol hH z O) =
      ∑' m : ℕ, ((Complex.I * z) ^ m / (m.factorial : ℂ)) •
        adPow (qubitOpToCLM H) (qubitOpToCLM O) m := by
  rw [qubitOpToCLM_heisenbergEvol hH z O]
  have h := exp_conj_eq_tsum_adPow (qubitOpToCLM H) (qubitOpToCLM O) (Complex.I * z)
  simpa [neg_smul] using h

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

private def pauliMulIdxE : Fin 4 → Fin 4 → Fin 4
  | 0, β => β
  | α, 0 => α
  | 1, 1 => 0
  | 2, 2 => 0
  | 3, 3 => 0
  | 1, 2 => 3
  | 2, 1 => 3
  | 2, 3 => 1
  | 3, 2 => 1
  | 3, 1 => 2
  | 1, 3 => 2
  | _, _ => 0

private def pauliMulPhaseE : Fin 4 → Fin 4 → ℂ
  | 1, 2 => Complex.I
  | 2, 3 => Complex.I
  | 3, 1 => Complex.I
  | 2, 1 => -Complex.I
  | 3, 2 => -Complex.I
  | 1, 3 => -Complex.I
  | _, _ => 1

private lemma pauliMat_mul_eqE (α β : Fin 4) :
    pauliMat α * pauliMat β = pauliMulPhaseE α β • pauliMat (pauliMulIdxE α β) := by
  fin_cases α <;> fin_cases β <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMat, pauliMulIdxE, pauliMulPhaseE, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.I_mul_I]

/-- Product of two Pauli strings supported on `U₁` and `U₂` lies in `supportedSubmodule N (U₂ ∪ U₁)`. -/
lemma pauliString_mul_mem_union {N : ℕ} {U₁ U₂ : Finset (Fin N)}
    {a b : Fin N → Fin 4}
    (ha : ∀ x, a x ≠ 0 → x ∈ U₁) (hb : ∀ x, b x ≠ 0 → x ∈ U₂) :
    pauliString a * pauliString b ∈ supportedSubmodule N (U₂ ∪ U₁) := by
  have hsupp : ∀ x : Fin N, pauliMulIdxE (a x) (b x) ≠ 0 → x ∈ U₂ ∪ U₁ := by
    intro x hne
    by_cases hax : a x = 0
    · rw [hax] at hne
      have hbx : b x ≠ 0 := by simpa [pauliMulIdxE] using hne
      exact Finset.mem_union_left _ (hb x hbx)
    · exact Finset.mem_union_right _ (ha x hax)
  have hsupp' : ∀ x ∉ U₂ ∪ U₁, pauliMulIdxE (a x) (b x) = 0 := by
    intro x hx
    by_contra hne
    exact hx (hsupp x hne)
  have hprod : pauliString a * pauliString b =
      (∏ x : Fin N, pauliMulPhaseE (a x) (b x)) •
        pauliString (fun x ↦ pauliMulIdxE (a x) (b x)) := by
    unfold pauliString
    rw [kronOp_mul]
    ext r s
    simp only [kronOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro x _
    rw [pauliMat_mul_eqE (a x) (b x), Matrix.smul_apply, smul_eq_mul]
  rw [hprod]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨fun x ↦ pauliMulIdxE (a x) (b x), hsupp', rfl⟩)

/-- Disjoint-support operators in `QubitOp N` commute. -/
theorem supportedSubmodule_comm_zero {N : ℕ} {U₁ U₂ : Finset (Fin N)}
    (hdisj : Disjoint U₁ U₂) {A B : QubitOp N}
    (hA : A ∈ supportedSubmodule N U₁) (hB : B ∈ supportedSubmodule N U₂) :
    A * B - B * A = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hA
  · rintro _ ⟨a, ha, rfl⟩
    have ha' : ∀ x, a x ≠ 0 → x ∈ U₁ := fun x hne ↦ by_contra fun hx ↦ hne (ha x hx)
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hB
    · rintro _ ⟨b, hb, rfl⟩
      have hb' : ∀ x, b x ≠ 0 → x ∈ U₂ := fun x hne ↦ by_contra fun hx ↦ hne (hb x hx)
      exact pauliString_comm_zero_of_disjoint hdisj ha' hb'
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
    have ha' : ∀ x, a x ≠ 0 → x ∈ U₁ := fun x hne ↦ by_contra fun hx ↦ hne (ha x hx)
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hB
    · rintro _ ⟨b, hb, rfl⟩
      have hb' : ∀ x, b x ≠ 0 → x ∈ U₂ := fun x hne ↦ by_contra fun hx ↦ hne (hb x hx)
      have h1 : pauliString a * pauliString b ∈ supportedSubmodule N (U₂ ∪ U₁) :=
        pauliString_mul_mem_union ha' hb'
      have h2 : pauliString b * pauliString a ∈ supportedSubmodule N (U₂ ∪ U₁) := by
        rw [Finset.union_comm]; exact pauliString_mul_mem_union hb' ha'
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
- Operator truncation `O = A_M + R_M` (`‖A_M‖_W² = 1 - q`, `‖R_M‖_W² = q`),
- Krylov tail bound `q ≤ exp(-θ M + A)` (from Theorem 1.1(a) / `JacobiSemigroup`), and
- Static hypothesis `(H1)` `mssThermalSize G A_M ≤ (1 - q) * (C₁ N^δ s_M^η + C₂)`. -/
theorem theorem_1_1b_end_to_end {N : ℕ} (G : GibbsData N)
    (hQsq : G.ρQuarter * G.ρQuarter = G.ρHalf)
    (O A_M R_M : QubitOp N) {q θ M A C₁ C₂ δ η s_M : ℝ}
    (hdecomp : O = A_M + R_M)
    (hnormA : (wightmanInner G.ρHalf A_M A_M).re = 1 - q)
    (hnormR : (wightmanInner G.ρHalf R_M R_M).re = q)
    (hq_nn : 0 ≤ q) (hq_le : q ≤ 1)
    (htail : q ≤ Real.exp (-(θ * M) + A))
    (hΛ_nn : 0 ≤ C₁ * (N : ℝ) ^ δ * s_M ^ η + C₂)
    (hH1_static : mssThermalSize G A_M ≤ (1 - q) * (C₁ * (N : ℝ) ^ δ * s_M ^ η + C₂)) :
    mssThermalSize G O ≤
    (C₁ * (N : ℝ) ^ δ * s_M ^ η + C₂) +
      2 * (N : ℝ) * Real.exp ((-(θ * M) + A) / 2) +
      (N : ℝ) * Real.exp (-(θ * M) + A) := by
  have hlem42 := lemma_4_2_operator_thermal_size_truncation G hQsq O A_M R_M
    hdecomp hnormA hnormR hq_nn hq_le hΛ_nn hH1_static
  have hsqrt_le : Real.sqrt q ≤ Real.exp ((-(θ * M) + A) / 2) := by
    have h1 := Real.sqrt_le_sqrt htail
    have h2 : Real.sqrt (Real.exp (-(θ * M) + A)) = Real.exp ((-(θ * M) + A) / 2) := by
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
