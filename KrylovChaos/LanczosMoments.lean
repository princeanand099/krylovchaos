/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.SpectralDyck
import Mathlib.Data.Matrix.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic

/-!
# Concrete Tridiagonal Jacobi Matrix, Dyck-Path Moment Expansion & Meixner `sech` Bound

Closes the remaining Section 5 gaps from ground up without scalar assumptions:
1. Concrete `D × D` symmetric tridiagonal Jacobi matrix `jacobiMat D b`.
2. **Exact Dyck-Path Moment Expansion**:
   `((jacobiMat D b) ^ (2 * n)) 0 0 = ∑_{γ ∈ 𝒟_{2n}} pathWeight b n γ`
   (`jacobiMat_moment_eq_dyck_sum`), proved by induction on step length for general
   finite-height lattice paths (`jacobiMat_pow_eq_sum_finPaths`).
3. **Full Summed Lemma 5.1 Moment Lower Bound** (`lemma_5_1_moment_lower_bound`):
   combines `jacobiMat_moment_eq_dyck_sum`, `shiftDyckPath_injective`, and
   `lemma_5_1_path_weight_lower` to prove directly on matrix powers:
   `(∏_{h=1}^{N₀} b_h²) * (T_Meixner^{2(n - N₀)})_{0,0} ≤ (T^{2n})_{0,0}`.
4. **Ground-Up Meixner `sech` Moment Lower Bound (Eq. 5.5)** (`meixner_sech_moment_lower_bound`):
   evaluates `∫_0^∞ ω^{2m} e^{-a ω} dω = (2m)! / a^{2m+1}` via Mathlib's Gamma integral
   and bounds `e^{-x} ≤ (cosh x)⁻¹` on `[0, ∞)` to prove Eq. (5.5) unconditionally.
-/

namespace KrylovChaos

open scoped Classical Matrix

section JacobiDyckExpansion

/-- Concrete `D × D` real symmetric tridiagonal Jacobi matrix with zero diagonal and
off-diagonal entries `b 1, b 2, ..., b (D - 1)`. -/
def jacobiMat (D : ℕ) (b : ℕ → ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun i j ↦
    if j.1 = i.1 + 1 then b (i.1 + 1)
    else if i.1 = j.1 + 1 then b (j.1 + 1)
    else 0

theorem jacobiMat_transpose (D : ℕ) (b : ℕ → ℝ) :
    (jacobiMat D b)ᵀ = jacobiMat D b := by
  ext i j
  simp only [Matrix.transpose_apply, jacobiMat, Matrix.of_apply]
  split_ifs <;> try rfl
  all_goals omega

/-- Finite-height lattice path of length `m` starting at `0` and ending at `h : Fin D`,
with each step changing height by `±1`. -/
def isFinPath {D : ℕ} (m : ℕ) (h : Fin D) (γ : Fin (m + 1) → Fin D) : Prop :=
  (γ ⟨0, by omega⟩).1 = 0 ∧
  γ ⟨m, by omega⟩ = h ∧
  ∀ k : Fin m, (γ ⟨k.1 + 1, by omega⟩).1 = (γ ⟨k.1, by omega⟩).1 + 1 ∨
               (γ ⟨k.1, by omega⟩).1 = (γ ⟨k.1 + 1, by omega⟩).1 + 1

/-- Weight of a finite-height lattice path `γ : Fin (m + 1) → Fin D`. -/
def finPathWeight {D : ℕ} (b : ℕ → ℝ) (m : ℕ) (γ : Fin (m + 1) → Fin D) : ℝ :=
  ∏ k : Fin m, b (max (γ ⟨k.1, by omega⟩).1 (γ ⟨k.1 + 1, by omega⟩).1)

private def appendPath {D : ℕ} {m : ℕ} (γ : Fin (m + 1) → Fin D) (h : Fin D) :
    Fin (m + 2) → Fin D :=
  fun k ↦ if hk : k.1 ≤ m then γ ⟨k.1, by omega⟩ else h

private def initPath {D : ℕ} {m : ℕ} (γ' : Fin (m + 2) → Fin D) :
    Fin (m + 1) → Fin D :=
  fun k ↦ γ' ⟨k.1, by omega⟩

private lemma finPathWeight_append {D : ℕ} (b : ℕ → ℝ) (m : ℕ)
    (γ : Fin (m + 1) → Fin D) (h : Fin D) :
    finPathWeight b (m + 1) (appendPath γ h) =
      finPathWeight b m γ * b (max (γ ⟨m, by omega⟩).1 h.1) := by
  unfold finPathWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro k _
    have hk1 : k.1 ≤ m := by omega
    have hk2 : k.1 + 1 ≤ m := by omega
    simp only [Fin.val_castSucc, appendPath, hk1, hk2, ↓reduceDIte]
  · have hm1 : m ≤ m := le_refl m
    have hm2 : ¬ (m + 1 ≤ m) := by omega
    simp only [Fin.val_last, appendPath, hm1, hm2, ↓reduceDIte]

/-- **Lattice-Path Expansion of Jacobi Matrix Powers**:
For every `D > 0`, `m : ℕ`, and `h : Fin D`,
`((jacobiMat D b) ^ m) 0 h = ∑_{γ : 0 → h of length m} finPathWeight b m γ`. -/
theorem jacobiMat_pow_eq_sum_finPaths {D : ℕ} (hD : 0 < D) (b : ℕ → ℝ) :
    ∀ (m : ℕ) (h : Fin D),
      ((jacobiMat D b) ^ m) ⟨0, hD⟩ h =
      ∑ γ ∈ Finset.univ.filter (isFinPath m h), finPathWeight b m γ
  | 0, h => by
    simp only [pow_zero, Matrix.one_apply, finPathWeight, Finset.univ_eq_empty, Finset.prod_empty,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    by_cases hh : (⟨0, hD⟩ : Fin D) = h
    · subst hh
      have hcard : (Finset.univ.filter (isFinPath 0 ⟨0, hD⟩)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨fun _ ↦ ⟨0, hD⟩, ?_⟩
        ext γ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, isFinPath]
        constructor
        · rintro ⟨_, h2, _⟩
          ext k
          have hk : k = ⟨0, by omega⟩ := Fin.ext (by omega)
          rw [hk, h2]
        · intro hγ; subst hγ; exact ⟨rfl, rfl, fun k ↦ Fin.elim0 k⟩
      simp [hcard]
    · have hempty : Finset.univ.filter (isFinPath 0 h) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro γ _ ⟨h1, h2, _⟩
        have hval : (0 : ℕ) = h.1 := by rw [← h1, h2]
        exact hh (Fin.ext hval)
      simp [hh, hempty]
  | m + 1, h => by
    rw [pow_succ, Matrix.mul_apply]
    have hIH : ∀ j : Fin D, ((jacobiMat D b) ^ m) ⟨0, hD⟩ j =
        ∑ γ ∈ Finset.univ.filter (isFinPath m j), finPathWeight b m γ :=
      fun j ↦ jacobiMat_pow_eq_sum_finPaths hD b m j
    simp_rw [hIH, Finset.sum_mul]
    have hsig :
        (∑ j : Fin D, ∑ γ ∈ Finset.univ.filter (isFinPath m j),
          finPathWeight b m γ * jacobiMat D b j h) =
        ∑ p ∈ Finset.univ.sigma (fun j : Fin D ↦ Finset.univ.filter (isFinPath m j)),
          finPathWeight b m p.2 * jacobiMat D b p.1 h :=
      (Finset.sum_sigma (Finset.univ : Finset (Fin D))
        (fun j ↦ Finset.univ.filter (isFinPath m j))
        (fun p ↦ finPathWeight b m p.2 * jacobiMat D b p.1 h)).symm
    rw [hsig]
    have hadj : ∀ j : Fin D,
        jacobiMat D b j h =
          if h.1 = j.1 + 1 ∨ j.1 = h.1 + 1 then b (max j.1 h.1) else 0 := by
      intro j
      unfold jacobiMat
      simp only [Matrix.of_apply]
      by_cases h1 : h.1 = j.1 + 1
      · have hmax : max j.1 h.1 = j.1 + 1 := by omega
        simp [h1, hmax]
      · by_cases h2 : j.1 = h.1 + 1
        · have hmax : max j.1 h.1 = h.1 + 1 := by omega
          simp [h1, h2, hmax]
          intro hc; omega
        · simp [h1, h2]
    simp_rw [hadj]
    have hfilt :
        ∑ p ∈ Finset.univ.sigma (fun j : Fin D ↦ Finset.univ.filter (isFinPath m j)),
          finPathWeight b m p.2 *
            (if h.1 = p.1.1 + 1 ∨ p.1.1 = h.1 + 1 then b (max p.1.1 h.1) else 0) =
        ∑ p ∈ (Finset.univ.sigma (fun j : Fin D ↦ Finset.univ.filter (isFinPath m j))).filter
            (fun p ↦ h.1 = p.1.1 + 1 ∨ p.1.1 = h.1 + 1),
          finPathWeight b m p.2 * b (max p.1.1 h.1) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> simp
    rw [hfilt]
    refine Finset.sum_bij (fun p _ ↦ appendPath p.2 h) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and] at hp ⊢
      obtain ⟨⟨h0, hm_end, hsteps⟩, hadj_p⟩ := hp
      refine ⟨?_, ?_, ?_⟩
      · simp only [appendPath, Nat.zero_le, ↓reduceDIte]; exact h0
      · simp only [appendPath, show ¬ (m + 1 ≤ m) by omega, ↓reduceDIte]
      · intro k
        by_cases hk : k.1 < m
        · have h1 : k.1 ≤ m := by omega
          have h2 : k.1 + 1 ≤ m := by omega
          simp only [appendPath, h1, h2, ↓reduceDIte]
          exact hsteps ⟨k.1, hk⟩
        · have hkeq : k.1 = m := by omega
          have h1 : k.1 ≤ m := by omega
          have h2 : ¬ (k.1 + 1 ≤ m) := by omega
          simp only [appendPath, h1, h2, ↓reduceDIte]
          have hkm : p.2 ⟨k.1, by omega⟩ = p.1 := by
            convert hm_end using 2; exact Fin.ext hkeq
          rw [hkm]; exact hadj_p
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and] at hp₁ hp₂
      have hγ : p₁.2 = p₂.2 := by
        ext k
        have hk := congrFun heq ⟨k.1, by omega⟩
        simp only [appendPath, show k.1 ≤ m by omega, ↓reduceDIte] at hk
        exact congrArg Fin.val hk
      have hj : p₁.1 = p₂.1 := by
        rw [← hp₁.1.2.1, ← hp₂.1.2.1, hγ]
      exact Sigma.ext hj (heq_of_eq hγ)
    · intro γ' hγ'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ'
      obtain ⟨h0, hm1, hsteps⟩ := hγ'
      set j := γ' ⟨m, by omega⟩
      refine ⟨⟨j, initPath γ'⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and]
        refine ⟨⟨h0, rfl, fun k ↦ hsteps ⟨k.1, by omega⟩⟩, ?_⟩
        have hs := hsteps ⟨m, by omega⟩
        rw [hm1] at hs
        exact hs
      · ext k
        by_cases hk : k.1 ≤ m
        · simp only [appendPath, initPath, hk, ↓reduceDIte]
        · have hkeq : k = ⟨m + 1, by omega⟩ := Fin.ext (by dsimp; omega)
          simp only [appendPath, hk, ↓reduceDIte]
          rw [hkeq, hm1]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and] at hp
      rw [finPathWeight_append, hp.1.2.1]

/-- Every Dyck path of length `2n` stays at height `≤ n`. -/
lemma isDyckPath_le_n {n : ℕ} {γ : Fin (2 * n + 1) → ℕ} (hγ : isDyckPath n γ) :
    ∀ k : Fin (2 * n + 1), γ k ≤ n := by
  have hup : ∀ j : ℕ, (hj : j ≤ 2 * n) → γ ⟨j, by omega⟩ ≤ j := by
    intro j
    induction j with
    | zero => intro _; rw [hγ.1]
    | succ j ih =>
      intro hj
      have hstep := hγ.2.2 ⟨j, by omega⟩
      dsimp only at hstep
      have hprev := ih (by omega)
      omega
  have hdn : ∀ d : ℕ, (hd : d ≤ 2 * n) → γ ⟨2 * n - d, by omega⟩ ≤ d := by
    intro d
    induction d with
    | zero =>
      intro _
      have h0 : γ ⟨2 * n - 0, by omega⟩ = 0 := by convert hγ.2.1 using 2
      omega
    | succ d ih =>
      intro hd
      have hstep := hγ.2.2 ⟨2 * n - (d + 1), by omega⟩
      dsimp only at hstep
      have hprev := ih (by omega)
      have hidx : 2 * n - (d + 1) + 1 = 2 * n - d := by omega
      have hsame : γ ⟨2 * n - (d + 1) + 1, by omega⟩ = γ ⟨2 * n - d, by omega⟩ := by
        congr 1; exact Fin.ext hidx
      rw [hsame] at hstep
      omega
  intro k
  by_cases hk : k.1 ≤ n
  · exact le_trans (hup k.1 (by omega)) hk
  · have h1 := hdn (2 * n - k.1) (by omega)
    have h2 : γ ⟨2 * n - (2 * n - k.1), by omega⟩ = γ k := by
      congr 1; exact Fin.ext (by dsimp; omega)
    rw [h2] at h1
    omega

/-- **Exact Dyck-Path Moment Expansion**:
For `n < D`, the `2n`-th diagonal moment `((jacobiMat D b) ^ (2 * n)) 0 0` equals the sum of
`pathWeight b n` over all Dyck paths of length `2n` in `Fin (2 * n + 1) → Fin D`. -/
theorem jacobiMat_moment_eq_dyck_sum {D n : ℕ} (hD : n < D) (b : ℕ → ℝ) :
    ((jacobiMat D b) ^ (2 * n)) ⟨0, by omega⟩ ⟨0, by omega⟩ =
    ∑ γ ∈ Finset.univ.filter (fun γ : Fin (2 * n + 1) → Fin D ↦ isDyckPath n (fun k ↦ (γ k).1)),
      pathWeight b n (fun k ↦ (γ k).1) := by
  rw [jacobiMat_pow_eq_sum_finPaths (by omega) b (2 * n) ⟨0, by omega⟩]
  have hfilt :
      Finset.univ.filter (isFinPath (2 * n) ⟨0, by omega⟩) =
      Finset.univ.filter (fun γ : Fin (2 * n + 1) → Fin D ↦ isDyckPath n (fun k ↦ (γ k).1)) := by
    apply Finset.ext
    intro γ
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, isFinPath, isDyckPath]
    exact ⟨fun ⟨h0, hend, hsteps⟩ ↦ ⟨h0, congrArg Fin.val hend, hsteps⟩,
           fun ⟨h0, hend, hsteps⟩ ↦ ⟨h0, Fin.ext hend, hsteps⟩⟩
  rw [hfilt]
  rfl

/-- **Full Summed Lemma 5.1 Moment Lower Bound** (Eq. 5.4 directly on Jacobi matrix powers):
If `b h > 0` for all `h ≥ 1`, `b h ≥ α₁ h` for all `h ≥ N₀`, and `N₀ ≤ n < D`, then
`(∏_{h=1}^{N₀} b_h²) * ((jacobiMat D (fun h ↦ α₁ * h)) ^ (2 * (n - N₀))) 0 0 ≤
  ((jacobiMat D b) ^ (2 * n)) 0 0`. -/
theorem lemma_5_1_moment_lower_bound {D n N₀ : ℕ} {α₁ : ℝ}
    (b : ℕ → ℝ) (hN₀ : N₀ ≤ n) (hD : n < D) (hα₁ : 0 < α₁)
    (hb_pos : ∀ h ≥ 1, 0 < b h)
    (hb_ge : ∀ h ≥ N₀, α₁ * (h : ℝ) ≤ b h) :
    (∏ h ∈ Finset.Icc 1 N₀, (b h) ^ 2) *
      ((jacobiMat D (fun h ↦ α₁ * (h : ℝ))) ^ (2 * (n - N₀))) ⟨0, by omega⟩ ⟨0, by omega⟩ ≤
    ((jacobiMat D b) ^ (2 * n)) ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  rw [jacobiMat_moment_eq_dyck_sum hD b,
      jacobiMat_moment_eq_dyck_sum (by omega : n - N₀ < D) (fun h ↦ α₁ * (h : ℝ)),
      Finset.mul_sum]
  let S₁ := Finset.univ.filter
    (fun γ : Fin (2 * (n - N₀) + 1) → Fin D ↦ isDyckPath (n - N₀) (fun k ↦ (γ k).1))
  let S₂ := Finset.univ.filter
    (fun γ : Fin (2 * n + 1) → Fin D ↦ isDyckPath n (fun k ↦ (γ k).1))
  let f : (Fin (2 * (n - N₀) + 1) → Fin D) → (Fin (2 * n + 1) → Fin D) :=
    fun γ k ↦
      if h : shiftDyckPath hN₀ (fun j ↦ (γ j).1) k < D then
        ⟨shiftDyckPath hN₀ (fun j ↦ (γ j).1) k, h⟩
      else ⟨0, by omega⟩
  have hf_lt : ∀ γ ∈ S₁, ∀ k : Fin (2 * n + 1),
      shiftDyckPath hN₀ (fun j ↦ (γ j).1) k < D := by
    intro γ hγ k
    have hdyck : isDyckPath (n - N₀) (fun j ↦ (γ j).1) := (Finset.mem_filter.mp hγ).2
    have hshift : isDyckPath n (shiftDyckPath hN₀ (fun j ↦ (γ j).1)) :=
      shiftDyckPath_isDyck hN₀ hdyck
    exact lt_of_le_of_lt (isDyckPath_le_n hshift k) hD
  have hf_val : ∀ γ ∈ S₁, ∀ k : Fin (2 * n + 1),
      (f γ k).1 = shiftDyckPath hN₀ (fun j ↦ (γ j).1) k := by
    intro γ hγ k
    simp only [f, hf_lt γ hγ k, ↓reduceDIte]
  have hf_mem : ∀ γ ∈ S₁, f γ ∈ S₂ := by
    intro γ hγ
    simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and]
    have hdyck : isDyckPath (n - N₀) (fun j ↦ (γ j).1) := (Finset.mem_filter.mp hγ).2
    have hfun : (fun k ↦ (f γ k).1) = shiftDyckPath hN₀ (fun j ↦ (γ j).1) :=
      funext (hf_val γ hγ)
    rw [hfun]
    exact shiftDyckPath_isDyck hN₀ hdyck
  have hf_inj : Set.InjOn f S₁ := by
    intro γ₁ hγ₁ γ₂ hγ₂ heq
    have hdyck₁ : isDyckPath (n - N₀) (fun j ↦ (γ₁ j).1) := (Finset.mem_filter.mp hγ₁).2
    have hdyck₂ : isDyckPath (n - N₀) (fun j ↦ (γ₂ j).1) := (Finset.mem_filter.mp hγ₂).2
    have hsh : shiftDyckPath hN₀ (fun j ↦ (γ₁ j).1) = shiftDyckPath hN₀ (fun j ↦ (γ₂ j).1) := by
      funext k
      rw [← hf_val γ₁ hγ₁ k, ← hf_val γ₂ hγ₂ k, heq]
    have hval := shiftDyckPath_injective hN₀ hdyck₁ hdyck₂ hsh
    funext j
    exact Fin.ext (congrFun hval j)
  calc ∑ γ ∈ S₁, (∏ h ∈ Finset.Icc 1 N₀, (b h) ^ 2) *
          pathWeight (fun h ↦ α₁ * (h : ℝ)) (n - N₀) (fun k ↦ (γ k).1)
      ≤ ∑ γ ∈ S₁, pathWeight b n (fun k ↦ (f γ k).1) := by
        apply Finset.sum_le_sum
        intro γ hγ
        have hdyck : isDyckPath (n - N₀) (fun j ↦ (γ j).1) := (Finset.mem_filter.mp hγ).2
        have hfun : (fun k ↦ (f γ k).1) = shiftDyckPath hN₀ (fun j ↦ (γ j).1) :=
          funext (hf_val γ hγ)
        rw [hfun]
        exact lemma_5_1_path_weight_lower b hN₀ hα₁ hb_pos hb_ge hdyck
    _ = ∑ γ' ∈ S₁.image f, pathWeight b n (fun k ↦ (γ' k).1) := by
        rw [Finset.sum_image (fun γ₁ h₁ γ₂ h₂ h ↦ hf_inj h₁ h₂ h)]
    _ ≤ ∑ γ' ∈ S₂, pathWeight b n (fun k ↦ (γ' k).1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro γ' hγ'
          rcases Finset.mem_image.mp hγ' with ⟨γ, hγ, rfl⟩
          exact hf_mem γ hγ
        · intro γ' hγ' _
          have hdyck : isDyckPath n (fun k ↦ (γ' k).1) := (Finset.mem_filter.mp hγ').2
          unfold pathWeight
          apply Finset.prod_nonneg
          intro k _
          have hstep := hdyck.2.2 k
          dsimp only at hstep
          have hpos : 1 ≤ max (γ' ⟨k.1, by omega⟩).1 (γ' ⟨k.1 + 1, by omega⟩).1 := by omega
          exact (hb_pos _ hpos).le

end JacobiDyckExpansion

section MeixnerSechBound

/-- Elementary exponential lower bound on `1 / cosh x`: for `x ≥ 0`,
`exp (-x) ≤ (cosh x)⁻¹ ≤ 2 * exp (-x)`. -/
lemma exp_neg_le_inv_cosh {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ (Real.cosh x)⁻¹ ∧ (Real.cosh x)⁻¹ ≤ 2 * Real.exp (-x) := by
  have hcosh_pos : 0 < Real.cosh x := Real.cosh_pos x
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  have h1 : Real.cosh x ≤ Real.exp x := by
    rw [Real.cosh_eq]
    have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
    linarith
  have h2 : Real.exp x / 2 ≤ Real.cosh x := by
    rw [Real.cosh_eq]
    have : 0 < Real.exp (-x) := Real.exp_pos (-x)
    linarith
  constructor
  · rw [Real.exp_neg]
    exact inv_anti₀ hcosh_pos h1
  · rw [Real.exp_neg]
    have : (Real.cosh x)⁻¹ ≤ (Real.exp x / 2)⁻¹ :=
      inv_anti₀ (by positivity) h2
    simpa [inv_div, div_eq_mul_inv, mul_comm] using this

/-- Exact Gamma evaluation of the exponential moment on `(0, ∞)`:
for `a > 0` and `k : ℕ`, `∫ ω in Ioi 0, ω ^ k * exp (-(a * ω)) = k! / a ^ (k + 1)`. -/
theorem integral_pow_mul_exp_neg_Ioi {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ∫ ω in Set.Ioi (0 : ℝ), ω ^ k * Real.exp (-(a * ω)) =
    (k.factorial : ℝ) / a ^ (k + 1) := by
  have hΓ : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ k = (k.factorial : ℝ) := by
    have h1 := Real.Gamma_eq_integral (show (0 : ℝ) < (k : ℝ) + 1 by positivity)
    rw [Real.Gamma_nat_eq_factorial k] at h1
    rw [h1]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [add_sub_cancel_right, Real.rpow_natCast]
  have hcomp :=
    MeasureTheory.Measure.integral_comp_mul_left
      (Set.indicator (Set.Ioi (0 : ℝ)) (fun x ↦ Real.exp (-x) * x ^ k)) a
  have hind : (fun ω : ℝ ↦ Set.indicator (Set.Ioi (0 : ℝ))
      (fun x ↦ Real.exp (-x) * x ^ k) (a * ω)) =
      Set.indicator (Set.Ioi (0 : ℝ)) (fun ω ↦ Real.exp (-(a * ω)) * (a * ω) ^ k) := by
    ext ω
    by_cases hω : 0 < ω
    · have haω : 0 < a * ω := mul_pos ha hω
      simp [Set.indicator_of_mem, Set.mem_Ioi, hω, haω]
    · have haω : ¬ (0 < a * ω) := fun h ↦ hω ((mul_pos_iff_of_pos_left ha).mp h)
      simp [Set.indicator_of_notMem, Set.mem_Ioi, hω, haω]
  rw [hind, MeasureTheory.integral_indicator measurableSet_Ioi,
      MeasureTheory.integral_indicator measurableSet_Ioi, hΓ,
      abs_of_pos (inv_pos.mpr ha), smul_eq_mul] at hcomp
  have hpull : ∫ ω in Set.Ioi (0 : ℝ), Real.exp (-(a * ω)) * (a * ω) ^ k =
      a ^ k * ∫ ω in Set.Ioi (0 : ℝ), ω ^ k * Real.exp (-(a * ω)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro ω _
    dsimp only
    rw [mul_pow]; ring
  rw [hpull] at hcomp
  have hak_ne : a ^ k ≠ 0 := pow_ne_zero k ha.ne'
  rw [pow_succ, ← div_div]
  have hdiv : ∫ ω in Set.Ioi (0 : ℝ), ω ^ k * Real.exp (-(a * ω)) =
      (a⁻¹ * (k.factorial : ℝ)) / a ^ k := by
    field_simp [hak_ne]
    linarith [hcomp]
  rw [hdiv]
  field_simp [ha.ne', hak_ne]

/-- **Ground-Up Meixner `sech` Moment Lower Bound (Eq. 5.5)**:
For every `α₁ > 0` and `m : ℕ`,
`(2 / π) * (2m)! * (2 α₁ / π)^{2m} ≤ (1 / α₁) * ∫_{ω > 0} ω^{2m} * (cosh(π ω / (2 α₁)))⁻¹ dω`. -/
theorem meixner_sech_moment_lower_bound {α₁ : ℝ} (hα₁ : 0 < α₁) (m : ℕ) :
    (2 / Real.pi) * ((2 * m).factorial : ℝ) * (2 * α₁ / Real.pi) ^ (2 * m) ≤
    (1 / α₁) * ∫ ω in Set.Ioi (0 : ℝ),
      ω ^ (2 * m) * (Real.cosh (Real.pi * ω / (2 * α₁)))⁻¹ := by
  set a := Real.pi / (2 * α₁)
  have ha : 0 < a := by positivity
  have harg : ∀ ω : ℝ, Real.pi * ω / (2 * α₁) = a * ω := fun ω ↦ by ring
  simp_rw [harg]
  have hint_std : MeasureTheory.IntegrableOn
      (fun x : ℝ ↦ Real.exp (-x) * x ^ (2 * m)) (Set.Ioi 0) := by
    have h0 := Real.GammaIntegral_convergent (show (0 : ℝ) < (2 * m : ℕ) + 1 by positivity)
    refine h0.congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
    dsimp only
    rw [add_sub_cancel_right, Real.rpow_natCast]
  have hint_exp : MeasureTheory.IntegrableOn
      (fun ω : ℝ ↦ ω ^ (2 * m) * Real.exp (-(a * ω))) (Set.Ioi 0) := by
    have h1 : MeasureTheory.Integrable
        (Set.indicator (Set.Ioi (0 : ℝ)) (fun x ↦ Real.exp (-x) * x ^ (2 * m))) :=
      (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).mpr hint_std
    have h2 := h1.comp_mul_left' ha.ne'
    have hind : (fun ω : ℝ ↦ Set.indicator (Set.Ioi (0 : ℝ))
        (fun x ↦ Real.exp (-x) * x ^ (2 * m)) (a * ω)) =
        Set.indicator (Set.Ioi (0 : ℝ)) (fun ω ↦ Real.exp (-(a * ω)) * (a * ω) ^ (2 * m)) := by
      ext ω
      by_cases hω : 0 < ω
      · simp [Set.indicator_of_mem, Set.mem_Ioi, hω, mul_pos ha hω]
      · have haω : ¬ (0 < a * ω) := fun h ↦ hω ((mul_pos_iff_of_pos_left ha).mp h)
        simp [Set.indicator_of_notMem, Set.mem_Ioi, hω, haω]
    rw [hind, MeasureTheory.integrable_indicator_iff measurableSet_Ioi] at h2
    have h3 : MeasureTheory.IntegrableOn
        (fun ω : ℝ ↦ (a ^ (2 * m))⁻¹ * (Real.exp (-(a * ω)) * (a * ω) ^ (2 * m))) (Set.Ioi 0) :=
      h2.const_mul (a ^ (2 * m))⁻¹
    refine h3.congr_fun (fun ω _ ↦ ?_) measurableSet_Ioi
    dsimp only
    have hak : a ^ (2 * m) ≠ 0 := pow_ne_zero _ ha.ne'
    rw [mul_pow]
    field_simp [hak]
  have hint_cosh : MeasureTheory.IntegrableOn
      (fun ω : ℝ ↦ ω ^ (2 * m) * (Real.cosh (a * ω))⁻¹) (Set.Ioi 0) := by
    have hcont : Continuous (fun ω : ℝ ↦ ω ^ (2 * m) * (Real.cosh (a * ω))⁻¹) :=
      (continuous_pow (2 * m)).mul
        ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀
          fun x ↦ (Real.cosh_pos _).ne')
    refine (hint_exp.const_mul 2).mono' hcont.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with ω hω
    have hω_pos : 0 < ω := hω
    have haω_nn : 0 ≤ a * ω := (mul_pos ha hω_pos).le
    have hval_nn : 0 ≤ ω ^ (2 * m) * (Real.cosh (a * ω))⁻¹ := by
      have := Real.cosh_pos (a * ω)
      positivity
    rw [Real.norm_of_nonneg hval_nn]
    have hbd := (exp_neg_le_inv_cosh haω_nn).2
    have := mul_le_mul_of_nonneg_left hbd (pow_nonneg hω_pos.le (2 * m))
    linarith
  have hmono :
      ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * m) * Real.exp (-(a * ω)) ≤
      ∫ ω in Set.Ioi (0 : ℝ), ω ^ (2 * m) * (Real.cosh (a * ω))⁻¹ := by
    refine MeasureTheory.setIntegral_mono_on hint_exp hint_cosh measurableSet_Ioi ?_
    intro ω hω
    have hω_pos : 0 < ω := hω
    exact mul_le_mul_of_nonneg_left
      (exp_neg_le_inv_cosh (mul_pos ha hω_pos).le).1
      (pow_nonneg hω_pos.le (2 * m))
  rw [integral_pow_mul_exp_neg_Ioi ha (2 * m)] at hmono
  have hmul := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / α₁)
  have hident :
      (1 / α₁) * (((2 * m).factorial : ℝ) / a ^ (2 * m + 1)) =
      (2 / Real.pi) * ((2 * m).factorial : ℝ) * (2 * α₁ / Real.pi) ^ (2 * m) := by
    have hpi_ne : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hα_ne : α₁ ≠ 0 := hα₁.ne'
    simp only [a, pow_succ, div_pow]
    field_simp [hpi_ne, hα_ne]
  linarith [hmul, hident]

end MeixnerSechBound

end KrylovChaos
