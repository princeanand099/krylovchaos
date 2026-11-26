/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.ManyBodySetup
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Section 9, Proposition 9.1(2) (Eq. 9.2): Exact Bimodal State Thermal Size on `QubitOp N`

Evaluates the exact thermal size `𝒮_ρ(A)` on the concrete `N`-qubit non-clustering bimodal
state (`N ≥ 2`, Eq. 9.1):
`ρ_N = (1/2) |0⟩⟨0|_0 ⊗ (I_{N-1} / 2^{N-1}) + (1/2) |1⟩⟨1|_0 ⊗ |0⋯0⟩⟨0⋯0|_{1..N-1}`
and the concrete `1`-local Hermitian operator `A_N = √2 |1⟩⟨1|_0 ⊗ I_{1..N-1} ∈ 𝒱_1`,
proving from ground up on `QubitOp N`:
1. Exact computational-basis diagonal formula for `⟨diag d, siteSizeOp x (diag d)⟩_HS`
   (`diag_siteSizeOp_inner`).
2. Exact Hilbert–Schmidt size of `J_ρ(A_N) = |1, 0, …, 0⟩⟨1, 0, …, 0|`: `N / 2`
   (`bimodal_jA_size`).
3. Exact Hilbert–Schmidt size of `ρ_N^{1/2}`: `(N + 1) / 4 - 2^{-(N + 1) / 2}`
   (`bimodal_rhoHalf_size`).
4. **Exact Eq. (9.2)** (`prop_9_1_bimodal_exact_size`):
   `⟨J_ρ(A_N), 𝒮 J_ρ(A_N)⟩_HS - ⟨ρ_N^{1/2}, 𝒮 ρ_N^{1/2}⟩_HS = (N - 1) / 4 + 2^{-(N + 1) / 2}`
   for every `N ≥ 2`.
-/

namespace KrylovChaos

open scoped Matrix Classical

section DiagonalSizeFormula

/-- Bit-flip of computational basis state `s : Fin N → Fin 2` at site `x : Fin N`. -/
def flipSite {N : ℕ} (x : Fin N) (s : Fin N → Fin 2) : Fin N → Fin 2 :=
  Function.update s x (1 - s x)

lemma flipSite_invol {N : ℕ} (x : Fin N) (s : Fin N → Fin 2) :
    flipSite x (flipSite x s) = s := by
  ext y
  by_cases hy : y = x
  · subst hy
    simp only [flipSite, Function.update_self]
    fin_cases (s y) <;> decide
  · simp [flipSite, Function.update_of_ne hy]

lemma flipSite_ne_self {N : ℕ} (x : Fin N) (s : Fin N → Fin 2) :
    flipSite x s ≠ s := by
  intro h
  have hx := congrFun h x
  simp only [flipSite, Function.update_self] at hx
  fin_cases (s x) <;> simp at hx

private lemma pauliSite_diag_conj {N : ℕ} (x : Fin N) (α : Fin 4)
    (d : (Fin N → Fin 2) → ℝ) :
    pauliSite x α * Matrix.diagonal (fun s ↦ (d s : ℂ)) * pauliSite x α =
    Matrix.diagonal (fun s ↦
      if α = 0 ∨ α = 3 then (d s : ℂ) else (d (flipSite x s) : ℂ)) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  have hP : ∀ u v : Fin N → Fin 2,
      pauliSite x α u v =
      (if ∀ y : Fin N, y ≠ x → u y = v y then pauliMat α (u x) (v x) else 0) := by
    intro u v
    unfold pauliSite pauliString kronOp
    simp only [Matrix.of_apply]
    by_cases hall : ∀ y : Fin N, y ≠ x → u y = v y
    · rw [if_pos hall, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
      simp only [Function.update_self]
      have hrest : (∏ y ∈ Finset.univ.erase x, pauliMat (Function.update (fun _ ↦ 0) x α y) (u y) (v y)) = 1 := by
        apply Finset.prod_eq_one
        intro y hy
        have hne : y ≠ x := (Finset.mem_erase.mp hy).1
        rw [Function.update_of_ne hne, hall y hne]
        fin_cases (v y) <;> simp [pauliMat]
      rw [hrest, mul_one]
    · rw [if_neg hall]
      push_neg at hall
      rcases hall with ⟨y, hyx, huy⟩
      apply Finset.prod_eq_zero (Finset.mem_univ y)
      rw [Function.update_of_ne hyx]
      fin_cases (u y) <;> fin_cases (v y) <;> simp [pauliMat] at huy ⊢
  simp_rw [hP]
  by_cases hα : α = 0 ∨ α = 3
  · rw [if_pos hα]
    have hdiag : ∀ u v : Fin N → Fin 2,
        (if ∀ y, y ≠ x → u y = v y then pauliMat α (u x) (v x) else 0) =
        if u = v then pauliMat α (u x) (u x) else 0 := by
      intro u v
      by_cases huv : u = v
      · subst huv; simp
      · rw [if_neg huv]
        by_cases hall : ∀ y, y ≠ x → u y = v y
        · rw [if_pos hall]
          have hux : u x ≠ v x := fun hx ↦ huv (funext fun y ↦ if h : y = x then h ▸ hx else hall y h)
          rcases hα with rfl | rfl <;> fin_cases (u x) <;> fin_cases (v x) <;> simp [pauliMat] at hux ⊢
        · rw [if_neg hall]
    simp_rw [hdiag]
    by_cases hab : a = b
    · subst hab
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single a]
      · simp only [↓reduceIte]
        rcases hα with rfl | rfl <;> fin_cases (a x) <;> simp [pauliMat]
      · intro c _ hca; simp [Ne.symm hca]
      · intro h; exact absurd (Finset.mem_univ a) h
    · simp only [hab, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hac : a = c
      · subst hac; simp [hab]
      · simp [hac]
  · rw [if_neg hα]
    have hα12 : α = 1 ∨ α = 2 := by fin_cases α <;> simp at hα ⊢
    have hflip : ∀ u v : Fin N → Fin 2,
        (if ∀ y, y ≠ x → u y = v y then pauliMat α (u x) (v x) else 0) =
        if v = flipSite x u then pauliMat α (u x) (1 - u x) else 0 := by
      intro u v
      by_cases hv : v = flipSite x u
      · subst hv
        have hall : ∀ y, y ≠ x → u y = flipSite x u y := fun y hy ↦ by simp [flipSite, Function.update_of_ne hy]
        simp [hall, flipSite, Function.update_self]
      · rw [if_neg hv]
        by_cases hall : ∀ y, y ≠ x → u y = v y
        · rw [if_pos hall]
          have hux : v x ≠ 1 - u x := by
            intro hx
            apply hv
            ext y
            by_cases hy : y = x
            · subst hy; simp [flipSite, Function.update_self, hx]
            · simp [flipSite, Function.update_of_ne hy, hall y hy]
          rcases hα12 with rfl | rfl <;> fin_cases (u x) <;> fin_cases (v x) <;> simp [pauliMat] at hux ⊢
        · rw [if_neg hall]
    simp_rw [hflip]
    by_cases hab : a = b
    · subst hab
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single (flipSite x a)]
      · simp only [↓reduceIte, flipSite_invol]
        have hflx : (flipSite x a) x = 1 - a x := by simp [flipSite]
        rw [hflx]
        rcases hα12 with rfl | rfl <;> fin_cases (a x) <;> simp [pauliMat, Complex.I_mul_I]
      · intro c _ hc; simp [hc]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [hab, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hc : c = flipSite x a
      · subst hc
        have hne : b ≠ a := Ne.symm hab
        simp [flipSite_invol, hne]
      · simp [hc]

/-- Exact computational-basis formula for `Re ⟨diag d, siteSizeOp x (diag d)⟩_HS`:
`(1 / 2) ∑_s d(s) (d(s) - d(flip_x s))`. -/
theorem diag_siteSizeOp_inner {N : ℕ} (x : Fin N) (d : (Fin N → Fin 2) → ℝ) :
    (hsInner (Matrix.diagonal (fun s ↦ (d s : ℂ)))
      (siteSizeOp x (Matrix.diagonal (fun s ↦ (d s : ℂ))))).re =
    ∑ s : Fin N → Fin 2, d s * (d s - d (flipSite x s)) / 2 := by
  have hE : partialTraceSite x (Matrix.diagonal (fun s ↦ (d s : ℂ))) =
      Matrix.diagonal (fun s ↦ (((d s + d (flipSite x s)) / 2 : ℝ) : ℂ)) := by
    unfold partialTraceSite
    simp_rw [pauliSite_diag_conj]
    ext a b
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.diagonal_apply, Fin.sum_univ_four,
      smul_eq_mul]
    by_cases hab : a = b
    · subst hab; simp; push_cast; ring
    · simp [hab]
  have hS : siteSizeOp x (Matrix.diagonal (fun s ↦ (d s : ℂ))) =
      Matrix.diagonal (fun s ↦ (((d s - d (flipSite x s)) / 2 : ℝ) : ℂ)) := by
    unfold siteSizeOp
    rw [hE]
    ext a b
    simp only [Matrix.sub_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab; simp; push_cast; ring
    · simp [hab]
  rw [hS]
  unfold hsInner
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

end DiagonalSizeFormula

section BimodalExactEvaluation

/-- Pure computational basis state `|1, 0, …, 0⟩` on `N ≥ 2` qubits. -/
def bimodalBasis1 {N : ℕ} (hN : 2 ≤ N) : Fin N → Fin 2 :=
  Function.update (fun _ ↦ 0) ⟨0, by omega⟩ 1

/-- Computational-basis diagonal of `J_ρ(A_N) = |1, 0, …, 0⟩⟨1, 0, …, 0|`. -/
def bimodalJADiag {N : ℕ} (hN : 2 ≤ N) (s : Fin N → Fin 2) : ℝ :=
  if s = bimodalBasis1 hN then 1 else 0

/-- Computational-basis diagonal of `ρ_N^{1/2}` for Eq. (9.1):
- `2^{-N/2}` on `s_0 = 0`,
- `2^{-1/2}` on `s = |1, 0, …, 0⟩`,
- `0` on all other `s` with `s_0 = 1`. -/
noncomputable def bimodalRhoHalfDiag {N : ℕ} (hN : 2 ≤ N) (s : Fin N → Fin 2) : ℝ :=
  if s ⟨0, by omega⟩ = 0 then (Real.sqrt ((2 : ℝ) ^ N))⁻¹
  else if s = bimodalBasis1 hN then (Real.sqrt 2)⁻¹
  else 0

/-- Exact Hilbert–Schmidt operator size of `J_ρ(A_N)`: `⟨J_ρ(A_N), 𝒮 J_ρ(A_N)⟩_HS = N / 2`. -/
theorem bimodal_jA_size {N : ℕ} (hN : 2 ≤ N) :
    (hsInner (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ)))
      (totalSizeOp (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ))))).re =
    (N : ℝ) / 2 := by
  have hsum :
      (hsInner (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ)))
        (totalSizeOp (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ))))).re =
      ∑ x : Fin N, (hsInner (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ)))
        (siteSizeOp x (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ))))).re := by
    unfold totalSizeOp hsInner
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  rw [hsum]
  have hsite : ∀ x : Fin N,
      (hsInner (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ)))
        (siteSizeOp x (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ))))).re = 1 / 2 := by
    intro x
    rw [diag_siteSizeOp_inner]
    rw [Finset.sum_eq_single (bimodalBasis1 hN)]
    · simp [bimodalJADiag, flipSite_ne_self]
    · intro s _ hs; simp [bimodalJADiag, hs]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hsite]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Exact Hilbert–Schmidt operator size of `ρ_N^{1/2}`:
`⟨ρ_N^{1/2}, 𝒮 ρ_N^{1/2}⟩_HS = (N + 1) / 4 - (√(2^{N+1}))⁻¹`. -/
theorem bimodal_rhoHalf_size {N : ℕ} (hN : 2 ≤ N) :
    (hsInner (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ)))
      (totalSizeOp (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ))))).re =
    ((N : ℝ) + 1) / 4 - (Real.sqrt ((2 : ℝ) ^ (N + 1)))⁻¹ := by
  have hsum :
      (hsInner (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ)))
        (totalSizeOp (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ))))).re =
      ∑ x : Fin N, (hsInner (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ)))
        (siteSizeOp x (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ))))).re := by
    unfold totalSizeOp hsInner
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  rw [hsum]
  let x₀ : Fin N := ⟨0, by omega⟩
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ x₀)]
  have hother : ∀ x ∈ Finset.univ.erase x₀,
      (hsInner (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ)))
        (siteSizeOp x (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ))))).re = 1 / 4 := by
    intro x hx
    have hne : x ≠ x₀ := (Finset.mem_erase.mp hx).1
    rw [diag_siteSizeOp_inner]
    rw [Finset.sum_eq_single (bimodalBasis1 hN)]
    · have h1 : bimodalBasis1 hN x₀ = 1 := by simp [bimodalBasis1, x₀]
      have h2 : flipSite x (bimodalBasis1 hN) x₀ = 1 := by
        simp [flipSite, Function.update_of_ne (Ne.symm hne), h1]
      have h3 : flipSite x (bimodalBasis1 hN) ≠ bimodalBasis1 hN := flipSite_ne_self x _
      simp only [bimodalRhoHalfDiag, x₀] at *
      rw [if_neg (by rw [h1]; decide), if_pos rfl, if_neg (by rw [h2]; decide), if_neg h3]
      have hsq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (2 : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
      linarith [hsq]
    · intro s _ hs
      by_cases hs0 : s x₀ = 0
      · have hfl0 : flipSite x s x₀ = 0 := by
          simp [flipSite, Function.update_of_ne (Ne.symm hne), hs0]
        simp [bimodalRhoHalfDiag, x₀, hs0, hfl0]
      · simp [bimodalRhoHalfDiag, x₀, hs0, hs]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsum_other :
      (∑ x ∈ Finset.univ.erase x₀,
        (hsInner (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ)))
          (siteSizeOp x (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ))))).re) =
      ((N : ℝ) - 1) / 4 := by
    rw [Finset.sum_congr rfl hother, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    ring
  have hfirst :
      (hsInner (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ)))
        (siteSizeOp x₀ (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ))))).re =
      1 / 2 - (Real.sqrt ((2 : ℝ) ^ (N + 1)))⁻¹ := by
    rw [diag_siteSizeOp_inner]
    set c₀ := (Real.sqrt ((2 : ℝ) ^ N))⁻¹
    set c₁ := (Real.sqrt 2)⁻¹
    let s₀ : Fin N → Fin 2 := fun _ ↦ 0
    have hfl_s0 : flipSite x₀ s₀ = bimodalBasis1 hN := by
      ext y; simp [flipSite, s₀, bimodalBasis1, x₀]
    have hfl_s1 : flipSite x₀ (bimodalBasis1 hN) = s₀ := by
      rw [← hfl_s0, flipSite_invol]
    have hcard0 : (Finset.univ.filter (fun s : Fin N → Fin 2 ↦ s x₀ = 0)).card = 2 ^ (N - 1) := by
      let e : {s : Fin N → Fin 2 // s x₀ = 0} ≃ ({y : Fin N // y ≠ x₀} → Fin 2) :=
        { toFun := fun s y ↦ s.1 y.1
          invFun := fun f ↦ ⟨fun y ↦ if h : y = x₀ then 0 else f ⟨y, h⟩, by simp⟩
          left_inv := fun s ↦ by
            ext y; by_cases h : y = x₀
            · subst h; simp [s.2]
            · simp [h]
          right_inv := fun f ↦ by
            ext y; simp [y.2] }
      have h1 : (Finset.univ.filter (fun s : Fin N → Fin 2 ↦ s x₀ = 0)).card =
          Fintype.card {s : Fin N → Fin 2 // s x₀ = 0} := by
        rw [Fintype.card_subtype]
      rw [h1, Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_subtype_compl, Fintype.card_unique, Fintype.card_fin]
    have hsplit :
        (∑ s : Fin N → Fin 2, bimodalRhoHalfDiag hN s *
          (bimodalRhoHalfDiag hN s - bimodalRhoHalfDiag hN (flipSite x₀ s)) / 2) =
        (∑ s ∈ Finset.univ.filter (fun s : Fin N → Fin 2 ↦ s x₀ = 0),
          bimodalRhoHalfDiag hN s *
            (bimodalRhoHalfDiag hN s - bimodalRhoHalfDiag hN (flipSite x₀ s)) / 2) +
        (bimodalRhoHalfDiag hN (bimodalBasis1 hN) *
          (bimodalRhoHalfDiag hN (bimodalBasis1 hN) -
            bimodalRhoHalfDiag hN (flipSite x₀ (bimodalBasis1 hN))) / 2) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : Fin N → Fin 2 ↦ s x₀ = 0)]
      congr 1
      rw [Finset.sum_eq_single (bimodalBasis1 hN)]
      · intro s hs hne
        have hs1 : s x₀ ≠ 0 := (Finset.mem_filter.mp hs).2
        simp [bimodalRhoHalfDiag, x₀, hs1, hne]
      · intro h
        have hmem : bimodalBasis1 hN ∈ Finset.univ.filter (fun s : Fin N → Fin 2 ↦ ¬ s x₀ = 0) := by
          simp [bimodalBasis1, x₀]
        exact absurd hmem h
    rw [hsplit]
    have hs0_mem : s₀ ∈ Finset.univ.filter (fun s : Fin N → Fin 2 ↦ s x₀ = 0) := by simp [s₀]
    rw [← Finset.add_sum_erase _ _ hs0_mem]
    have hrest : ∀ s ∈ (Finset.univ.filter (fun s : Fin N → Fin 2 ↦ s x₀ = 0)).erase s₀,
        bimodalRhoHalfDiag hN s *
          (bimodalRhoHalfDiag hN s - bimodalRhoHalfDiag hN (flipSite x₀ s)) / 2 =
        c₀ ^ 2 / 2 := by
      intro s hs
      have hne_s0 : s ≠ s₀ := (Finset.mem_erase.mp hs).1
      have hs0 : s x₀ = 0 := (Finset.mem_filter.mp (Finset.mem_erase.mp hs).2).2
      have hfl1 : flipSite x₀ s x₀ = 1 := by simp [flipSite, hs0]
      have hfl_ne : flipSite x₀ s ≠ bimodalBasis1 hN := by
        intro h
        apply hne_s0
        have := congrArg (flipSite x₀) h
        rwa [flipSite_invol, hfl_s1] at this
      simp only [bimodalRhoHalfDiag, x₀, hs0, ↓reduceIte]
      rw [if_neg (by rw [hfl1]; decide), if_neg hfl_ne]
      simp only [c₀]; ring
    rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_erase_of_mem hs0_mem, hcard0,
      nsmul_eq_mul]
    have hs0_val :
        bimodalRhoHalfDiag hN s₀ *
          (bimodalRhoHalfDiag hN s₀ - bimodalRhoHalfDiag hN (flipSite x₀ s₀)) / 2 =
        c₀ * (c₀ - c₁) / 2 := by
      rw [hfl_s0]
      have h1 : bimodalBasis1 hN x₀ = 1 := by simp [bimodalBasis1, x₀]
      simp only [bimodalRhoHalfDiag, x₀, s₀, ↓reduceIte, c₀, c₁]
      rw [if_neg (by rw [h1]; decide)]
    have hs1_val :
        bimodalRhoHalfDiag hN (bimodalBasis1 hN) *
          (bimodalRhoHalfDiag hN (bimodalBasis1 hN) -
            bimodalRhoHalfDiag hN (flipSite x₀ (bimodalBasis1 hN))) / 2 =
        c₁ * (c₁ - c₀) / 2 := by
      rw [hfl_s1]
      have h1 : bimodalBasis1 hN x₀ = 1 := by simp [bimodalBasis1, x₀]
      simp only [bimodalRhoHalfDiag, x₀, s₀, ↓reduceIte, c₀, c₁]
      rw [if_neg (by rw [h1]; decide)]
    rw [hs0_val, hs1_val]
    have hc0_sq : c₀ ^ 2 = ((2 : ℝ) ^ N)⁻¹ := by
      simp only [c₀, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ N)]
    have hc1_sq : c₁ ^ 2 = (2 : ℝ)⁻¹ := by
      simp only [c₁, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hc0c1 : c₀ * c₁ = (Real.sqrt ((2 : ℝ) ^ (N + 1)))⁻¹ := by
      simp only [c₀, c₁, ← mul_inv, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ N),
        pow_succ]
    have hpow_cast : (((2 ^ (N - 1) - 1 : ℕ) : ℝ)) = (2 : ℝ) ^ (N - 1) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow)]
      simp
    have h2N : (2 : ℝ) ^ (N - 1) * ((2 : ℝ) ^ N)⁻¹ = (2 : ℝ)⁻¹ := by
      have h1 : (2 : ℝ) ^ N = (2 : ℝ) ^ (N - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [h1]
      have hne : (2 : ℝ) ^ (N - 1) ≠ 0 := by positivity
      field_simp [hne]
    rw [hpow_cast]
    calc c₀ * (c₀ - c₁) / 2 + ((2 : ℝ) ^ (N - 1) - 1) * (c₀ ^ 2 / 2) + c₁ * (c₁ - c₀) / 2
        = ((2 : ℝ) ^ (N - 1) * c₀ ^ 2 + c₁ ^ 2) / 2 - c₀ * c₁ := by ring
      _ = ((2 : ℝ) ^ (N - 1) * ((2 : ℝ) ^ N)⁻¹ + (2 : ℝ)⁻¹) / 2 -
            (Real.sqrt ((2 : ℝ) ^ (N + 1)))⁻¹ := by rw [hc0_sq, hc1_sq, hc0c1]
      _ = ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) / 2 - (Real.sqrt ((2 : ℝ) ^ (N + 1)))⁻¹ := by rw [h2N]
      _ = 1 / 2 - (Real.sqrt ((2 : ℝ) ^ (N + 1)))⁻¹ := by ring
  rw [hfirst, hsum_other]
  ring

/-- **Proposition 9.1(2) (Exact Eq. 9.2 on `QubitOp N`)**:
For every `N ≥ 2`, the thermal size of `A_N = √2 |1⟩⟨1|_0` in the non-clustering bimodal
state `ρ_N` (Eq. 9.1) satisfies
`𝒮_{ρ_N}(A_N) = (N - 1) / 4 + (√(2^{N+1}))⁻¹ = (N - 1) / 4 + 2^{-(N + 1) / 2}`. -/
theorem prop_9_1_bimodal_exact_size {N : ℕ} (hN : 2 ≤ N) :
    (hsInner (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ)))
      (totalSizeOp (Matrix.diagonal (fun s ↦ (bimodalJADiag hN s : ℂ))))).re -
    (hsInner (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ)))
      (totalSizeOp (Matrix.diagonal (fun s ↦ (bimodalRhoHalfDiag hN s : ℂ))))).re =
    ((N : ℝ) - 1) / 4 + (Real.sqrt ((2 : ℝ) ^ (N + 1)))⁻¹ := by
  rw [bimodal_jA_size hN, bimodal_rhoHalf_size hN]
  ring

end BimodalExactEvaluation

end KrylovChaos
