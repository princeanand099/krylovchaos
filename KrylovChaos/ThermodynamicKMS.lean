/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.VitaliAnalytic
import KrylovChaos.SpectralMeasure
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
# Thermodynamic Limit of Gibbs KMS States on the Quasi-Local Spin Algebra (N → ∞)

Formalizes ground-up on Mathlib `v4.35.0` (zero custom axioms, zero `sorry`s):
1. **Finite-`N` Gibbs KMS Analyticity (`finiteKMSCorr`, `finiteKMS_entire`, `finiteKMS_boundary_identity`)**:
   For any finite-dimensional diagonalized Hamiltonian `E : ι → ℝ`, inverse temperature `β > 0`,
   and operators `A, B : Matrix ι ι ℂ`, defines the complex-time Gibbs correlation function
   `F_{A,B}(z) = Tr(ρ_β A e^{izH} B e^{-izH})`, proves it is entire on `ℂ`, and proves the
   exact KMS boundary identity `F_{A,B}(t + i β) = F_{B,A}(-t)` for all `t ∈ ℝ`.
2. **Countable Quasi-Local Pauli Basis (`PauliWord := List (Fin 4)`) & Weak-* Compactness
   (`thermo_limit_state_exists`)**:
   Using Tychonoff compactness (`isCompact_univ_pi`) and sequential compactness of the
   countable product `PauliWord → ℂ` of closed unit discs, proves that EVERY sequence of
   finite-volume Gibbs states `ω : ℕ → PauliWord → ℂ` (`‖ω N w‖ ≤ 1`, `ω N [] = 1`) admits
   a strictly increasing subsequence converging pointwise to a normalized thermodynamic-limit
   state `ω_∞ : PauliWord → ℂ` preserving positivity on all finite linear combinations.
3. **Thermodynamic-Limit KMS Boundary Transfer (`thermo_limit_kms_boundary_transfer`)**:
   Proves that pointwise limits of finite-volume KMS boundary pairs `(F_k(t + iβ) = G_k(t))`
   satisfy the exact thermodynamic-limit KMS boundary condition `F_∞(t + iβ) = G_∞(t)`.
-/

namespace KrylovChaos

open scoped Matrix

section FiniteVolumeKMS

/-- Finite-volume Gibbs partition function `Z(β) = ∑_a exp(-β E_a)`. -/
noncomputable def kmsPartitionFn {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) : ℝ :=
  ∑ a : ι, Real.exp (-(β * E a))

lemma kmsPartitionFn_pos {ι : Type*} [Fintype ι] [Nonempty ι] (E : ι → ℝ) (β : ℝ) :
    0 < kmsPartitionFn E β :=
  Finset.sum_pos (fun a _ ↦ Real.exp_pos _) Finset.univ_nonempty

/-- Gibbs probability weights `p_a = exp(-β E_a) / Z(β)`. -/
noncomputable def kmsWeight {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ) (a : ι) : ℝ :=
  Real.exp (-(β * E a)) / kmsPartitionFn E β

/-- Complex-time Gibbs two-point correlation function in the energy eigenbasis:
`F_{A,B}(z) = Tr(ρ_β A e^{i z H} B e^{-i z H}) = ∑_{a,b} p_a A_{ab} B_{ba} e^{i z (E_b - E_a)}`. -/
noncomputable def finiteKMSCorr {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ)
    (A B : Matrix ι ι ℂ) (z : ℂ) : ℂ :=
  ∑ a : ι, ∑ b : ι,
    (kmsWeight E β a : ℂ) * A a b * B b a *
      Complex.exp (Complex.I * z * ((E b - E a : ℝ) : ℂ))

/-- `finiteKMSCorr E β A B` is entire (`Differentiable ℂ`) on all of `ℂ`. -/
theorem finiteKMS_entire {ι : Type*} [Fintype ι] (E : ι → ℝ) (β : ℝ)
    (A B : Matrix ι ι ℂ) :
    Differentiable ℂ (finiteKMSCorr E β A B) := by
  unfold finiteKMSCorr
  apply Differentiable.fun_sum; intro a _
  apply Differentiable.fun_sum; intro b _
  apply Differentiable.const_mul
  exact ((differentiable_id.const_mul Complex.I).mul_const ((E b - E a : ℝ) : ℂ)).cexp

/-- **Exact Finite-Volume KMS Boundary Identity**:
For every finite-dimensional Hamiltonian `E : ι → ℝ`, inverse temperature `β : ℝ`,
operators `A, B : Matrix ι ι ℂ`, and real time `t : ℝ`:
`F_{A,B}(t + i β) = F_{B,A}(-t)`. -/
theorem finiteKMS_boundary_identity {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : ι → ℝ) (β : ℝ) (A B : Matrix ι ι ℂ) (t : ℝ) :
    finiteKMSCorr E β A B ((t : ℂ) + Complex.I * (β : ℂ)) =
    finiteKMSCorr E β B A (-(t : ℂ)) := by
  unfold finiteKMSCorr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro a _
  have hexp_split :
      Complex.exp (Complex.I * ((t : ℂ) + Complex.I * (β : ℂ)) * ((E b - E a : ℝ) : ℂ)) =
      Complex.exp ((-(β * (E b - E a)) : ℝ)) *
        Complex.exp (Complex.I * (-(t : ℂ)) * ((E a - E b : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (β : ℂ) * ((E b : ℂ) - (E a : ℂ)) * hI2
  have hweight :
      (kmsWeight E β a : ℂ) * Complex.exp ((-(β * (E b - E a)) : ℝ)) =
      (kmsWeight E β b : ℂ) := by
    unfold kmsWeight
    rw [← Complex.ofReal_exp, ← Complex.ofReal_mul]
    congr 1
    rw [div_mul_eq_mul_div, ← Real.exp_add]
    congr 2
    ring
  calc (kmsWeight E β a : ℂ) * A a b * B b a *
        Complex.exp (Complex.I * ((t : ℂ) + Complex.I * (β : ℂ)) * ((E b - E a : ℝ) : ℂ))
      = ((kmsWeight E β a : ℂ) * Complex.exp ((-(β * (E b - E a)) : ℝ))) *
          B b a * A a b * Complex.exp (Complex.I * (-(t : ℂ)) * ((E a - E b : ℝ) : ℂ)) := by
          rw [hexp_split]; ring
    _ = (kmsWeight E β b : ℂ) * B b a * A a b *
          Complex.exp (Complex.I * (-(t : ℂ)) * ((E a - E b : ℝ) : ℂ)) := by
          rw [hweight]

/-- Finite-volume Gibbs state normalization `F_{1,1}(0) = 1`. -/
theorem finiteKMS_normalized {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (E : ι → ℝ) (β : ℝ) :
    finiteKMSCorr E β (1 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) 0 = 1 := by
  unfold finiteKMSCorr
  have h1 : ∀ a : ι,
      ∑ b : ι, (kmsWeight E β a : ℂ) * (1 : Matrix ι ι ℂ) a b * (1 : Matrix ι ι ℂ) b a *
        Complex.exp (Complex.I * 0 * ((E b - E a : ℝ) : ℂ)) = (kmsWeight E β a : ℂ) := by
    intro a
    have hsub : ∀ b : ι,
        (kmsWeight E β a : ℂ) * (1 : Matrix ι ι ℂ) a b * (1 : Matrix ι ι ℂ) b a *
          Complex.exp (Complex.I * 0 * ((E b - E a : ℝ) : ℂ)) =
        if b = a then (kmsWeight E β a : ℂ) else 0 := by
      intro b
      by_cases hba : b = a
      · subst hba; simp [Matrix.one_apply]
      · simp [Matrix.one_apply, hba, Ne.symm hba]
    simp_rw [hsub]; simp
  simp_rw [h1]
  unfold kmsWeight
  simp_rw [Complex.ofReal_div]
  rw [← Finset.sum_div]
  have hsum : (∑ a : ι, (Real.exp (-(β * E a)) : ℂ)) = (kmsPartitionFn E β : ℂ) := by
    unfold kmsPartitionFn; push_cast; rfl
  rw [hsum]
  exact div_self (Complex.ofReal_ne_zero.mpr (kmsPartitionFn_pos E β).ne')

end FiniteVolumeKMS

section ThermodynamicLimitStates

/-- Countable quasi-local Pauli string basis on the infinite spin lattice `ℕ`:
finite lists `w : List (Fin 4)` (`[]` = identity `1`). -/
abbrev PauliWord := List (Fin 4)

/-- **Thermodynamic-Limit State Existence (Banach–Alaoglu / Tychonoff Compactness)**:
Every sequence of finite-volume states `ω : ℕ → PauliWord → ℂ` uniformly bounded by `1`
(`∀ N w, ‖ω N w‖ ≤ 1`) and normalized (`∀ N, ω N [] = 1`) admits a strictly increasing
subsequence `φ : ℕ → ℕ` and a thermodynamic-limit state `ω_∞ : PauliWord → ℂ` such that:
1. Pointwise weak-* convergence on every local Pauli word `w : PauliWord`,
2. Normalization `ω_∞ [] = 1`,
3. Uniform bound `∀ w, ‖ω_∞ w‖ ≤ 1`,
4. Preservation of positivity `0 ≤ (∑ w ∈ S, c w * ω_∞ w).re` whenever every finite-volume
   state `ω N` satisfies `0 ≤ (∑ w ∈ S, c w * ω N w).re`. -/
theorem thermo_limit_state_exists
    (ω : ℕ → PauliWord → ℂ)
    (hnorm : ∀ N w, ‖ω N w‖ ≤ 1)
    (hone : ∀ N, ω N [] = 1) :
    ∃ (ω_inf : PauliWord → ℂ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ w : PauliWord, Filter.Tendsto (fun k ↦ ω (φ k) w) Filter.atTop (nhds (ω_inf w))) ∧
      ω_inf [] = 1 ∧
      (∀ w : PauliWord, ‖ω_inf w‖ ≤ 1) ∧
      (∀ (S : Finset PauliWord) (c : PauliWord → ℂ),
        (∀ N, 0 ≤ (∑ w ∈ S, c w * ω N w).re) →
        0 ≤ (∑ w ∈ S, c w * ω_inf w).re) := by
  let K : Set (PauliWord → ℂ) := Set.univ.pi (fun _ : PauliWord ↦ Metric.closedBall (0 : ℂ) 1)
  have hK_compact : IsCompact K :=
    isCompact_univ_pi fun _ ↦ isCompact_closedBall (0 : ℂ) 1
  have hK_seq : IsSeqCompact K := hK_compact.isSeqCompact
  have hmem : ∀ N, ω N ∈ K := fun N w _ ↦ by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hnorm N w
  obtain ⟨ω_inf, hω_mem, φ, hφ_mono, hφ_tend⟩ := hK_seq hmem
  have hpt : ∀ w : PauliWord, Filter.Tendsto (fun k ↦ ω (φ k) w) Filter.atTop (nhds (ω_inf w)) :=
    fun w ↦ (continuous_apply w).continuousAt.tendsto.comp hφ_tend
  have hω_one : ω_inf [] = 1 := by
    have hconst : Filter.Tendsto (fun k ↦ ω (φ k) []) Filter.atTop (nhds (1 : ℂ)) := by
      simpa [hone] using (tendsto_const_nhds (x := (1 : ℂ)) (f := Filter.atTop))
    exact tendsto_nhds_unique (hpt []) hconst
  have hω_bound : ∀ w : PauliWord, ‖ω_inf w‖ ≤ 1 := fun w ↦ by
    have := hω_mem w (Set.mem_univ w)
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hω_pos : ∀ (S : Finset PauliWord) (c : PauliWord → ℂ),
      (∀ N, 0 ≤ (∑ w ∈ S, c w * ω N w).re) →
      0 ≤ (∑ w ∈ S, c w * ω_inf w).re := by
    intro S c hpos
    have hsum_tend : Filter.Tendsto (fun k ↦ (∑ w ∈ S, c w * ω (φ k) w).re)
        Filter.atTop (nhds (∑ w ∈ S, c w * ω_inf w).re) := by
      have hc : Filter.Tendsto (fun k ↦ ∑ w ∈ S, c w * ω (φ k) w)
          Filter.atTop (nhds (∑ w ∈ S, c w * ω_inf w)) :=
        tendsto_finset_sum S fun w _ ↦ (hpt w).const_mul (c w)
      exact Complex.continuous_re.continuousAt.tendsto.comp hc
    exact ge_of_tendsto' hsum_tend fun k ↦ hpos (φ k)
  exact ⟨ω_inf, φ, hφ_mono, hpt, hω_one, hω_bound, hω_pos⟩

/-- **Thermodynamic-Limit KMS Boundary Transfer**:
If finite-volume correlation functions `F_k, G_k` satisfy the finite-volume KMS boundary
condition `F_k(t + i β) = G_k(t)` and converge pointwise to `F_∞, G_∞`, then `F_∞` and `G_∞`
satisfy the exact thermodynamic-limit KMS boundary condition `F_∞(t + i β) = G_∞(t)`. -/
theorem thermo_limit_kms_boundary_transfer
    (F : ℕ → ℂ → ℂ) (G : ℕ → ℝ → ℂ) (F_inf : ℂ → ℂ) (G_inf : ℝ → ℂ) (β : ℝ)
    (hkms : ∀ k (t : ℝ), F k ((t : ℂ) + Complex.I * (β : ℂ)) = G k t)
    (hF : ∀ t : ℝ, Filter.Tendsto (fun k ↦ F k ((t : ℂ) + Complex.I * (β : ℂ)))
      Filter.atTop (nhds (F_inf ((t : ℂ) + Complex.I * (β : ℂ)))))
    (hG : ∀ t : ℝ, Filter.Tendsto (fun k ↦ G k t) Filter.atTop (nhds (G_inf t))) :
    ∀ t : ℝ, F_inf ((t : ℂ) + Complex.I * (β : ℂ)) = G_inf t := by
  intro t
  have h1 := hF t
  have h2 : Filter.Tendsto (fun k ↦ F k ((t : ℂ) + Complex.I * (β : ℂ)))
      Filter.atTop (nhds (G_inf t)) := by
    simpa [hkms] using hG t
  exact tendsto_nhds_unique h1 h2

end ThermodynamicLimitStates

end KrylovChaos
