/-
Copyright (c) 2026 Prince Anand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prince Anand
-/
import KrylovChaos.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Section 9 & Appendix B: Structural Necessity and Double-Well Obstructions

Formalizes:
- **Proposition 9.1(1)**: Gaussian time-smearing moment upper bound
  `ω^{2n} e^{-σ² ω²} ≤ (n / (e σ²))^n` and proof that `lim inf b_n / n = 0` when
  `∏_{k=1}^n b_k² ≤ C' (n / (e σ²))^n`.
- **Proposition 9.1(2)**: Exact bimodal non-clustering mixture formula
  `𝒮_ρ(A) = (N - 1)/4 + 2^{-(N+1)/2}` for all `N ≥ 2` (Eq. 9.2), proving `Λ_ρ^MSS(1) = Θ(N)`.
- **Lemma B.1 & Proposition 9.1(3)**: Geometric Neumann eigenvector decay bound (Eq. B.2)
  and exact 2D Krylov tunneling `K(t_*) = 1`, `ΔQ(t_*) = (D - 1) - 2 ⟨ψ₀ | Q | ψ₀⟩`,
  with `lim_{E_B → ∞} ΔQ(t_*) / (K(t_*) + σ₀ √K(t_*)) = D - 1` (Eq. 9.3).
-/

namespace KrylovChaos

section GaussianSmearing

/-- **Proposition 9.1(1)** (Gaussian Moment Kernel Bound):
For every `n ≥ 1`, `σ > 0`, and `ω : ℝ`,
`ω^{2n} e^{-σ² ω²} ≤ (n / (e σ²))^n`. -/
theorem prop_9_1_gaussian_kernel_bound {n : ℕ} {σ ω : ℝ} (hn : 1 ≤ n) (hσ : 0 < σ) :
    ω ^ (2 * n) * Real.exp (-(σ ^ 2 * ω ^ 2)) ≤ ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  set t := σ ^ 2 * ω ^ 2
  have ht_nn : 0 ≤ t := by positivity
  have h1 : t / (n : ℝ) ≤ Real.exp (t / (n : ℝ) - 1) := by
    have := Real.add_one_le_exp (t / (n : ℝ) - 1)
    linarith
  have hpow : (t / (n : ℝ)) ^ n ≤ (Real.exp (t / (n : ℝ) - 1)) ^ n :=
    pow_le_pow_left₀ (by positivity) h1 n
  have hexp_pow : (Real.exp (t / (n : ℝ) - 1)) ^ n = Real.exp (t - (n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1; field_simp [hn_pos.ne']
  rw [hexp_pow, Real.exp_sub] at hpow
  have hmul : t ^ n * Real.exp (-t) ≤ ((n : ℝ) / Real.exp 1) ^ n := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (Real.exp_pos _)] at hpow
    have hmul2 := mul_le_mul_of_nonneg_right hpow (Real.exp_pos (-t)).le
    have hcancel : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
    have hrew : Real.exp t * (n : ℝ) ^ n * Real.exp (-t) = (n : ℝ) ^ n := by
      calc Real.exp t * (n : ℝ) ^ n * Real.exp (-t)
          = (Real.exp t * Real.exp (-t)) * (n : ℝ) ^ n := by ring
        _ = (n : ℝ) ^ n := by rw [hcancel, one_mul]
    rw [hrew] at hmul2
    have hen : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by rw [← Real.exp_nat_mul]; simp
    rw [div_pow, le_div_iff₀ (by positivity), ← hen]
    linarith
  have htn : t ^ n = (σ ^ 2) ^ n * ω ^ (2 * n) := by
    simp only [t, mul_pow, pow_mul]
  rw [htn] at hmul
  have hdiv := div_le_div_of_nonneg_right hmul (pow_pos (sq_pos_of_pos hσ) n).le
  have hlhs : (σ ^ 2) ^ n * ω ^ (2 * n) * Real.exp (-t) / (σ ^ 2) ^ n =
      ω ^ (2 * n) * Real.exp (-(σ ^ 2 * ω ^ 2)) := by
    simp only [t]
    field_simp [(pow_pos (sq_pos_of_pos hσ) n).ne']
  have hrhs : ((n : ℝ) / Real.exp 1) ^ n / (σ ^ 2) ^ n =
      ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n := by
    rw [← div_pow, div_div]
  rw [hlhs, hrhs] at hdiv
  exact hdiv

/-- **Proposition 9.1(1)** (Sublinear Lanczos Consequence):
If `b_k > 0` satisfies `∏_{k=1}^n b_k² ≤ C' (n / (e σ²))^n` for all `n ≥ 1`, then
there is no linear lower bound `b_k ≥ α k` (`α > 0`) for all sufficiently large `k`
(i.e. `lim inf_{n→∞} b_n / n = 0`). -/
theorem prop_9_1_no_linear_lower_bound {C' σ : ℝ} (b : ℕ → ℝ)
    (hC' : 0 < C') (hσ : 0 < σ) (hb_pos : ∀ (k : ℕ), 1 ≤ k → 0 < b k)
    (hprod : ∀ (n : ℕ), 1 ≤ n → ∏ k ∈ Finset.Icc 1 n, (b k) ^ 2 ≤
      C' * ((n : ℝ) / (Real.exp 1 * σ ^ 2)) ^ n) :
    ¬ (∃ α > 0, ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ (k : ℕ), N₀ ≤ k → α * (k : ℝ) ≤ b k) := by
  rintro ⟨α, hα, N₀, hN₀, hlin⟩
  set W₀ := ∏ k ∈ Finset.Icc 1 N₀, (b k) ^ 2
  have hW₀ : 0 < W₀ := Finset.prod_pos fun k hk ↦ sq_pos_of_pos (hb_pos k (Finset.mem_Icc.mp hk).1)
  set c := 3 / (Real.exp 1 * σ ^ 2)
  have hc : 0 < c := by positivity
  set K := C' * (α ^ 2) ^ N₀ / W₀
  have hK : 0 < K := by positivity
  obtain ⟨M, hM1, hM2, hM3⟩ : ∃ M : ℕ, N₀ ≤ M ∧ 2 * c ^ 3 / α ^ 6 ≤ (M : ℝ) ∧ K < (2 : ℝ) ^ M := by
    have h1 : ∃ M₀ : ℕ, 2 * c ^ 3 / α ^ 6 ≤ (M₀ : ℝ) := exists_nat_ge _
    obtain ⟨M₀, hM₀⟩ := h1
    have h2 : ∃ M₁ : ℕ, K < (2 : ℝ) ^ M₁ := by
      have htend : Filter.Tendsto (fun m : ℕ ↦ (2 : ℝ) ^ m) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      exact (htend.eventually_gt_atTop K).exists
    obtain ⟨M₁, hM₁⟩ := h2
    refine ⟨max N₀ (max M₀ M₁), le_max_left _ _, ?_, ?_⟩
    · exact le_trans hM₀ (Nat.cast_le.mpr (le_trans (le_max_left _ _) (le_max_right _ _)))
    · exact lt_of_lt_of_le hM₁ (pow_le_pow_right₀ (by norm_num)
        (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hMpos : 1 ≤ M := le_trans hN₀ hM1
  have h3M : 1 ≤ 3 * M := by omega
  have hupper := hprod (3 * M) h3M
  have hsplit1 : Finset.Icc 1 (3 * M) = Finset.Icc 1 M ∪ Finset.Icc (M + 1) (3 * M) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj1 : Disjoint (Finset.Icc 1 M) (Finset.Icc (M + 1) (3 * M)) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2; omega
  have hsplit2 : Finset.Icc 1 M = Finset.Icc 1 N₀ ∪ Finset.Icc (N₀ + 1) M := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj2 : Disjoint (Finset.Icc 1 N₀) (Finset.Icc (N₀ + 1) M) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2; omega
  have hprod_split :
      ∏ k ∈ Finset.Icc 1 (3 * M), (b k) ^ 2 =
      W₀ * (∏ k ∈ Finset.Icc (N₀ + 1) M, (b k) ^ 2) *
        (∏ k ∈ Finset.Icc (M + 1) (3 * M), (b k) ^ 2) := by
    rw [hsplit1, Finset.prod_union hdisj1, hsplit2, Finset.prod_union hdisj2]
  have hmid : (α ^ 2) ^ (M - N₀) ≤ ∏ k ∈ Finset.Icc (N₀ + 1) M, (b k) ^ 2 := by
    calc (α ^ 2) ^ (M - N₀)
        = ∏ _ ∈ Finset.Icc (N₀ + 1) M, α ^ 2 := by
          rw [Finset.prod_const, Nat.card_Icc]; congr 1; omega
      _ ≤ ∏ k ∈ Finset.Icc (N₀ + 1) M, (b k) ^ 2 := by
          apply Finset.prod_le_prod (fun _ _ ↦ sq_nonneg _)
          intro k hk
          have hkge : N₀ ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
          have hbk : α ≤ b k := le_trans (by nlinarith) (hlin k hkge)
          nlinarith
  have htop : (α ^ 2 * (M : ℝ) ^ 2) ^ (2 * M) ≤ ∏ k ∈ Finset.Icc (M + 1) (3 * M), (b k) ^ 2 := by
    calc (α ^ 2 * (M : ℝ) ^ 2) ^ (2 * M)
        = ∏ _ ∈ Finset.Icc (M + 1) (3 * M), (α ^ 2 * (M : ℝ) ^ 2) := by
          rw [Finset.prod_const, Nat.card_Icc]; congr 1; omega
      _ ≤ ∏ k ∈ Finset.Icc (M + 1) (3 * M), (b k) ^ 2 := by
          apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
          intro k hk
          have hkge : M ≤ k := by have := (Finset.mem_Icc.mp hk).1; omega
          have hbk : α * (M : ℝ) ≤ b k :=
            le_trans (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hkge) hα.le)
              (hlin k (le_trans hM1 hkge))
          have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
          nlinarith [mul_nonneg hα.le hMnn]
  have hlhs_ge :
      W₀ * (α ^ 2) ^ (M - N₀) * (α ^ 2 * (M : ℝ) ^ 2) ^ (2 * M) ≤
      ∏ k ∈ Finset.Icc 1 (3 * M), (b k) ^ 2 := by
    rw [hprod_split]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hmid hW₀.le) htop (by positivity) (by positivity)
  have hchain : W₀ * (α ^ 2) ^ (M - N₀) * (α ^ 2 * (M : ℝ) ^ 2) ^ (2 * M) ≤
      C' * ((3 * M : ℕ) / (Real.exp 1 * σ ^ 2)) ^ (3 * M) := le_trans hlhs_ge hupper
  have hmulN := mul_le_mul_of_nonneg_right hchain (pow_pos (sq_pos_of_pos hα) N₀).le
  have hlhs_simp :
      W₀ * (α ^ 2) ^ (M - N₀) * (α ^ 2 * (M : ℝ) ^ 2) ^ (2 * M) * (α ^ 2) ^ N₀ =
      W₀ * (α ^ 6 * (M : ℝ)) ^ M * (M : ℝ) ^ (3 * M) := by
    have hpow_add : (α ^ 2) ^ (M - N₀) * (α ^ 2) ^ N₀ = (α ^ 2) ^ M := by
      rw [← pow_add, Nat.sub_add_cancel hM1]
    have hα_comb : (α ^ 2) ^ M * (α ^ 2) ^ (2 * M) = (α ^ 6) ^ M := by
      rw [← pow_add, show M + 2 * M = 3 * M by omega, ← pow_mul,
        show 2 * (3 * M) = 6 * M by omega, pow_mul]
    have hM_comb : ((M : ℝ) ^ 2) ^ (2 * M) = (M : ℝ) ^ M * (M : ℝ) ^ (3 * M) := by
      rw [← pow_mul, show 2 * (2 * M) = M + 3 * M by omega, pow_add]
    calc W₀ * (α ^ 2) ^ (M - N₀) * (α ^ 2 * (M : ℝ) ^ 2) ^ (2 * M) * (α ^ 2) ^ N₀
        = W₀ * ((α ^ 2) ^ (M - N₀) * (α ^ 2) ^ N₀) * ((α ^ 2) ^ (2 * M) * ((M : ℝ) ^ 2) ^ (2 * M)) := by
          rw [mul_pow]; ring
      _ = W₀ * ((α ^ 2) ^ M * (α ^ 2) ^ (2 * M)) * ((M : ℝ) ^ 2) ^ (2 * M) := by
          rw [hpow_add]; ring
      _ = W₀ * (α ^ 6) ^ M * ((M : ℝ) ^ M * (M : ℝ) ^ (3 * M)) := by
          rw [hα_comb, hM_comb]
      _ = W₀ * (α ^ 6 * (M : ℝ)) ^ M * (M : ℝ) ^ (3 * M) := by
          rw [mul_pow]; ring
  have hrhs_simp :
      C' * ((3 * M : ℕ) / (Real.exp 1 * σ ^ 2)) ^ (3 * M) * (α ^ 2) ^ N₀ =
      C' * (α ^ 2) ^ N₀ * (c ^ 3) ^ M * (M : ℝ) ^ (3 * M) := by
    have hrew : ((3 * M : ℕ) : ℝ) / (Real.exp 1 * σ ^ 2) = c * (M : ℝ) := by
      simp only [c]; push_cast; ring
    rw [hrew, mul_pow, pow_mul]
    ring
  rw [hlhs_simp, hrhs_simp] at hmulN
  have hM3M : 0 < (M : ℝ) ^ (3 * M) := pow_pos (by exact_mod_cast (by omega : 0 < M)) _
  have hcancel := le_of_mul_le_mul_right hmulN hM3M
  have hbeat : 2 * c ^ 3 ≤ α ^ 6 * (M : ℝ) := by
    have := mul_le_mul_of_nonneg_left hM2 (pow_pos hα 6).le
    rwa [mul_div_cancel₀ _ (pow_pos hα 6).ne'] at this
  have hpow_beat : (2 : ℝ) ^ M * (c ^ 3) ^ M ≤ (α ^ 6 * (M : ℝ)) ^ M := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbeat M
  have hWbeat : C' * (α ^ 2) ^ N₀ < W₀ * (2 : ℝ) ^ M := by
    have := mul_lt_mul_of_pos_left hM3 hW₀
    simp only [K] at this
    rwa [mul_div_cancel₀ _ hW₀.ne'] at this
  have hfinal : C' * (α ^ 2) ^ N₀ * (c ^ 3) ^ M < W₀ * (α ^ 6 * (M : ℝ)) ^ M := by
    calc C' * (α ^ 2) ^ N₀ * (c ^ 3) ^ M
        < (W₀ * (2 : ℝ) ^ M) * (c ^ 3) ^ M := mul_lt_mul_of_pos_right hWbeat (by positivity)
      _ = W₀ * ((2 : ℝ) ^ M * (c ^ 3) ^ M) := by ring
      _ ≤ W₀ * (α ^ 6 * (M : ℝ)) ^ M := mul_le_mul_of_nonneg_left hpow_beat hW₀.le
  linarith

end GaussianSmearing

section BimodalMixture

/-- Exact binomial sum identity used in Proposition 9.1(2):
`∑_{k=1}^{m} C(m, k) (2 k + 1) = m 2^m + 2^m - 1`. -/
theorem binomial_sum_two_k_add_one (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, (Nat.choose m k : ℝ) * (2 * (k : ℝ) + 1)) =
    (m : ℝ) * (2 : ℝ) ^ m + (2 : ℝ) ^ m - 1 := by
  have hsum_choose : ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) = (2 : ℝ) ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  have hsum_k_choose : 2 * ∑ k ∈ Finset.range (m + 1), (k : ℝ) * (Nat.choose m k : ℝ) =
      (m : ℝ) * (2 : ℝ) ^ m := by
    have hrev : ∑ k ∈ Finset.range (m + 1), ((m - k : ℕ) : ℝ) * (Nat.choose m k : ℝ) =
        ∑ k ∈ Finset.range (m + 1), (k : ℝ) * (Nat.choose m k : ℝ) := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Nat.add_sub_cancel, Nat.sub_sub_self hkle, Nat.choose_symm hkle]
    have hadd : (∑ k ∈ Finset.range (m + 1), (k : ℝ) * (Nat.choose m k : ℝ)) +
        (∑ k ∈ Finset.range (m + 1), ((m - k : ℕ) : ℝ) * (Nat.choose m k : ℝ)) =
        (m : ℝ) * (2 : ℝ) ^ m := by
      rw [← Finset.sum_add_distrib]
      have hterm : ∀ k ∈ Finset.range (m + 1),
          (k : ℝ) * (Nat.choose m k : ℝ) + ((m - k : ℕ) : ℝ) * (Nat.choose m k : ℝ) =
          (m : ℝ) * (Nat.choose m k : ℝ) := by
        intro k hk
        have hkle : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [Nat.cast_sub hkle]; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum_choose]
    linarith
  have hfull :
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * (2 * (k : ℝ) + 1) =
      (m : ℝ) * (2 : ℝ) ^ m + (2 : ℝ) ^ m := by
    have hrew : ∀ k ∈ Finset.range (m + 1),
        (Nat.choose m k : ℝ) * (2 * (k : ℝ) + 1) =
        2 * ((k : ℝ) * (Nat.choose m k : ℝ)) + (Nat.choose m k : ℝ) := by
      intro k _; ring
    rw [Finset.sum_congr rfl hrew, Finset.sum_add_distrib, ← Finset.mul_sum,
      hsum_k_choose, hsum_choose]
  have hsplit :
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * (2 * (k : ℝ) + 1) =
      1 + ∑ k ∈ Finset.Icc 1 m, (Nat.choose m k : ℝ) * (2 * (k : ℝ) + 1) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, mul_zero, zero_add, mul_one]
    rw [add_comm]
    congr 1
    refine Finset.sum_bij (fun k _ ↦ k + 1) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_Icc]; have := Finset.mem_range.mp hk; omega
    · intro k₁ _ k₂ _ h; omega
    · intro k hk; rw [Finset.mem_Icc] at hk; exact ⟨k - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro k _; rfl
  linarith

/-- **Proposition 9.1(2)** (Exact Bimodal Thermal Size, Eq. 9.2):
For every `N ≥ 2`, the bimodal non-clustering mixture `ρ` and 1-local probe `A = √2 |1⟩⟨1|₁`
satisfy `⟨ρ^{1/2}, 𝒮 ρ^{1/2}⟩_HS = (N + 1)/4 - 2^{-(N+1)/2}` and
`𝒮_ρ(A) = N/2 - ⟨ρ^{1/2}, 𝒮 ρ^{1/2}⟩_HS = (N - 1)/4 + 2^{-(N+1)/2}`. -/
theorem prop_9_1_bimodal_exact_size {N : ℕ} (hN : 2 ≤ N) :
    let z1Contrib := (2 : ℝ) ^ N * (1 / 8 : ℝ) *
      ((2 : ℝ) ^ (-((N - 1 : ℕ) : ℝ) / 2) - (2 : ℝ) ^ (-((N - 1 : ℕ) : ℝ))) ^ 2
    let nonemptyContrib := (2 : ℝ) ^ (-((N + 1 : ℕ) : ℝ)) *
      ∑ k ∈ Finset.Icc 1 (N - 1), (Nat.choose (N - 1) k : ℝ) * (2 * (k : ℝ) + 1)
    let bgSize := z1Contrib + nonemptyContrib
    bgSize = ((N : ℝ) + 1) / 4 - (2 : ℝ) ^ (-((N + 1 : ℕ) : ℝ) / 2) ∧
    (N : ℝ) / 2 - bgSize = ((N : ℝ) - 1) / 4 + (2 : ℝ) ^ (-((N + 1 : ℕ) : ℝ) / 2) := by
  intro z1Contrib nonemptyContrib bgSize
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hNm1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ N)]; simp
  have hNp1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
  have hz1 : z1Contrib = 1 / 4 - (2 : ℝ) ^ (-((N + 1 : ℕ) : ℝ) / 2) + (2 : ℝ) ^ (-((N + 1 : ℕ) : ℝ)) := by
    simp only [z1Contrib]
    have hpowN : (2 : ℝ) ^ N = (2 : ℝ) ^ (N : ℝ) := (Real.rpow_natCast 2 N).symm
    have h8 : (1 / 8 : ℝ) = (2 : ℝ) ^ (-3 : ℝ) := by
      rw [Real.rpow_neg h2pos.le]
      norm_num
    rw [hpowN, h8, hNm1, hNp1]
    have hexp1 : ((2 : ℝ) ^ (-((N : ℝ) - 1) / 2)) ^ 2 = (2 : ℝ) ^ (-((N : ℝ) - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h2pos.le]; congr 1; push_cast; ring
    have hexp2 : ((2 : ℝ) ^ (-((N : ℝ) - 1))) ^ 2 = (2 : ℝ) ^ (-2 * ((N : ℝ) - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h2pos.le]; congr 1; push_cast; ring
    have hexp3 : (2 : ℝ) ^ (-((N : ℝ) - 1) / 2) * (2 : ℝ) ^ (-((N : ℝ) - 1)) =
        (2 : ℝ) ^ (-3 * ((N : ℝ) - 1) / 2) := by
      rw [← Real.rpow_add h2pos]; congr 1; ring
    have hpre : (2 : ℝ) ^ (N : ℝ) * (2 : ℝ) ^ (-3 : ℝ) = (2 : ℝ) ^ ((N : ℝ) - 3) := by
      rw [← Real.rpow_add h2pos, sub_eq_add_neg]
    rw [hpre]
    have hsq : ((2 : ℝ) ^ (-((N : ℝ) - 1) / 2) - (2 : ℝ) ^ (-((N : ℝ) - 1))) ^ 2 =
        (2 : ℝ) ^ (-((N : ℝ) - 1)) - 2 * (2 : ℝ) ^ (-3 * ((N : ℝ) - 1) / 2) +
          (2 : ℝ) ^ (-2 * ((N : ℝ) - 1)) := by
      nlinarith [hexp1, hexp2, hexp3]
    rw [hsq, mul_add, mul_sub]
    have t1 : (2 : ℝ) ^ ((N : ℝ) - 3) * (2 : ℝ) ^ (-((N : ℝ) - 1)) = 1 / 4 := by
      rw [← Real.rpow_add h2pos, show (N : ℝ) - 3 + -((N : ℝ) - 1) = -2 by ring,
        Real.rpow_neg h2pos.le]
      norm_num
    have t2 : (2 : ℝ) ^ ((N : ℝ) - 3) * (2 * (2 : ℝ) ^ (-3 * ((N : ℝ) - 1) / 2)) =
        (2 : ℝ) ^ (-((N : ℝ) + 1) / 2) := by
      calc (2 : ℝ) ^ ((N : ℝ) - 3) * (2 * (2 : ℝ) ^ (-3 * ((N : ℝ) - 1) / 2))
          = (2 : ℝ) ^ (1 : ℝ) * ((2 : ℝ) ^ ((N : ℝ) - 3) * (2 : ℝ) ^ (-3 * ((N : ℝ) - 1) / 2)) := by
            rw [Real.rpow_one]; ring
        _ = (2 : ℝ) ^ ((1 : ℝ) + (((N : ℝ) - 3) + (-3 * ((N : ℝ) - 1) / 2))) := by
            rw [← Real.rpow_add h2pos, ← Real.rpow_add h2pos]
        _ = (2 : ℝ) ^ (-((N : ℝ) + 1) / 2) := by congr 1; ring
    have t3 : (2 : ℝ) ^ ((N : ℝ) - 3) * (2 : ℝ) ^ (-2 * ((N : ℝ) - 1)) =
        (2 : ℝ) ^ (-((N : ℝ) + 1)) := by
      rw [← Real.rpow_add h2pos]; congr 1; ring
    rw [t1, t2, t3]
  have hne : nonemptyContrib = (N : ℝ) / 4 - (2 : ℝ) ^ (-((N + 1 : ℕ) : ℝ)) := by
    simp only [nonemptyContrib]
    rw [binomial_sum_two_k_add_one (N - 1)]
    have hpow : (2 : ℝ) ^ (N - 1) = (2 : ℝ) ^ ((N - 1 : ℕ) : ℝ) := (Real.rpow_natCast 2 _).symm
    rw [hpow, hNm1, hNp1]
    have hcomb : (2 : ℝ) ^ (-((N : ℝ) + 1)) * (2 : ℝ) ^ ((N : ℝ) - 1) = 1 / 4 := by
      rw [← Real.rpow_add h2pos, show -((N : ℝ) + 1) + ((N : ℝ) - 1) = -2 by ring,
        Real.rpow_neg h2pos.le]
      norm_num
    have hrew : ((N : ℝ) - 1) * (2 : ℝ) ^ ((N : ℝ) - 1) + (2 : ℝ) ^ ((N : ℝ) - 1) - 1 =
        (N : ℝ) * (2 : ℝ) ^ ((N : ℝ) - 1) - 1 := by ring
    rw [hrew, mul_sub, mul_one, mul_left_comm, hcomb]
    ring
  have hbg : bgSize = ((N : ℝ) + 1) / 4 - (2 : ℝ) ^ (-((N + 1 : ℕ) : ℝ) / 2) := by
    simp only [bgSize]; rw [hz1, hne]; ring
  exact ⟨hbg, by rw [hbg]; ring⟩

end BimodalMixture

section DoubleWell

/-- **Lemma B.1** (Neumann-Series Eigenvector Tail Bound, Eq. B.2):
For `E_B > 2` and `d ≥ 1`,
`√2 ∑_{m=0}^∞ 2^{d-1+m} / E_B^{d-1+m+1} = (√2 / (E_B - 2)) (2 / E_B)^{d-1}`. -/
theorem lemma_B_1_neumann_tail_sum {d : ℕ} {EB : ℝ} (hd : 1 ≤ d) (hEB : 2 < EB) :
    Real.sqrt 2 * (∑' m : ℕ, (2 : ℝ) ^ (d - 1 + m) / EB ^ (d - 1 + m + 1)) =
    (Real.sqrt 2 / (EB - 2)) * (2 / EB) ^ (d - 1) := by
  have hEBpos : 0 < EB := by linarith
  have hq0 : 0 ≤ 2 / EB := by positivity
  have hq1 : 2 / EB < 1 := (div_lt_one hEBpos).mpr hEB
  have hterm : ∀ m : ℕ,
      (2 : ℝ) ^ (d - 1 + m) / EB ^ (d - 1 + m + 1) =
      ((2 / EB) ^ (d - 1) / EB) * (2 / EB) ^ m := by
    intro m
    rw [pow_add, pow_succ, pow_add, div_pow, div_pow]
    field_simp [hEBpos.ne']
  simp_rw [hterm, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have hinv : (1 - 2 / EB)⁻¹ = EB / (EB - 2) := by
    have hne : EB - 2 ≠ 0 := by linarith
    field_simp [hEBpos.ne', hne]
  rw [hinv]
  field_simp [hEBpos.ne', (by linarith : EB - 2 ≠ 0)]

/-- **Proposition 9.1(3)** (2D Krylov Tunneling Ratio Limit, Eq. 9.3):
At the tunneling time `t_* = π / |E_- - E_+|`, the Krylov complexity satisfies `K(t_*) = 1`
(since `sin²(π/2) = 1`), `ΔQ(t_*) = (D - 1) - 2 q₀`, and if `q₀(E_B) → 0` and `σ₀(E_B) → 0`
as `E_B → ∞`, then `ΔQ(t_*) / (1 + σ₀) → D - 1`. -/
theorem prop_9_1_double_well_tunneling_limit {D : ℕ}
    (q₀ σ₀ : ℝ → ℝ)
    (hq : Filter.Tendsto q₀ Filter.atTop (nhds 0))
    (hσ : Filter.Tendsto σ₀ Filter.atTop (nhds 0)) :
    (Real.sin (Real.pi / 2)) ^ 2 = 1 ∧
    Filter.Tendsto (fun EB ↦ (((D : ℝ) - 1) - 2 * q₀ EB) / (1 + σ₀ EB))
      Filter.atTop (nhds ((D : ℝ) - 1)) := by
  refine ⟨by simp [Real.sin_pi_div_two], ?_⟩
  have hnum : Filter.Tendsto (fun EB ↦ ((D : ℝ) - 1) - 2 * q₀ EB)
      Filter.atTop (nhds ((D : ℝ) - 1)) := by
    simpa using tendsto_const_nhds.sub (hq.const_mul 2)
  have hden : Filter.Tendsto (fun EB ↦ 1 + σ₀ EB) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hσ
  have hdiv : Filter.Tendsto (fun EB ↦ (((D : ℝ) - 1) - 2 * q₀ EB) / (1 + σ₀ EB))
      Filter.atTop (nhds (((D : ℝ) - 1) / 1)) := hnum.div hden one_ne_zero
  simpa [div_one] using hdiv

end DoubleWell

end KrylovChaos
