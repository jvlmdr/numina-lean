-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9y000xueaxfondxlk0

import Mathlib

open Real
open scoped Nat

/- Show that the equation
$$
1 + x + \frac{x^{2}}{2!} + \frac{x^{3}}{3!} + \cdots + \frac{x^{2 n}}{(2 n)!} = 0
$$
has no real roots. -/

-- Convenience lemma which only exists for `iteratedFDeriv` in Mathlib.
lemma iteratedDerivWithin_eq_iteratedDeriv {s : Set ℝ} {f : ℝ → ℝ} {x : ℝ} {n : ℕ}
    (hs : UniqueDiffOn ℝ s) (hf : ContDiff ℝ n f) (hxs : x ∈ s) :
    iteratedDerivWithin n f s x = iteratedDeriv n f x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs hf.contDiffAt hxs]
  rw [iteratedDeriv_eq_iteratedFDeriv]

-- Simple lemma for replacing the `nth` derivative of `exp` with `exp` itself.
lemma iteratedDeriv_exp (n : ℕ) : iteratedDeriv n exp = exp := by
  simpa using iteratedDeriv_exp_const_mul n 1

-- Recall that the sum of `x ^ k / k !` is `exp x`.
-- It is trivial to show that this sum is positive for any number of terms with `x ≥ 0`.
-- For `x < 0`, we need to examine the remainder.
-- We cannot use `Antitone.tendsto_le_alternating_series` because the sequence is only monotone
-- decreasing for sufficiently large `n`.
lemma exp_remainder_lagrange_of_neg {x : ℝ} (hx : x < 0) (n : ℕ) :
    ∃ ξ ∈ Set.Ioo x 0, exp x =
      ∑ i in Finset.range (n + 1), x ^ i / i ! + exp ξ * (x ^ (n + 1) / (n + 1)!) := by
  -- Apply `taylor_mean_remainder_lagrange` to `x ↦ f (-x)` on `(0, -x)`.
  have hx : 0 < -x := by simpa using hx
  have := taylor_mean_remainder_lagrange (n := n) hx contDiff_neg.exp.contDiffOn <| by
    refine DifferentiableOn.mono ?_ Set.Ioo_subset_Icc_self
    refine contDiff_neg.exp.contDiffOn.differentiableOn_iteratedDerivWithin (n := ⊤) ?_ ?_
    · exact WithTop.natCast_lt_top n
    · exact uniqueDiffOn_Icc hx
  simp only [neg_neg, sub_zero] at this
  rcases this with ⟨ξ, hξ_mem, hξ⟩
  -- This gives `0 < ξ < -x`, hence use `x < -ξ < 0`.
  refine ⟨-ξ, ?_, ?_⟩
  · rw [Set.neg_mem_Ioo_iff]
    simpa using hξ_mem
  rw [sub_eq_iff_eq_add'] at hξ
  convert hξ using 2
  · -- Show that Taylor series for `exp` is the series given.
    -- simp only [div_eq_mul_inv]
    simp only [taylorWithinEval, taylorWithin, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PolynomialModule.comp_eval]
    suffices iteratedDerivWithin i (fun x ↦ exp (-x)) (Set.Icc 0 (-x)) 0 = (-1) ^ i by
      calc _
      _ = x ^ i / i ! * (-1) ^ (2 * i) := by simp
      _ = (-x) ^ i * ((i ! : ℝ)⁻¹ * (-1) ^ i) := by ring
      _ = _ := by simp [taylorCoeffWithin, this]
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx) contDiff_neg.exp]
    swap
    · simpa using hx.le
    simp [iteratedDeriv_comp_neg, iteratedDeriv_exp]
  · rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx) contDiff_neg.exp]
    swap
    · exact Set.mem_Icc_of_Ioo hξ_mem
    simp only [iteratedDeriv_comp_neg, iteratedDeriv_exp, smul_eq_mul]
    calc _
    _ = exp (-ξ) * (x ^ (n + 1) / (n + 1)!) * (-1) ^ (2 * n) := by simp
    _ = _ := by ring

theorem algebra_270990 (n : ℕ) :
    ¬∃ x : ℝ, ∑ i ∈ Finset.range (2 * n + 1), x ^ i / (Nat.factorial i) = 0 := by
  rw [not_exists]
  intro x
  refine ne_of_gt ?_
  cases lt_or_le x 0 with
  | inr hx =>
    -- When `x` is non-negative, the sum is at least 1.
    rw [Finset.sum_range_succ']
    refine add_pos_of_nonneg_of_pos ?_ (by simp)
    exact Finset.sum_nonneg fun i hi ↦ by simp [div_nonneg, hx]
  | inl hx =>
    -- When `x` is negative, we use the remainder of the Taylor series.
    obtain ⟨ξ, hξ_mem, hξ⟩ := exp_remainder_lagrange_of_neg hx (2 * n)
    suffices exp ξ * (x ^ (2 * n + 1) / (2 * n + 1)!) < 0 by
      rw [← sub_eq_iff_eq_add] at hξ
      rw [← hξ, sub_pos]
      exact lt_trans this (exp_pos x)
    -- We can see that `x ^ (2 * n + 1)` is negative since `2 * n + 1` is odd.
    -- The other factors are positive.
    refine mul_neg_of_pos_of_neg (exp_pos ξ) ?_
    refine div_neg_of_neg_of_pos ?_ (by simpa using Nat.factorial_pos _)
    exact Odd.pow_neg (odd_two_mul_add_one n) hx
