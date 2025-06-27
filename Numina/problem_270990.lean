-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9y000xueaxfondxlk0

import Mathlib

open Real
open scoped Nat

/- Show that the equation
$$
1 + x + \frac{x^{2}}{2!} + \frac{x^{3}}{3!} + \cdots + \frac{x^{2 n}}{(2 n)!} = 0
$$
has no real roots. -/

lemma exp_remainder_lagrange_of_neg {x : ℝ} (hx : x < 0) (n : ℕ) :
    ∃ ξ ∈ Set.Ioo x 0, exp x =
      ∑ i in Finset.range (n + 1), x ^ i / i ! + exp ξ * (x ^ (n + 1) / (n + 1)!) := by
  have hx' : 0 < -x := by simpa using hx
  have := taylor_mean_remainder_lagrange (f := fun x ↦ exp (-x)) (n := n) hx'
    contDiff_neg.exp.contDiffOn
    (by
      refine DifferentiableOn.mono ?_ Set.Ioo_subset_Icc_self
      exact contDiff_neg.exp.contDiffOn.differentiableOn_iteratedDerivWithin
        (WithTop.coe_lt_top _) (uniqueDiffOn_Icc hx'))
  simp only at this
  rcases this with ⟨ξ, hξ_mem, hξ⟩
  refine ⟨-ξ, ?_, ?_⟩
  · rw [Set.neg_mem_Ioo_iff]
    simpa using hξ_mem
  rw [sub_eq_iff_eq_add'] at hξ
  convert hξ using 2
  · simp
  · -- TODO: simps
    simp only [taylorWithinEval, taylorWithin, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [PolynomialModule.comp_eval]
    simp [taylorCoeffWithin]
    suffices iteratedDerivWithin i (fun x ↦ rexp (-x)) (Set.Icc 0 (-x)) 0 = (-1) ^ i by
      simp [this]
      ring_nf  -- TODO
      simp [mul_comm _ 2]
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin]
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc hx')]
    rotate_left
    · exact contDiff_neg.exp.contDiffAt
    · simpa using hx'.le
    rw [← iteratedDeriv_eq_iteratedFDeriv]
    simpa using funext_iff.mp (iteratedDeriv_exp_const_mul i (-1)) 0
  · simp
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin]
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc hx')]
    rotate_left
    · exact contDiff_neg.exp.contDiffAt
    · exact Set.mem_Icc_of_Ioo hξ_mem
    rw [← iteratedDeriv_eq_iteratedFDeriv]
    have := funext_iff.mp (iteratedDeriv_exp_const_mul (n + 1) (-1)) ξ
    simp at this
    rw [this]
    ring_nf
    simp [mul_comm _ 2]

theorem algebra_270990 (n : ℕ) :
    ¬∃ x : ℝ, ∑ i ∈ Finset.range (2 * n + 1), x ^ i / (Nat.factorial i) = 0 := by
  rw [not_exists]
  intro x
  refine ne_of_gt ?_
  -- We know that `x` must be negative. Otherwise, the sum would be at least 1.
  cases lt_or_le x 0 with
  | inr hx =>
    rw [Finset.sum_range_succ']
    refine add_pos_of_nonneg_of_pos ?_ (by simp)
    exact Finset.sum_nonneg fun i hi ↦ by simp [div_nonneg, hx]
  | inl hx =>

    have := exp_remainder_lagrange_of_neg hx (2 * n)
    rcases this with ⟨ξ, hξ_mem, hξ⟩

    rw [← sub_eq_iff_eq_add] at hξ
    rw [← hξ]
    rw [sub_pos]
    refine lt_trans ?_ (exp_pos x)
    refine mul_neg_of_pos_of_neg (exp_pos ξ) ?_
    refine div_neg_of_neg_of_pos ?_ (by simpa using Nat.factorial_pos _)
    exact Odd.pow_neg (odd_two_mul_add_one n) hx
