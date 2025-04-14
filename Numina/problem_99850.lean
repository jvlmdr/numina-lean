-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi4002m4nay8o1n2fkb

import Mathlib

open Real MeasureTheory

/- Determine the family of primitives
$$ I = \int \frac{x \ln \left(1 + \sqrt{1 + x^{2}}\right)}{\sqrt{1+x^{2}}} d x $$
-/

theorem calculus_99850 (a x : ℝ) :
    ∃ c, ∫ x in a..x, x * log (1 + √(1 + x ^ 2)) / √(1 + x ^ 2) =
      (1 + √(1 + x ^ 2)) * log (1 + √(1 + x ^ 2)) - √(1 + x ^ 2) + c := by
  -- Use `-f a` as the constant.
  use -((1 + √(1 + a ^ 2)) * log (1 + √(1 + a ^ 2)) - √(1 + a ^ 2))
  rw [← sub_eq_add_neg]

  -- Let `y = √(1 + x^2)`, then `dy/dx = x / √(1 + x^2)` and we can see that
  -- `I = ∫ x log (1 + √(1 + x^2)) / √(1 + x^2) dx = ∫ dy log (1 + y) dy`.
  convert intervalIntegral.integral_comp_mul_deriv' (a := a) (b := x) (g := fun y ↦ log (1 + y))
      (f := fun x ↦ √(1 + x ^ 2)) (f' := fun x ↦ x / √(1 + x ^ 2)) ?_ ?_ ?_ using 3 with x
  rotate_left 2
  · -- d/dx √(1 + x ^ 2) = x / √(1 + x ^ 2)
    intro u _
    convert HasDerivAt.sqrt (f' := 2 * u) ?_ ?_ using 1
    · ring
    · refine .const_add _ ?_
      simpa using hasDerivAt_pow 2 u
    · refine ne_of_gt ?_
      exact add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)
  · refine Continuous.continuousOn ?_
    refine .div continuous_id' (.sqrt <| .add continuous_const <| continuous_pow 2) fun u ↦ ?_
    refine ne_of_gt <| sqrt_pos.mpr ?_
    exact add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)
  · refine ContinuousOn.log (continuous_add_left 1).continuousOn fun u ↦ ?_
    simp only [Set.mem_image, forall_exists_index, and_imp]
    rintro v _ rfl
    refine ne_of_gt ?_
    exact add_pos_of_pos_of_nonneg one_pos (sqrt_nonneg _)

  · -- Demonstrate that the composition is valid.
    rw [Function.comp_def]
    ring
  -- Then it remains to find the integral of `log (1 + y)`.
  generalize ha' : √(1 + a ^ 2) = a'
  generalize hy : √(1 + x ^ 2) = y
  replace ha' : 0 ≤ a' := ha' ▸ sqrt_nonneg (1 + a ^ 2)
  replace hy : 0 ≤ y := hy ▸ sqrt_nonneg (1 + x ^ 2)
  -- Need to prove that `1 + v ≠ 0` for the integral to be valid.
  have h_one_add {v} (hv : v ∈ Set.uIcc a' y) : 0 < 1 + v := by
    refine add_pos_of_pos_of_nonneg one_pos ?_
    refine le_trans (le_min ha' hy) (inf_le_iff.mpr ?_)
    exact (Set.mem_uIcc.mp hv).imp And.left And.left
  -- Use integration by parts with `u = log (1 + y)`, `v' = 1`, `u' = (1 + y)⁻¹`, `v = 1 + y`.
  symm
  convert intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a') (b := y)
    (u := fun x ↦ log (1 + x)) (u' := fun x ↦ (1 + x)⁻¹) ?_
    (fun v _ ↦ .const_add 1 (hasDerivAt_id' v)) ?_ intervalIntegrable_const using 1
  · simp
  · suffices ∫ y in a'..y, (1 + y)⁻¹ * (1 + y) = (y - a') by
      rw [this]
      ring
    calc _
    _ = ∫ y in a'..y, (1 : ℝ) := by
      refine intervalIntegral.integral_congr fun v hv ↦ ?_
      exact inv_mul_cancel₀ (h_one_add hv).ne'
    _ = _ := integral_one
  · -- d/dy (log (1 + y)) = (1 + y)⁻¹
    intro v hv
    simpa using HasDerivAt.log ((hasDerivAt_id' v).const_add 1) (h_one_add hv).ne'
  · suffices IntervalIntegrable (fun x ↦ (x - -1)⁻¹) volume a' y by
      convert this using 2 with u
      ring
    rw [intervalIntegrable_sub_inv_iff]
    refine .inr <| Set.not_mem_uIcc_of_lt ?_ ?_
    · exact neg_one_lt_zero.trans_le ha'
    · exact neg_one_lt_zero.trans_le hy
