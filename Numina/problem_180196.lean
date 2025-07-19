-- https://cloud.kili-technology.com/label/projects/label/cm8cszy9501rd5kaylgcpqvus

import Mathlib

open Real

/- Show $\frac{1}{2} + \log_{9} x - \log_{3}(5 x) > \log_{\frac{1}{3}}(x+3)$. -/

theorem algebra_180196 {x : ℝ} (hx : 0 < x) :
    1/2 + logb 9 x - logb 3 (5 * x) > logb (1/3) (x + 3) := by
  simp only [one_div, gt_iff_lt]
  -- Multiply through by two.
  suffices 2 * logb 3⁻¹ (x + 3) < 1 + 2 * logb 9 x - 2 * logb 3 (5 * x) by
    rw [← mul_lt_mul_left two_pos]
    convert this using 1
    simp [mul_sub, mul_add]
  -- Gather the logs on one side.
  refine lt_tsub_of_add_lt_right ?_
  refine lt_add_of_tsub_lt_right ?_

  -- We will need `0 < x + 3` to manipulate the logs.
  have hx3 : 0 < x + 3 := by linarith

  calc _
  -- Change all logs to base 3: log_(1/3) x = log_3 x / (-1), log_9 x = log_3 x / 2.
  _ = -2 * logb 3 (x + 3) + 2 * logb 3 (5 * x) - logb 3 x := by
    congr 1
    · congr 1
      simp only [← log_div_log]
      simp [div_neg]
    · simp only [← log_div_log]
      rw [mul_comm, div_mul]
      congr
      calc log 9 / 2
      _ = log (3 ^ 2) / 2 := by norm_num
      _ = log 3 := by simp
  -- Combine the addition and subtraction of logs.
  _ = 2 * logb 3 (5 * x) - (2 * logb 3 (x + 3) + logb 3 x) := by ring
  _ = logb 3 ((5 * x) ^ 2 / ((x + 3) ^ 2 * x)) := by
    rw [logb_div (by simp [hx.ne']) (by simp [hx.ne', hx3.ne'])]
    congr 1
    · simp [logb_pow]
    · rw [logb_mul (by simp [hx3.ne']) (by simp [hx.ne'])]
      simp [logb_pow]
  -- Eliminate the common factor of x.
  _ = logb 3 (25 * x * x / ((x + 3) ^ 2 * x)) := by
    congr
    ring
  _ = logb 3 (25 * x / ((x + 3) ^ 2)) := by
    congr 1
    exact mul_div_mul_right _ _ hx.ne'
  _ < logb 3 3 := by
    refine logb_lt_logb (by norm_num) ?_ ?_
    · simp [hx, hx3]
    refine (div_lt_iff₀ ?_).mpr ?_
    · simp [hx3]
    -- Put into standard quadratic form.
    rw [← sub_pos]
    suffices 0 < 3 * (x * x) + -7 * x + 27 by
      convert this using 1
      ring
    -- Now it suffices to show that `b^2 - 4ac < 0` and `0 < a`.
    suffices ∀ a b c : ℝ, 0 < a → discrim a b c < 0 → ∀ x, 0 < a * (x * x) + b * x + c by
      refine this 3 (-7) 27 (by norm_num) ?_ x
      rw [discrim]
      norm_num
    intro a b c ha h x
    calc a * (x * x) + b * x + c
    _ = (4 * a) * (a * (x * x) + b * x + c) / (4 * a) :=
      (mul_div_cancel_left₀ _ (by simpa using ha.ne')).symm
    _ = ((2 * a * x + b) ^ 2 - discrim a b c) / (4 * a) := by
      congr
      rw [discrim]
      ring
    _ > 0 := by simpa [ha] using h.trans_le (sq_nonneg _)
  _ = 1 := logb_self_eq_one (by norm_num)
