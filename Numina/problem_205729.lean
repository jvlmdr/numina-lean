-- https://cloud.kili-technology.com/label/projects/label/cm91j40co007fseayqmr9rulb

import Mathlib

open Real

/- Prove the following inequality:
$$ \log _{5} 6 + \log _{6} 7 + \log _{7} 8 + \log _{8} 5 > 4 $$
-/
theorem inequalities_205729 : logb 5 6 + logb 6 7 + logb 7 8 + logb 8 5 > 4 := by
  suffices logb 5 6 + logb 6 7 + logb 7 8 + logb 8 5 - 4 > 0 by simpa using this
  calc _
  -- Examine the difference between each term and 1.
  _ = logb 5 6 - 1 + (logb 6 7 - 1) + (logb 7 8 - 1) + (logb 8 5 - 1) := by ring
  _ = logb 5 (6 / 5) + logb 6 (7 / 6) + logb 7 (8 / 7) + logb 8 (5 / 8) := by simp [Real.logb_div]
  -- The first three terms have an argument greater than 1.
  -- Use the fact that `a < b` implies `logb b x < logb a x` for `x > 1`
  -- to obtain a bound using only base 8.
  _ > logb 8 (6 / 5) + logb 8 (7 / 6) + logb 8 (8 / 7) + logb 8 (5 / 8) := by
    refine add_lt_add_right ?_ _
    suffices ∀ {a b x : ℝ}, 1 < a → 1 < x → a < b → logb b x < logb a x by
      refine add_lt_add (add_lt_add ?_ ?_) ?_ <;> refine this ?_ ?_ ?_ <;> norm_num
    intro a b x ha hx hab
    refine div_lt_div_of_pos_left (log_pos hx) (log_pos ha) ?_
    exact log_lt_log (one_pos.trans ha) hab
  _ = logb 8 (6 / 5 * (7 / 6) * (8 / 7) * (5 / 8)) := by
    rw [Real.logb_mul, Real.logb_mul, Real.logb_mul] <;> norm_num
  _ = 0 := by simp
