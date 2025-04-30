-- https://cloud.kili-technology.com/label/projects/label/cma1au4rj00hfthv578mlp2l3

import Mathlib

/- Solve the system of equations
10 x^{2} + 5 y^{2} - 2 x y - 38 x - 6 y + 41 = 0
3 x^{2} - 2 y^{2} + 5 x y - 17 x - 6 y + 20 = 0 -/

theorem algebra_159027 {x y : ℝ}
    (h₁ : 10 * x ^ 2 + 5 * y ^ 2 - 2 * x * y - 38 * x - 6 * y + 41 = 0)
    (h₂ : 3 * x ^ 2 - 2 * y ^ 2 + 5 * x * y - 17 * x - 6 * y + 20 = 0) :
    x = 2 ∧ y = 1 := by
  -- Eliminate the product (x y):
  -- Multiply the first equation by 5 and the second equation by 2.
  have : 56 * x ^ 2 - 224 * x + 21 * y ^ 2 - 42 * y + 245 = 0 := by
    convert congrArg₂ (5 * · + 2 * ·) h₁ h₂ using 1
    · ring
    · simp
  -- Remove factor of 7.
  replace : 8 * x ^ 2 - 32 * x + 3 * y ^ 2 - 6 * y + 35 = 0 := by
    convert congrArg (· / 7) this using 1
    · ring
    · simp
  -- Factor the two squares.
  replace : 8 * (x - 2) ^ 2 + 3 * (y - 1) ^ 2 = 0 := by
    convert this using 1
    ring
  suffices 8 * (x - 2) ^ 2 = 0 ∧ 3 * (y - 1) ^ 2 = 0 by
    simpa [sub_eq_zero] using this
  refine (add_eq_zero_iff_of_nonneg ?_ ?_).mp this
  · simpa using sq_nonneg (x - 2)
  · simpa using sq_nonneg (y - 1)
