-- https://cloud.kili-technology.com/label/projects/label/cma3ygp4o00odahayf8j1xavc

import Mathlib

/- If real numbers $a, b, x, y$ satisfy
$a x + b y = 3$,
$a x^{2} + b y^{2} = 7$,
$a x^{3} + b y^{3} = 16$,
$a x^{4} + b y^{4} = 42$,
find the value of $a x^{5}+b y^{5}$. -/

theorem algebra_250464 (a b x y : ℝ) (h₁ : a * x + b * y = 3) (h₂ : a * x^2 + b * y^2 = 7)
    (h₃ : a * x^3 + b * y^3 = 16) (h₄ : a * x^4 + b * y^4 = 42) :
    a * x^5 + b * y^5 = 20 := by
  -- Multiply by (x + y) to relate the different powers.
  have h₂' : 7 * (x + y) = 16 + 3 * (x * y) := by
    calc _
    _ = (a * x^2 + b * y^2) * (x + y) := by rw [h₂]
    _ = a * x ^ 3 + b * y ^ 3 + (a * x + b * y) * (x * y) := by ring
    _ = _ := by rw [h₁, h₃]
  have h₃' : 16 * (x + y) = 42 + 7 * (x * y) := by
    calc _
    _ = (a * x^3 + b * y^3) * (x + y) := by rw [h₃]
    _ = a * x ^ 4 + b * y ^ 4 + (a * x^2 + b * y^2) * (x * y) := by ring
    _ = _ := by rw [h₄, h₂]

  -- From these two equations, we can determine the values of `x + y` and `x * y`.
  -- First obtain `x * y` in terms of `x + y`.
  have h_mul : x * y = 2 * (x + y) - 10 := by
    symm
    refine sub_eq_of_eq_add' ?_
    convert congrArg₂ (· - 2 * ·) h₃' h₂' using 1 <;> ring
  have h_add : x + y = -14 := by
    have : 7 * (x + y) = -14 + 6 * (x + y) := by
      convert h_mul ▸ h₂' using 1
      ring
    convert sub_eq_iff_eq_add.mpr this using 1
    ring
  replace h_mul : x * y = -38 := by
    convert h_add ▸ h_mul using 1
    norm_num

  -- Now obtain an expression for `a * x^5 + b * y^5` using the same method as above.
  have h₄' : 42 * (x + y) = a * x ^ 5 + b * y ^ 5 + 16 * (x * y) := by
    calc _
    _ = (a * x^4 + b * y^4) * (x + y) := by rw [h₄]
    _ = a * x ^ 5 + b * y ^ 5 + (a * x^3 + b * y^3) * (x * y) := by ring
    _ = _ := by rw [h₃]

  calc _
  _ = 42 * (x + y) - 16 * (x * y) := (sub_eq_iff_eq_add.mpr h₄').symm
  _ = 42 * (-14) - 16 * (-38) := by rw [h_add, h_mul]
  _ = _ := by norm_num
