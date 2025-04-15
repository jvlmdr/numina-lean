-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi3000p4nayo6y6hnqb

import Mathlib

open Real

/- Calculate the indefinite integral:
$$
\int \frac{2 x^{3} + 6 x^{2} + 5 x + 4}{(x - 2)(x + 1)^{3}} d x
$$
-/

theorem calculus_132790 (x : ℝ) (hx : x ≠ 2) (hx' : x ≠ -1) (C : ℝ) :
    HasDerivAt (fun x ↦ 2 * log |x - 2| + 1 / (2 * (x + 1)^2) + C)
      ((2 * x^3 + 6 * x^2 + 5 * x + 4) / ((x - 2) * (x + 1)^3)) x := by
  -- The Lebesgue integral is not defined for intervals containing 2 and -1.
  -- Therefore we seek a function whose derivative is the desired function.
  refine .add_const ?_ _
  simp only [log_abs, one_div]

  -- Decompose the proper rational fraction into partial fractions using
  -- the method of undetermined coefficients.
  --   (2 x^3 + 6 x^2 + 5 x + 4) / (x - 2) (x + 1)^3
  --   = A / (x - 2) + B₁ / (x + 1) + B₂ / (x + 1)^2 + B₃ / (x + 1)^3
  -- This gives:
  --   2 x^3 + 6 x^2 + 5 x + 4
  --   = A (x + 1)^3 + B₁ (x - 2) (x + 1)^2 + B₂ (x - 2) (x + 1) + B₃ (x - 2)
  --   = A (x^3 + 3 x^2 + 3 x + 1) + B₁ (x^3 - 3 x - 2) + B₂ (x^2 - x - 2) + B₃ (x - 2)
  --   = (A + B₁) x^3 + (3 A + B₂) x^2 + (3 A - 3 B₁ - B₂ + B₃) x + (A - 2 B₁ - 2 B₂ - 2 B₃)
  -- And therefore:
  --   A + B₁ = 2
  --   3 A + B₂ = 6
  --   3 A - 3 B₁ - B₂ + B₃ = 5
  --   A - 2 B₁ - 2 B₂ - 2 B₃ = 4
  -- Putting this together we obtain A = 2, B₁ = 0, B₂ = 0, B₃ = -1.
  suffices HasDerivAt (fun x ↦ 2 * log (x - 2) + (2 * (x + 1) ^ 2)⁻¹)
      (2 / (x - 2) - 1 / (x + 1) ^ 3) x by
    convert this using 1
    symm
    calc _
    _ = _ := div_sub_div _ _ (sub_ne_zero_of_ne hx) (by simpa using sub_ne_zero_of_ne hx')
    _ = _ := by
      congr 1
      ring

  -- Take out common factors and rewrite using zpow.
  suffices HasDerivAt (fun x ↦ 2 * log (x - 2) + 2⁻¹ * (x + 1) ^ (-2 : ℤ))
      (2 * (1 / (x - 2)) + 2⁻¹ * (-2 * (x + 1) ^ (-3 : ℤ))) x by
    convert this using 1
    · funext x
      rw [zpow_neg, zpow_ofNat, mul_inv]
    · rw [zpow_neg, zpow_ofNat]
      ring
  refine .add (.const_mul 2 ?_) (.const_mul 2⁻¹ ?_)
  · refine .log ?_ (sub_ne_zero_of_ne hx)
    exact .sub_const (hasDerivAt_id' x) 2
  · convert HasDerivAt.comp x (hasDerivAt_zpow (-2) _ ?_) (.add_const (hasDerivAt_id' x) 1) using 1
    · simp
    · simpa using sub_ne_zero_of_ne hx'
