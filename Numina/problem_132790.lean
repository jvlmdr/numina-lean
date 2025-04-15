-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi3000p4nayo6y6hnqb

import Mathlib

open Real MeasureTheory

/- Calculate the indefinite integral:
$$
\int \frac{2 x^{3} + 6 x^{2} + 5 x + 4}{(x - 2)(x + 1)^{3}} d x
$$
-/

theorem calculus_132790 (a x : ℝ) :
    ∃ C, ∫ x in a..x, (2 * x^3 + 6 * x^2 + 5 * x + 4) / ((x - 2) * (x + 1)^3) =
      2 * log |x - 2| + 1 / (2 * (x + 1)^2) + C := by

  -- Use `-f a` as the constant.
  use -((2 * log |a - 2|) + (1 / (2 * (a + 1)^2)))
  simp only [log_abs, one_div, ← sub_eq_add_neg]

  calc _
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
  _ = ∫ x in a..x, 2 / (x - 2) - 1 / (x + 1) ^ 3 := by
    -- Must consider ae-equality to avoid the singularities at `x = 2` and `x = -1`.
    refine intervalIntegral.integral_congr_ae ?_
    refine ae_iff.mpr ?_
    refine nonpos_iff_eq_zero.mp ?_
    calc _
    -- Discard the `uIcc a x` condition.
    _ ≤ volume {x : ℝ | (2 * x ^ 3 + 6 * x ^ 2 + 5 * x + 4) / ((x - 2) * (x + 1) ^ 3) ≠
        2 / (x - 2) - 1 / (x + 1) ^ 3} := measure_mono fun u ↦ by simp
    -- Show that the inequality holds for all x except `x = 2` and `x = -1`.
    _ ≤ volume ({2, -1} : Set ℝ) := by
      refine measure_mono fun x hx ↦ ?_
      contrapose hx
      replace hx : x ≠ 2 ∧ x ≠ -1 := by simpa using hx
      suffices (2 * x ^ 3 + 6 * x ^ 2 + 5 * x + 4) / ((x - 2) * (x + 1) ^ 3) =
          2 / (x - 2) - 1 / (x + 1) ^ 3 by simpa using this
      symm
      calc _
      _ = _ := div_sub_div _ _ (sub_ne_zero_of_ne hx.1) (by simpa using sub_ne_zero_of_ne hx.2)
      _ = _ := by
        congr 1
        ring
    -- Show that this set has measure zero.
    _ ≤ volume ({2} : Set ℝ) + volume ({-1} : Set ℝ) := measure_union_le {2} {-1}
    _ = 0 := by simp

  _ = _ := by

    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
      (f := fun x ↦ 2 * log (x - 2) + (2 * (x + 1) ^ 2)⁻¹)
    · -- Should be easy.
      sorry
    · -- Oh shit. Not valid for Lebesgue integral?
      -- Need to work with limit?
      sorry
