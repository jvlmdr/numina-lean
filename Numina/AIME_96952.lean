-- https://cloud.kili-technology.com/label/projects/label/cm84mpwv601weiev5cqwbrnw6
-- https://artofproblemsolving.com/wiki/index.php/2017_AIME_I_Problems/Problem_10

import Mathlib

open Complex

/- Let $z_1 = 18 + 83i$, $z_2 = 18 + 39i$m and $z_3 = 78 + 99i$, where $i = \sqrt{-1}$.
Let $z$ be the unique complex number with the properties that
$\frac{z_3 - z_1}{z_2 - z_1} \frac{z - z_2}{z - z_3}$ is a real number and
the imaginary part of $z$ is the greatest possible. Find the real part of $z$. -/

theorem algebra_96952 {z₁ z₂ z₃ : ℂ}
    (hz₁ : z₁ = 18 + 83 * I) (hz₂ : z₂ = 18 + 39 * I) (hz₃ : z₃ = 78 + 99 * I) :
    ∃ z, ((z₃ - z₁) / (z₂ - z₁) * ((z - z₂) / (z - z₃))).im = 0 ∧
      z.re = 56 ∧
      ∀ x, ((z₃ - z₁) / (z₂ - z₁) * ((x - z₂) / (x - z₃))).im = 0 → z.im ≥ x.im := by
  -- Simplify the constant fraction on the left.
  have h_const : (z₃ - z₁) / (z₂ - z₁) = ⟨-4, 15⟩ / 11 :=
    calc _
    _ = (4 * I ^ 2 + 15 * I) / 11 := by
      simp only [hz₁, hz₂, hz₃]
      simp only [add_sub_add_left_eq_sub, ← sub_mul, ← div_div, div_I]
      ring
    _ = _ := by simp [mk_eq_add_mul_I]

  have h_cond (a b : ℝ) : ((z₃ - z₁) / (z₂ - z₁) * ((⟨a, b⟩ - z₂) / (⟨a, b⟩ - z₃))).im = 0 ↔
      (a - 56) ^ 2 + (b - 61) ^ 2 = 1928 :=
    calc _
    _ ↔ (⟨-4, 15⟩ / 11 * ((⟨a, b⟩ - z₂) / (⟨a, b⟩ - z₃))).im = 0 := by rw [h_const]
    -- Eliminate the constant divisor 11.
    _ ↔ (⟨-4, 15⟩ * ((⟨a, b⟩ - z₂) / (⟨a, b⟩ - z₃))).im = 0 := by
      rw [← mul_div_right_comm]
      simp
    -- Swap division for multiplication by the conjugate.
    _ ↔ (⟨-4, 15⟩ * ((⟨a, b⟩ - z₂) * starRingEnd ℂ (⟨a, b⟩ - z₃))).im = 0 := by
      simp only [div_eq_mul_inv, inv_def, ← mul_assoc, im_mul_ofReal, mul_eq_zero]
      refine or_iff_left_of_imp fun hz ↦ ?_
      simp only [inv_eq_zero, map_eq_zero, sub_eq_zero] at hz
      simp [← hz]
    -- Substitute the values of z₂, z₃ and expand the product.
    _ ↔ -(4 * ((a - 18) * (-b + 99) + (b - 39) * (a - 78))) +
        15 * ((a - 18) * (a - 78) - (b - 39) * (-b + 99)) = 0 := by
      simp [hz₂, hz₃]
    -- Group terms and complete the two squares.
    _ ↔ 15 * ((a - 56) ^ 2 + (b - 61) ^ 2 - 1928) = 0 := by
      refine Eq.congr_left ?_
      ring
    -- Eliminate the constant factor 15.
    _ ↔ _ := by simp [sub_eq_zero]

  -- Adopt this definition of the condition.
  simp only [h_cond]
  -- Since `(a - 56)^2 + (b - 61)^2 = 1928`, the imaginary part will be maximized at a = 56.
  -- The imaginary part is given by `b = 61 + √(1928 - (a - 56)^2)`.
  use ⟨56, 61 + √1928⟩, by simp, rfl, fun x hx ↦ ?_
  replace hx : (x.im - 61) ^ 2 = 1928 - (x.re - 56) ^ 2 := eq_sub_of_add_eq' hx
  replace hx : x.im - 61 ≤ √(1928 - (x.re - 56) ^ 2) := Real.le_sqrt_of_sq_le hx.le
  refine (le_add_of_sub_left_le hx).trans ?_
  simp [sq_nonneg]
