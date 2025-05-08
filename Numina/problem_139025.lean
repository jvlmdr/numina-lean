-- https://cloud.kili-technology.com/label/projects/label/cma3ygf29006bahaymp62cx4r

import Mathlib

open Real Polynomial

/- The real polynomial p(x) ≡ x 3 + ax 2 + bx + c has three real roots α < β < γ.
Show that √(a 2 - 3b) < (γ - α) ≤ 2 √(a 2 /3 - b). -/

theorem algebra_139025 {a b c α β γ : ℝ}
    (hαβ : α < β) (hβγ : β < γ)
    (h : X ^ 3 + C a * X ^ 2 + C b * X + C c = (X - C α) * (X - C β) * (X - C γ)) :
    √(a ^ 2 - 3 * b) < (γ - α) ∧ (γ - α) ≤ 2 * √(a ^ 2 / 3 - b) := by
  -- Expand the root-product form to obtain the canonical form.
  have h : X ^ 3 + C a * X ^ 2 + C b * X + C c =
      X ^ 3 - C (α + β + γ) * X ^ 2 + C (α * β + β * γ + γ * α) * X - C (α * β * γ) := by
    rw [h]
    simp only [map_add, map_mul]
    ring
  -- Use extensionality of polynomials to relate the coefficients to the roots.
  have ha : a = -(α + β + γ) := by simpa [coeff_mul_X_pow'] using ext_iff.mp h 2
  have hb : b = α * β + β * γ + γ * α := by simpa [coeff_mul_X_pow'] using ext_iff.mp h 1
  -- The key result, which will be used to prove both bounds.
  -- Uses `(α + β + γ)^2 = α^2 + β^2 + γ^2 + 2 * (α * β + β * γ + γ * α)`.
  have : a ^ 2 - 3 * b = α^2 + β^2 + γ^2 - (α * β + β * γ + γ * α) := by
    rw [ha, hb]
    ring

  refine ⟨?_, ?_⟩
  · refine (sqrt_lt' ?_).mpr ?_
    · simpa using hαβ.trans hβγ
    -- Use the result above to express in terms of `(γ - α) ^ 2`.
    rw [this]
    calc _
    _ = (γ - α) ^ 2 - (γ - β) * (β - α) := by ring
    _ < _ := by
      refine (sub_lt_self_iff _).mpr ?_
      refine mul_pos ?_ ?_
      · simpa using hβγ
      · simpa using hαβ
  · -- Move the factor of 2 inside the square root to obtain `_ ≤ √_`.
    suffices γ - α ≤ √(2 ^ 2 * (a ^ 2 / 3 - b)) by simpa using this
    refine (le_sqrt' ?_).mpr ?_
    · simpa using hαβ.trans hβγ
    -- Multiply through by 3 to eliminate the fraction.
    refine (mul_le_mul_iff_of_pos_right three_pos).mp ?_
    suffices 3 * (γ - α) ^ 2 ≤ 4 * (a ^ 2 - 3 * b) by
      convert this using 1 <;> ring
    -- Gather the terms into two squares, which are non-negative.
    refine sub_nonneg.mp ?_
    rw [this]
    calc _
    _ ≤ ((γ - β) - (β - α)) ^ 2 := sq_nonneg _
    _ = _ := by ring
