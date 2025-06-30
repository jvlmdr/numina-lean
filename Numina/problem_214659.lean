-- https://cloud.kili-technology.com/label/projects/label/cmcbovi8d00u0ueaxdwyw2g5v

import Mathlib

open Complex

/- For which real parameters $a$ does there exist a complex number $z$ such that
$$
|z + \sqrt{2}| = \sqrt{a^{2} - 3 a + 2} \quad \text { and } \quad |z + i \sqrt{2}| < a ?
$$
-/

theorem algebra_214659 (a : ℝ) :
    (0 ≤ a^2 - 3 * a + 2 ∧ ∃ z : ℂ, abs (z + √2) = √(a^2 - 3 * a + 2) ∧ abs (z + I * √2) < a) ↔
      2 < a := by
  -- We include `0 ≤ a^2 - 3 * a + 2` as an assumption since `√x` is zero for `x < 0`.
  -- Otherwise, for `z = -√2`, the constraint would be satisfied for any `a^2 - 3 * a + 2 ≤ 0`.
  have h_factor : a^2 - 3 * a + 2 = (a - 1) * (a - 2) := by ring
  simp only [h_factor]

  constructor
  · intro ⟨ha, z, hz_eq, hz_lt⟩
    have ha' := ha  -- TODO
    rw [mul_nonneg_iff] at ha
    cases ha with
    | inl ha =>
      have ha : 2 ≤ a := by linarith
      -- When `a = 2`, we have `z = -√2`, which contradicts the strict inequality.
      suffices a ≠ 2 from lt_of_le_of_ne ha this.symm
      rintro rfl
      have hz : z = -√2 := by
        refine norm_sub_eq_zero_iff.mp ?_
        convert hz_eq using 1
        · simp
        · norm_num
      rcases hz with rfl
      refine hz_lt.ne ?_
      convert Complex.abs_add_mul_I (-√2) √2 using 2
      · simp only [ofReal_neg]
        ring
      · suffices 2 = √(2 * 2) by simpa [two_mul]
        simp

    | inr ha =>
      have ha : a ≤ 1 := by linarith
      -- Now we know that `|z - (-i √2)| < a ≤ 1` and `|z - (-√2)| = √((a - 1) * (a - 2))`.
      -- Note that the distance `|(-√2) - (-i √2)| = 2`.
      -- It will suffice to show that these circles do not intersect.
      -- That is, that the triangle inequality is contradicted.
      exfalso
      suffices abs (z + √2) + abs (z + I * √2) < abs (-√2 + I * √2) by
        refine (norm_sub_le_norm_sub_add_norm_sub (-√2 : ℂ) z (-I * √2)).not_lt ?_
        simpa [norm_sub_rev _ z]
      suffices √((1 - a) * (2 - a)) + abs (z + I * √2) < 2 by
        convert this
        · rw [hz_eq]
          congr 1
          ring
        · convert Complex.abs_add_mul_I (-√2) √2 using 2
          · simp only [ofReal_neg]
            ring
          · suffices 2 = √(2 * 2) by simpa [two_mul]
            simp
      -- Use the fact that `|z + I * √2| < a`.
      suffices √((1 - a) * (2 - a)) + a < 2 from lt_trans (by simpa) this
      -- Obtain a factor of `2 - a` on both sides.
      rw [← lt_sub_iff_add_lt]
      -- Now use `1 - a < 2 - a`.
      calc _
      _ < √((2 - a) * (2 - a)) := by
        refine Real.sqrt_lt_sqrt ?_ ?_
        · refine mul_nonneg ?_ ?_ <;> linarith
        rw [mul_lt_mul_right (by linarith)]
        linarith
      _ = _ := Real.sqrt_mul_self (by linarith)

  · intro ha
    -- Move along the line joining `-√2` and `-i √2`; that is, in the direction `1 - i`.
    let x : ℂ := √((a - 1) * (a - 2)) * ((1 - I) / abs (1 - I))
    have h_norm : abs (1 - I) = √2 := by
      convert Complex.abs_add_mul_I 1 (-1) using 2
      · simp only [ofReal_one, ofReal_neg]
        ring
      · norm_num

    refine ⟨?_, x - √2, ?_, ?_⟩
    · refine mul_nonneg ?_ ?_ <;> linarith
    · suffices abs (1 - I) ≠ 0 by simp [x, _root_.abs_of_nonneg, div_self this]
      simp [Complex.ext_iff]
    · calc _
      _ = abs (x - 2 * (1 - I) / abs (1 - I)) := by
        congr 1
        rw [h_norm]
        suffices x - √2 * (1 - I) = x - ↑(2 / √2) * (1 - I) by
          simp only [ofReal_div, ofReal_ofNat] at this
          convert this using 1 <;> ring
        rw [Real.div_sqrt]
      _ = abs ((√((a - 1) * (a - 2)) - 2) * ((1 - I) / abs (1 - I))) := by
        congr 1
        ring
      _ = abs (↑(√((a - 1) * (a - 2)) - 2) : ℂ) := by
        -- TODO: better to use `√2` in denominator?
        suffices Complex.abs (1 - I) ≠ 0 by simp [AbsoluteValue.map_mul, div_self this]
        simp [Complex.ext_iff]
      _ = |√((a - 1) * (a - 2)) - 2| := abs_ofReal _
      _ < a := by
        refine abs_sub_lt_of_nonneg_of_lt (by simp) ?_ two_pos.le ha
        rw [Real.sqrt_lt' (by linarith)]
        linarith
