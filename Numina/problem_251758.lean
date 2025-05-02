-- https://cloud.kili-technology.com/label/projects/label/cma29f86f002vhsayredue56q

import Mathlib

open Real

/-
$$
\frac{\tan 96° - \tan 12° (1 + \frac{1}{\sin 6°})}
  {1 + \tan 96° \tan 12° (1 + \frac{1}{\sin 6°})} = \text{?}
$$
-/

theorem algebra_251758 :
    (tan (96 / 180 * π) - tan (12 / 180 * π) * (1 + 1 / sin (6 / 180 * π))) /
    (1 + tan (96 / 180 * π) * tan (12 / 180 * π) * (1 + 1 / sin (6 / 180 * π))) = √3 / 3 := by

  have h_cos96 : cos (96 / 180 * π) ≠ 0 := by
    refine ne_of_lt ?_
    refine cos_neg_of_pi_div_two_lt_of_lt ?_ ?_
    · calc _
      _ = (90 / 180) * π := by ring
      _ < _ := by gcongr; norm_num
    · calc _
      _ < π := mul_lt_of_lt_one_left pi_pos (by norm_num)
      _ < _ := by simp [pi_pos]

  have h_cos12 : cos (12 / 180 * π) ≠ 0 := by
    refine ne_of_gt ?_
    refine cos_pos_of_mem_Ioo ⟨?_, ?_⟩
    · calc _
      _ < (0 : ℝ) := by simp [pi_pos]
      _ < _ := by simp [pi_pos]
    · calc _
      _ < (1 / 2) * π := mul_lt_mul_of_pos_right (by norm_num) pi_pos
      _ = _ := by ring

  have h_sin6 : sin (6 / 180 * π) ≠ 0 := by
    refine ne_of_gt ?_
    refine sin_pos_of_pos_of_lt_pi ?_ ?_
    · simp [pi_pos]
    · refine mul_lt_of_lt_one_left pi_pos ?_
      norm_num

  have h_sin54_sin18 : sin (54 / 180 * π) - sin (18 / 180 * π) = 1 / 2 := by
    calc
    _ = _ := sin_sub_sin _ _
    _ = 2 * sin (π / 10) * cos (π / 5) := by
      simp only [mul_assoc]
      congr 3 <;> ring
    _ = 2 * ((√5 - 1) / 4) * ((1 + √5) / 4) := by
      congr
      · sorry
      · exact cos_pi_div_five
    _ = (√5 ^ 2 - 1) / 8 := by ring
    _ = (5 - 1) / 8 := by simp
    _ = _ := by ring

  calc _
  -- _ = (tan (8 / 15 * π) - tan (1 / 15 * π) * (1 + 1 / sin (1 / 30 * π))) /
  --     (1 + tan (8 / 15 * π) * tan (1 / 15 * π) * (1 + 1 / sin (1 / 30 * π))) := by
  --   congr <;> ring

  -- Multiply top and bottom by `(cos 96) (cos 12) (sin 6)`.
  _ = _ := Eq.symm <| mul_div_mul_left _ _
    (c := cos (96 / 180 * π) * cos (12 / 180 * π) * sin (6 / 180 * π)) <| by
      suffices cos (96 / 180 * π) ≠ 0 ∧ cos (12 / 180 * π) ≠ 0 ∧ sin (6 / 180 * π) ≠ 0 by
        simpa [and_assoc] using this
      refine ⟨?_, ?_, ?_⟩
      · exact h_cos96
      · exact h_cos12
      · exact h_sin6

  _ = (sin (96 / 180 * π) * cos (12 / 180 * π) * sin (6 / 180 * π) -
        cos (96 / 180 * π) * sin (12 / 180 * π) * (sin (6 / 180 * π) + 1)) /
      (cos (96 / 180 * π) * cos (12 / 180 * π) * sin (6 / 180 * π) +
        sin (96 / 180 * π) * sin (12 / 180 * π) * (sin (6 / 180 * π) + 1)) := by
    simp only [mul_sub, mul_add (_ * sin (6 / 180 * π))]
    congr 2
    · rw [← tan_mul_cos h_cos96]
      ring
    · rw [mul_mul_mul_comm]
      congr 1
      · rw [← tan_mul_cos h_cos12]
        ring
      · simp [mul_add, h_sin6]
    · simp
    · rw [mul_mul_mul_comm]
      congr 1
      · rw [← tan_mul_cos h_cos96, ← tan_mul_cos h_cos12]
        ring
      · simp [mul_add, h_sin6]

  -- Replace all 96 terms with 6 terms.
  _ = (cos (6 / 180 * π) * cos (12 / 180 * π) * sin (6 / 180 * π) -
        -sin (6 / 180 * π) * sin (12 / 180 * π) * (sin (6 / 180 * π) + 1)) /
      (-sin (6 / 180 * π) * cos (12 / 180 * π) * sin (6 / 180 * π) +
        cos (6 / 180 * π) * sin (12 / 180 * π) * (sin (6 / 180 * π) + 1)) := by
    have h_sin96' : sin (96 / 180 * π) = cos (6 / 180 * π) := by
      convert sin_add_pi_div_two (6 / 180 * π) using 2
      ring
    have h_cos96' : cos (96 / 180 * π) = -sin (6 / 180 * π) := by
      convert cos_add_pi_div_two (6 / 180 * π) using 2
      ring
    rw [h_sin96', h_cos96']

  -- Nearly have a term of `sin 6` to cancel from top and bottom.
  -- Replace `sin 12 = 2 sin 6 cos 6`.
  _ = (cos (6 / 180 * π) * cos (12 / 180 * π) * sin (6 / 180 * π) -
        -sin (6 / 180 * π) * sin (12 / 180 * π) * (sin (6 / 180 * π) + 1)) /
      (-sin (6 / 180 * π) * cos (12 / 180 * π) * sin (6 / 180 * π) + cos (6 / 180 * π) *
        (sin (12 / 180 * π) * sin (6 / 180 * π) + 2 * sin (6 / 180 * π) * cos (6 / 180 * π))) := by
    congr 2
    rw [mul_assoc, mul_add, mul_one]
    congr
    -- Employ the identity for `sin (2 θ)`.
    convert sin_two_mul (6 / 180 * π) using 1
    congr 1
    ring
  -- Eliminate the factor of `sin (6 / 180 * π)` from top and bottom.
  _ = (cos (6 / 180 * π) * cos (12 / 180 * π) + sin (12 / 180 * π) * (sin (6 / 180 * π) + 1)) /
      (-cos (12 / 180 * π) * sin (6 / 180 * π) +
        cos (6 / 180 * π) * sin (12 / 180 * π) + 2 * cos (6 / 180 * π) ^ 2) := by
    convert mul_div_mul_left _ _ h_sin6 using 2 <;> ring

  -- Use difference identities (12 - 6 = 6) where possible.
  _ = (sin (12 / 180 * π) + cos (12 / 180 * π - 6 / 180 * π)) /
      (sin (12 / 180 * π - 6 / 180 * π) + 2 * cos (6 / 180 * π) ^ 2) := by
    rw [cos_sub, sin_sub]
    congr 1 <;> ring
  _ = (sin (12 / 180 * π) + cos (6 / 180 * π)) /
      (sin (6 / 180 * π) + 2 * cos (6 / 180 * π) ^ 2) := by
    congr <;> ring

  -- Now phrase in terms of angles that have known sin, cos.
  -- We will make use of sin 54 - sin 18 = 1/2.
  -- Hence use 12 = 30 - 18, 90 - 6 = 30 + 54, 6 = 60 - 54.
  _ = (sin (12 / 180 * π) + sin (π / 2 - 6 / 180 * π)) /
      (sin (6 / 180 * π) + (1 + cos (2 * (6 / 180 * π)))) := by
    congr
    · exact (sin_pi_div_two_sub _).symm
    · rw [cos_sq]
      ring
  _ = (sin (π / 6 - π / 10) + sin (π / 6 + 3 * π / 10)) /
      (sin (π / 3 - 3 * π / 10) + (1 + cos (π / 6 - π / 10))) := by
    congr <;> ring

  -- Apply identities for sum and difference of angles.
  -- Substitute value of sin and cos at π/3, π/6.
  _ = (1/2 * (cos (3 * π / 10) + cos (π / 10)) + √3/2 * (sin (3 * π / 10) - sin (π / 10))) /
      (√3/2 * (cos (3 * π / 10) + cos (π / 10)) - 1/2 * (sin (3 * π / 10) - sin (π / 10)) + 1) := by
    simp only [sin_sub, sin_add, cos_sub]
    simp only [sin_pi_div_six, cos_pi_div_six, sin_pi_div_three, cos_pi_div_three]
    congr 1 <;> ring

  _ = (1/2 * (cos (3 * π / 10) + cos (π / 10)) + √3/4) /
      (√3/2 * (cos (3 * π / 10) + cos (π / 10)) + 3/4) := by
    suffices sin (3 * π / 10) - sin (π / 10) = 1 / 2 by
      rw [this]
      congr 1 <;> ring
    sorry

  _ = (1/2 * (cos (3 * π / 10) + cos (π / 10)) + √3/4) /
      (√3/2 * (cos (3 * π / 10) + cos (π / 10)) + √3^2/4) := by simp

  _ = (1/2 * (cos (3 * π / 10) + cos (π / 10)) + √3/4) /
      (√3 * (1/2 * (cos (3 * π / 10) + cos (π / 10)) + √3/4)) := by
    congr 1
    ring

  _ = (√3)⁻¹ := by
    refine div_mul_cancel_right₀ ?_ _
    refine ne_of_gt ?_
    refine add_pos ?_ (by norm_num)
    refine mul_pos (by norm_num) ?_
    refine add_pos ?_ ?_
    · refine cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · refine lt_trans (b := 0) ?_ ?_ <;> simp [pi_pos]
      · calc _
        _ = 3 / 10 * π := by ring
        _ < 2⁻¹ * π := by
          gcongr
          norm_num
        _ = _ := by ring
    · refine cos_pos_of_mem_Ioo ⟨?_, ?_⟩
      · refine lt_trans (b := 0) ?_ ?_ <;> simp [pi_pos]
      · calc _
        _ = 10⁻¹ * π := by ring
        _ < 2⁻¹ * π := by
          gcongr
          norm_num
        _ = _ := by ring

  _ = _ := sqrt_div_self.symm
