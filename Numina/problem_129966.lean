-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi3000i4nayv3bfj6s6

import Mathlib

open Real
open scoped BigOperators

/- For any real numbers $a, b, c$, prove that there exists a real number $x$ such that
$a \cos x + b \cos 3x + c \cos 9x \ge \frac{1}{2}(|a| + |b| + |c|)$. -/

theorem inequalities_129966 (a b c : ℝ) :
    ∃ x, a * cos x + b * cos (3 * x) + c * cos (9 * x) ≥ (|a| + |b| + |c|) / 2 := by
  -- Rewrite the condition as separate inequalities.
  -- Use a rational multiplied by `π` rather than a real.
  -- This will let us use `norm_num` to handle periodicity.
  suffices ∃ (k : ℚ), |a| / 2 ≤ a * cos (k * π) ∧
      |b| / 2 ≤ b * cos (↑(3 * k) * π) ∧ |c| / 2 ≤ c * cos (↑(9 * k) * π) by
    refine this.imp' (fun k : ℚ ↦ k * π) fun k ⟨hxa, hxb, hxc⟩ ↦ ?_
    simp only [add_div]
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact hxa
    · simpa [mul_assoc] using hxb
    · simpa [mul_assoc] using hxc

  -- The critical property that we'll use is that $\cos x$ is greater than or equal to $1/2$
  -- for $x$ in the interval $[-\pi/3, \pi/3]$.
  have h_half_le_cos (x : ℝ) (hx : |x| ≤ π / 3) : 2⁻¹ ≤ cos x := by
    suffices cos (π / 3) ≤ cos |x| by simpa using this
    refine (strictAntiOn_cos.le_iff_le ?_ ?_).mpr hx
    · simp [pi_nonneg, div_nonneg, div_le_self]
    · suffices |x| ≤ π by simpa
      refine le_trans hx ?_
      simp [pi_nonneg, div_le_self]

  -- Once splitting on the signs of `a, b, c`, we will have one of two conditions.
  have h_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℚ) (h_int : Even (round k))
      (h_fract : |k - round k| ≤ 3⁻¹) :
      |a| / 2 ≤ a * cos (k * π) := by
    rw [abs_of_nonneg ha]
    suffices 2⁻¹ ≤ cos (k * π) from mul_le_mul_of_nonneg_left this ha
    obtain ⟨m, hm⟩ : ∃ m, round k = 2 * m := by simpa using h_int.exists_two_nsmul
    convert h_half_le_cos ((k - 2 * m) * π) ?_ using 1
    · calc
      _ = _ := (cos_periodic.sub_int_mul_eq m).symm
      _ = _ := by
        congr
        ring
    · convert mul_le_mul_of_nonneg_right (Rat.cast_le.mpr h_fract) pi_nonneg using 1
      · simp [hm, abs_mul, pi_nonneg]
      · ring

  have h_nonpos {a : ℝ} (ha : a ≤ 0) (k : ℚ) (h_int : Odd (round k))
      (h_fract : |k - round k| ≤ 3⁻¹) :
      |a| / 2 ≤ a * cos (k * π) := by
    rw [abs_of_nonpos ha]
    suffices cos (k * π) ≤ -2⁻¹ by
      convert mul_le_mul_of_nonpos_left this ha using 1
      ring
    -- Shift by `π` to flip sign.
    suffices 2⁻¹ ≤ cos (k * π - π) by simpa [le_neg] using this
    obtain ⟨m, hm⟩ : ∃ m, round k = 2 * m + 1 := h_int.exists_bit1
    convert h_half_le_cos ((k - (2 * m + 1)) * π) ?_ using 1
    · calc _
      _ = _ := (cos_periodic.sub_int_mul_eq m).symm
      _ = _ := by
        congr
        ring
    · convert mul_le_mul_of_nonneg_right (Rat.cast_le.mpr h_fract) pi_nonneg using 1
      · simp [hm, abs_mul, pi_nonneg]
      · ring

  have h_nonneg' {a : ℝ} (ha : 0 ≤ a) (m : ℤ) (r : ℚ) (hm : Even m) (hr : |r| ≤ 3⁻¹) :
      |a| / 2 ≤ a * cos ((m + r) * π) := by
    have hr' : -2⁻¹ ≤ r ∧ r < 2⁻¹ := by
      rw [abs_le] at hr
      constructor <;> linarith
    convert h_nonneg ha (m + r) ?_ ?_
    · simp
    · rw [round_int_add]
      convert hm
      simpa using hr'
    · convert hr
      simpa using hr'
  have h_nonpos' {a : ℝ} (ha : a ≤ 0) (m : ℤ) (r : ℚ) (hm : Odd m) (hr : |r| ≤ 3⁻¹) :
      |a| / 2 ≤ a * cos ((m + r) * π) := by
    have hr' : -2⁻¹ ≤ r ∧ r < 2⁻¹ := by
      rw [abs_le] at hr
      constructor <;> linarith
    convert h_nonpos ha (m + r) ?_ ?_
    · simp
    · rw [round_int_add]
      convert hm
      simpa using hr'
    · convert hr
      simpa using hr'

  cases le_or_lt 0 a with
  | inl ha =>
    cases le_or_lt 0 b with
    | inl hb =>
      cases le_or_lt 0 c with
      | inl hc =>
        use 0
        simp [abs_of_nonneg, ha, hb, hc]
      | inr hc =>
        -- 0 ≤ a ∧ b ≤ 0 ∧ c ≤ 0
        refine ⟨2 / 27, ?_, ?_, ?_⟩
        · -- 2/27 = 0 + 2/27, 2/27 < 1/3 = 9/27
          convert h_nonneg' ha 0 (2 / 27) even_zero (abs_le.mpr ?_) <;> norm_num
        · -- 3 * (2/27) = 2/9
          convert h_nonneg' hb 0 (2 / 9) even_zero (abs_le.mpr ?_) <;> norm_num
        · -- 9 * (2/27) = 2/3 = 1 + -(1/3)
          convert h_nonpos' hc.le 1 (-3⁻¹) odd_one (abs_le.mpr ?_) <;> norm_num

    | inr hb =>
      cases le_or_lt 0 c with
      | inl hc =>
        -- 0 ≤ a ∧ b ≤ 0 ∧ 0 ≤ c
        refine ⟨2 / 9, ?_, ?_, ?_⟩
        · -- 2/9
          convert h_nonneg' ha 0 (2 / 9) even_zero (abs_le.mpr ?_) <;> norm_num
        · -- 3 * 2/9 = 2/3 = 1 - 1/3
          convert h_nonpos' hb.le 1 (-3⁻¹) odd_one (abs_le.mpr ?_) <;> norm_num
        · -- 9 * 2/9 = 2
          convert h_nonneg' hc 2 0 even_two (abs_le.mpr ?_) <;> norm_num

      | inr hc =>
        -- 0 ≤ a ∧ b ≤ 0 ∧ c ≤ 0
        refine ⟨3⁻¹, ?_, ?_, ?_⟩
        · -- 3⁻¹
          convert h_nonneg' ha 0 3⁻¹ even_zero (abs_le.mpr ?_) <;> norm_num
        · -- 3 * 3⁻¹ = 1
          convert h_nonpos' hb.le 1 0 odd_one (abs_le.mpr ?_) <;> norm_num
        · -- 9 * 3⁻¹ = 3
          convert h_nonpos' hc.le 3 0 (Int.odd_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num

  | inr ha =>
    cases le_or_lt 0 b with
    | inl hb =>
      cases le_or_lt 0 c with
      | inl hc =>
        -- a ≤ 0 ∧ 0 ≤ b ∧ 0 ≤ c
        refine ⟨2 / 3, ?_, ?_, ?_⟩
        · -- 2/3 = 1 + -1/3
          convert h_nonpos' ha.le 1 (-3⁻¹) odd_one (abs_le.mpr ?_) <;> norm_num
        · -- 3 * 2/3 = 2
          convert h_nonneg' hb 2 0 even_two (abs_le.mpr ?_) <;> norm_num
        · -- 9 * 2/3 = 6
          convert h_nonneg' hc 6 0 (Int.even_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num

      | inr hc =>
        -- a ≤ 0 ∧ 0 ≤ b ∧ c ≤ 0
        refine ⟨7 / 9, ?_, ?_, ?_⟩
        · -- 7 / 9 = 1 + -2/9
          convert h_nonpos' ha.le 1 (-2 / 9) odd_one (abs_le.mpr ?_) <;> norm_num
        · -- 3 * 7/9 = 7/3 = 2 + 1/3
          convert h_nonneg' hb 2 3⁻¹ even_two (abs_le.mpr ?_) <;> norm_num
        · -- 9 * 7/9 = 7
          convert h_nonpos' hc.le 7 0 (Int.odd_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num

    | inr hb =>
      cases le_or_lt 0 c with
      | inl hc =>
        -- a ≤ 0 ∧ b ≤ 0 ∧ 0 ≤ c
        refine ⟨8 / 9, ?_, ?_, ?_⟩
        · -- 8 / 9 = 1 + -1/9
          convert h_nonpos' ha.le 1 (-1 / 9) odd_one (abs_le.mpr ?_) <;> norm_num
        · -- 3 * 8/9 = 8/3 = 3 + -1/3
          convert h_nonpos' hb.le 3 (-3⁻¹) (Int.odd_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num
        · -- 9 * 8/9 = 8
          convert h_nonneg' hc 8 0 (even_two_mul (4 : ℤ)) (abs_le.mpr ?_) <;> norm_num
      | inr hc =>
        -- a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0
        refine ⟨1, ?_, ?_, ?_⟩
        · convert h_nonpos' ha.le 1 0 odd_one (abs_le.mpr ?_) <;> norm_num
        · convert h_nonpos' hb.le 3 0 (Int.odd_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num
        · convert h_nonpos' hc.le 9 0 (Int.odd_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num
