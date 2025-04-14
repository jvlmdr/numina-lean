-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi3000i4nayv3bfj6s6

import Mathlib

open Real

/- For any real numbers $a, b, c$, prove that there exists a real number $x$ such that
$a \cos x + b \cos 3x + c \cos 9x \ge \frac{1}{2}(|a| + |b| + |c|)$. -/

theorem inequalities_129966 (a b c : ℝ) :
    ∃ x, a * cos x + b * cos (3 * x) + c * cos (9 * x) ≥ (|a| + |b| + |c|) / 2 := by
  -- Rewrite the condition as separate inequalities.
  -- TODO: Write as something times k?
  suffices ∃ k, |a| / 2 ≤ a * cos (k * π) ∧ |b| / 2 ≤ b * cos (3 * k * π) ∧
      |c| / 2 ≤ c * cos (9 * k * π) by
    refine this.imp' (· * π) fun k ⟨hxa, hxb, hxc⟩ ↦ ?_
    simpa [add_div, mul_assoc] using add_le_add (add_le_add hxa hxb) hxc

  -- The critical property that we'll use is that `cos x` is greater than or equal to `1/2`
  -- for `x` in the interval `[-π/3, π/3]`
  have h_half_le_cos (x : ℝ) (hx : |x| ≤ π / 3) : 2⁻¹ ≤ cos x := by
    suffices cos (π / 3) ≤ cos |x| by simpa using this
    refine (strictAntiOn_cos.le_iff_le ?_ ?_).mpr hx
    · simp [pi_nonneg, div_nonneg, div_le_self]
    · suffices |x| ≤ π by simpa
      refine le_trans hx ?_
      simp [pi_nonneg, div_le_self]

  -- Generalize to `cos ((k + r) * π)`, where `k` is even and `r` is in `[-1/3, 1/3]`.
  have h_half_le_cos_even_add {k : ℤ} {r : ℝ} (hk : Even k) (hr : |r| ≤ 3⁻¹) :
      2⁻¹ ≤ cos ((k + r) * π) := by
    obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := by simpa using hk.exists_two_nsmul
    calc 2⁻¹
    _ ≤ cos (r * π) := by
      refine h_half_le_cos _ ?_
      have := mul_le_mul_of_nonneg_right hr pi_nonneg
      convert this using 1
      · simp [abs_mul, pi_nonneg]
      · simp [div_eq_inv_mul]
    _ = _ := (cos_add_int_mul_two_pi _ m).symm
    _ = _ := by
      congr 1
      simp only [Int.cast_mul]
      ring
  -- Generalize to `k` odd, where `cos ((k + r) * π)` is less than or equal to `-1/2`.
  have h_cos_odd_add_neg_half {k : ℤ} {r : ℝ} (hk : Odd k) (hr : |r| ≤ 3⁻¹) :
      cos ((k + r) * π) ≤ -2⁻¹ := by
    -- Shift by `π` to negate the cosine.
    suffices 2⁻¹ ≤ cos ((k + r) * π + π) by simpa [le_neg] using this
    -- Apply the result for even `k` to `k + 1`.
    convert h_half_le_cos_even_add hk.add_one hr using 2
    simp only [Int.cast_add]
    ring

  -- Use these results to obtain the desired result in the positive and negative cases.
  have h_nonneg {a : ℝ} (ha : 0 ≤ a) {x : ℝ}
      (k : ℤ) (r : ℝ) (hx : x = (k + r) * π) (hk : Even k) (hr : |r| ≤ 3⁻¹) :
      |a| / 2 ≤ a * cos x := by
    rw [abs_of_nonneg ha]
    rcases hx with rfl
    simpa using mul_le_mul_of_nonneg_left (h_half_le_cos_even_add hk hr) ha
  have h_nonpos {a : ℝ} (ha : a ≤ 0) {x : ℝ}
      (k : ℤ) (r : ℝ) (hx : x = (k + r) * π) (hk : Odd k) (hr : |r| ≤ 3⁻¹) :
      |a| / 2 ≤ a * cos x := by
    rw [abs_of_nonpos ha]
    rcases hx with rfl
    convert mul_le_mul_of_nonpos_left (h_cos_odd_add_neg_half hk hr) ha using 1
    simp [neg_div, div_eq_mul_inv]

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
          convert h_nonneg ha 0 (2 / 27) ?_ even_zero (abs_le.mpr ?_) <;> norm_num
        · -- 3 * (2/27) = 2/9
          convert h_nonneg hb 0 (2 / 9) ?_ even_zero (abs_le.mpr ?_) <;> norm_num
        · -- 9 * (2/27) = 2/3 = 1 + -(1/3)
          convert h_nonpos hc.le 1 (-3⁻¹) ?_ odd_one (abs_le.mpr ?_) <;> norm_num

    | inr hb =>
      cases le_or_lt 0 c with
      | inl hc =>
        -- 0 ≤ a ∧ b ≤ 0 ∧ 0 ≤ c
        refine ⟨2 / 9, ?_, ?_, ?_⟩
        · -- 2/9
          convert h_nonneg ha 0 (2 / 9) ?_ even_zero (abs_le.mpr ?_) <;> norm_num
        · -- 3 * 2/9 = 2/3 = 1 - 1/3
          convert h_nonpos hb.le 1 (-3⁻¹) ?_ odd_one (abs_le.mpr ?_) <;> norm_num
        · -- 9 * 2/9 = 2
          convert h_nonneg hc 2 0 ?_ even_two (abs_le.mpr ?_) <;> norm_num

      | inr hc =>
        -- 0 ≤ a ∧ b ≤ 0 ∧ c ≤ 0
        refine ⟨3⁻¹, ?_, ?_, ?_⟩
        · -- 3⁻¹
          convert h_nonneg ha 0 3⁻¹ ?_ even_zero (abs_le.mpr ?_) <;> norm_num
        · -- 3 * 3⁻¹ = 1
          convert h_nonpos hb.le 1 0 ?_ odd_one (abs_le.mpr ?_) <;> norm_num
        · -- 9 * 3⁻¹ = 3
          convert h_nonpos hc.le 3 0 ?_ (Int.odd_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num

  | inr ha =>
    cases le_or_lt 0 b with
    | inl hb =>
      cases le_or_lt 0 c with
      | inl hc =>
        -- a ≤ 0 ∧ 0 ≤ b ∧ 0 ≤ c
        refine ⟨2 / 3, ?_, ?_, ?_⟩
        · -- 2/3 = 1 + -1/3
          convert h_nonpos ha.le 1 (-3⁻¹) ?_ odd_one (abs_le.mpr ?_) <;> norm_num
        · -- 3 * 2/3 = 2
          convert h_nonneg hb 2 0 ?_ even_two (abs_le.mpr ?_) <;> norm_num
        · -- 9 * 2/3 = 6
          convert h_nonneg hc 6 0 ?_ (Int.even_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num

      | inr hc =>
        -- a ≤ 0 ∧ 0 ≤ b ∧ c ≤ 0
        refine ⟨7 / 9, ?_, ?_, ?_⟩
        · -- 7 / 9 = 1 + -2/9
          convert h_nonpos ha.le 1 (-2 / 9) ?_ odd_one (abs_le.mpr ?_) <;> norm_num
        · -- 3 * 7/9 = 7/3 = 2 + 1/3
          convert h_nonneg hb 2 3⁻¹ ?_ even_two (abs_le.mpr ?_) <;> norm_num
        · -- 9 * 7/9 = 7
          convert h_nonpos hc.le 7 0 ?_ (Int.odd_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num

    | inr hb =>
      cases le_or_lt 0 c with
      | inl hc =>
        -- a ≤ 0 ∧ b ≤ 0 ∧ 0 ≤ c
        refine ⟨8 / 9, ?_, ?_, ?_⟩
        · -- 8 / 9 = 1 + -1/9
          convert h_nonpos ha.le 1 (-1 / 9) ?_ odd_one (abs_le.mpr ?_) <;> norm_num
        · -- 3 * 8/9 = 8/3 = 3 + -1/3
          convert h_nonpos hb.le 3 (-3⁻¹) ?_ (Int.odd_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num
        · -- 9 * 8/9 = 8
          convert h_nonneg hc 8 0 ?_ (even_two_mul (4 : ℤ)) (abs_le.mpr ?_) <;> norm_num
      | inr hc =>
        -- a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0
        refine ⟨1, ?_, ?_, ?_⟩
        · convert h_nonpos ha.le 1 0 ?_ odd_one (abs_le.mpr ?_) <;> norm_num
        · convert h_nonpos hb.le 3 0 ?_ (Int.odd_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num
        · convert h_nonpos hc.le 9 0 ?_ (Int.odd_iff.mpr ?_) (abs_le.mpr ?_) <;> norm_num
