-- https://cloud.kili-technology.com/label/projects/label/cma3ygf29005nahayjbc4y5by

import Mathlib

open Real

/- Let $a, b, c$ be positive real numbers such that $a b c = 1$. Show that
$$
\frac{1}{a^{3} + b c} + \frac{1}{b^{3} + c a} + \frac{1}{c^{3} + a b} \leq
  \frac{(a b + b c + c a)^{2}}{6}
$$
-/

theorem inequalities_100122 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a ^ 3 + b * c) + 1 / (b ^ 3 + c * a) + 1 / (c ^ 3 + a * b) ≤
      ((a * b + b * c + c * a) ^ 2) / 6 :=
  calc _
  -- Apply the AM-GM inequality to `[a^3, b c]` to obtain
  -- `a^3 + b c ≥ 2 √(a^3 b c) = 2 √(u^2 (u v w) = 2 u`.
  _ ≤ 1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c) := by
    -- Generalize to apply multiple times.
    suffices ∀ {u v w : ℝ}, 0 < u → 0 < v → 0 < w → u * v * w = 1 → 2 * u ≤ u ^ 3 + v * w by
      gcongr
      · exact this ha hb hc habc
      · refine this hb hc ha ?_
        convert habc using 1
        ring
      · refine this hc ha hb ?_
        convert habc using 1
        ring
    intro a b c ha hb hc habc
    -- Divide by 2 to match the form from the AM-GM inequality.
    refine (le_div_iff₀' two_pos).mp ?_
    convert geom_mean_le_arith_mean2_weighted one_half_pos.le one_half_pos.le
      (pow_nonneg ha.le 3) (mul_nonneg hb.le hc.le) (add_halves 1) using 1
    · calc _
      _ = √((a ^ 2) * (a * b * c)) := by simp [habc, ha.le]
      _ = √((a ^ 3) * (b * c)) := congrArg sqrt (by ring)
      _ = √(a ^ 3) * √(b * c) := sqrt_mul (pow_nonneg ha.le 3)  _
      _ = _ := by simp [sqrt_eq_rpow]
    · ring

  -- Add the fractions using a common demoninator.
  _ = (1 / a + 1 / b + 1 / c) / 2 := by ring
  _ = (a * b + b * c + c * a) / (a * b * c) / 2 := by
    congr
    rw [div_add_div _ _ ha.ne' hb.ne', div_add_div _ _ (mul_pos ha hb).ne' hc.ne']
    ring

  -- Apply the AM-GM inequality to `[a b, b c, c a]` to obtain
  -- `((a b c)^2) ^ (1/3) = 1 ≤ (a b + b c + c a) / 3` and hence `3 ≤ (a b + b c + c a)`.
  _ = 3 * (a * b + b * c + c * a) / 6 := by
    rw [habc]
    ring
  _ ≤ (a * b + b * c + c * a) ^ 2 / 6 := by
    suffices 3 ≤ a * b + b * c + c * a by
      rw [sq]
      gcongr
    -- Divide by 3 to match the form from the AM-GM inequality.
    refine (one_le_div₀ three_pos).mp ?_
    convert geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num)
      (mul_nonneg ha.le hb.le) (mul_nonneg hb.le hc.le) (mul_nonneg hc.le ha.le)
      (add_thirds 1) using 1
    · symm
      calc
      _ = ((a * b * c) ^ 2) ^ (1/3 : ℝ) := by
        have hab := mul_pos ha hb
        have hbc := mul_pos hb hc
        have hca := mul_pos hc ha
        rw [← mul_rpow hab.le hbc.le, ← mul_rpow (mul_pos hab hbc).le hca.le]
        congr 1
        ring
      _ = _ := by simp [habc]
    · ring
