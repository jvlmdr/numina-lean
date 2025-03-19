-- https://cloud.kili-technology.com/label/projects/label/cm7enil0200sfzz87bml2zpcj

import Mathlib

/- Cities A and B are 45 miles apart.
Alicia lives in A and Beth lives in B.
Alicia bikes towards B at 18 miles per hour.
Leaving at the same time, Beth bikes toward A at 12 miles per hour.
How many miles from City A will they be when they meet?
(A) 20
(B) 24
(C) 25
(D) 26
(E) 27 -/

theorem algebra_65302 {d v1 v2 : ℝ} (hd : d = 45) (hv1 : v1 = 18) (hv2 : v2 = 12) {x t : ℝ}
    (h1 : x = v1 * t) (h2 : x = d - v2 * t) : x = 27 := by
  -- Re-arrange to eliminate: t = x / v1 = (d - x) / v2
  -- Cross multiply: v2 * x = v1 * (d - x) = v1 * d - v1 * x
  -- Re-arrange terms: x = v1 * d / (v1 + v2)
  suffices x = v1 * d / (v1 + v2) by
    rw [hv1, hv2, hd] at this
    norm_num at this
    exact this
  -- Obtain proofs of positivity to use for division.
  have hv1_pos : 0 < v1 := by simp [hv1]
  have hv2_pos : 0 < v2 := by simp [hv2]
  -- Re-arrange to eliminate t.
  have : x / v1 = (d - x) / v2 := by
    replace h1 : t = x / v1 := by
      refine eq_div_of_mul_eq hv1_pos.ne' ?_
      rw [mul_comm]
      exact h1.symm
    replace h2 : t = (d - x) / v2 := by
      refine eq_div_of_mul_eq hv2_pos.ne' ?_
      rw [eq_sub_iff_add_eq] at h2 ⊢
      rw [add_comm, mul_comm]
      exact h2
    exact h1.symm.trans h2
  -- Cross-multiply.
  rw [div_eq_div_iff hv1_pos.ne' hv2_pos.ne'] at this
  rw [eq_div_iff_mul_eq (add_pos hv1_pos hv2_pos).ne', mul_add]
  rw [sub_mul, eq_sub_iff_add_eq'] at this
  convert this using 1
  exact mul_comm _ _
