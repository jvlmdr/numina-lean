-- https://cloud.kili-technology.com/label/projects/label/cma3ygioc00d9ahayd27p6org

import Mathlib

open Real

/- Let $a, b, c$ be positive real numbers such that $a b c = 1$. Prove that
$$
\frac{1}{a+b} + \frac{1}{b+c} + \frac{1}{a+c} \leq \frac{a^{2}+b^{2}+c^{2}}{2}
$$
-/

theorem inequalities_112767 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a + b) + 1 / (b + c) + 1 / (a + c) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
  -- The AM-HM inequality provides `(a + b) / 2 ≥ 2 * a * b / (a + b)`
  -- and hence `1 / (a + b) ≤ (a + b) / (4 * a * b) = c * (a + b) / 4`.
  -- First combine the AM-GM and GM-HM inequalities to obtain the AM-HM inequality.
  have h_hm_am {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
      2 * (u * v) / (u + v) ≤ (u + v) / 2 := by
    convert le_trans
      (harm_mean_le_geom_mean Finset.univ (by simp) ![1, 1] ![u, v]
        (by simp [Fin.forall_fin_two]) (by simp) (by simp [Fin.forall_fin_two, hu, hv]))
      (geom_mean_le_arith_mean (ι := Fin 2) Finset.univ ![1, 1] ![u, v]
        (by simp [Fin.forall_fin_two]) (by simp) (by simp [Fin.forall_fin_two, hu.le, hv.le]))
      using 1
    · symm
      calc _
      _ = (1 + 1) / (u⁻¹ + v⁻¹) := by simp
      _ = 2 / (u⁻¹ + v⁻¹) := by norm_num
      _ = 2 * (u * v) / ((u⁻¹ + v⁻¹) * (u * v)) := by
        symm
        refine mul_div_mul_right _ _ ?_
        exact mul_ne_zero hu.ne' hv.ne'
      _ = 2 * (u * v) / (u + v) := by
        rw [add_comm, add_mul]
        congr
        · rw [mul_comm u v]
          exact inv_mul_cancel_left₀ hv.ne' u
        · exact inv_mul_cancel_left₀ hu.ne' v
    · symm
      calc _
      _ = (u + v) / (1 + 1) := by simp
      _ = _ := by norm_num

  -- Now re-arrange the terms and use `a b c = 1`.
  have h_hm_am' {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (huvw : u * v * w = 1) :
      1 / (u + v) ≤ (u + v) * w / 4 := by
    -- Replace `w` with `1 / (u * v)`.
    suffices 1 / (u + v) ≤ (u + v) / (4 * (u * v)) by
      convert this using 1
      calc _
      _ = (u + v) * w * (u * v) / (4 * (u * v)) := by
        refine (mul_div_mul_right _ _ ?_).symm
        exact mul_ne_zero hu.ne' hv.ne'
      _ = (u + v) * (u * v * w) / (4 * (u * v)) := by ring
      _ = _ := by simp [huvw]
    -- Multiply both sides by 2.
    suffices 2 / (u + v) ≤ (u + v) / (2 * (u * v)) by
      refine (mul_le_mul_right two_pos).mp ?_
      convert this using 1 <;> ring
    -- Take the inverse of both sides.
    refine (inv_le_inv₀ ?_ ?_).mp ?_
    · refine div_pos ?_ (mul_pos two_pos ?_)
      · exact add_pos hu hv
      · exact mul_pos hu hv
    · exact div_pos two_pos (add_pos hu hv)
    convert h_hm_am hu hv using 1 <;> simp

  calc _
  -- Apply our inequality to each term.
  _ ≤ (a + b) * c / 4 + (b + c) * a / 4 + (c + a) * b / 4 := by
    refine add_le_add (add_le_add ?_ ?_) ?_
    · exact h_hm_am' ha hb hc habc
    · refine h_hm_am' hb hc ha ?_
      convert habc using 1
      ring
    · rw [add_comm]
      refine h_hm_am' hc ha hb ?_
      convert habc using 1
      ring
  -- Expand and gather terms.
  _ = (a * b + b * c + c * a) / 2 := by ring
  _ ≤ _ := by
    -- Rewrite as a non-negative difference.
    refine div_le_div_of_nonneg_right ?_ two_pos.le
    refine sub_nonneg.mp ?_
    -- Show that this difference is equal to a sum of squares.
    calc _
    _ ≤ ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2 := by
      refine div_nonneg ?_ two_pos.le
      exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring
