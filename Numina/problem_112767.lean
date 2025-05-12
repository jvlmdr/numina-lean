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
  -- The AM-HM inequality provides `(a + b) / 2 ≥ 1 / (1 / (a + b)) = 2 * a * b / (a + b)`
  -- and hence `1 / (a + b) ≤ (a + b) / (4 * a * b) = c * (a + b) / 4`.
  have h_hm_am {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
      2 * (u * v) / (u + v) ≤ (u + v) / 2 := by
    convert le_trans
      (harm_mean_le_geom_mean Finset.univ (by simp) ![1, 1] ![u, v]
        (by simp [Fin.forall_fin_two]) (by simp)
        (by simpa [Fin.forall_fin_two] using ⟨hu, hv⟩))
      (geom_mean_le_arith_mean (ι := Fin 2) Finset.univ ![1, 1] ![u, v]
        (by simp [Fin.forall_fin_two]) (by simp)
        (by simpa [Fin.forall_fin_two] using ⟨hu.le, hv.le⟩)) using 1
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

  have h_hm_am' {u v w : ℝ} (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (huvw : u * v * w = 1) :
      1 / (u + v) ≤ (u + v) * w / 4 := by
    suffices 1 / (u + v) ≤ (u + v) * w * (u * v) / (4 * (u * v)) by
      convert this using 1
      refine (mul_div_mul_right _ _ ?_).symm
      exact mul_ne_zero hu.ne' hv.ne'
    -- TODO: merge with above and use `calc`?
    suffices 1 / (u + v) ≤ (u + v) * (u * v * w) / (4 * (u * v)) by
      convert this using 2
      ring
    suffices 1 / (u + v) ≤ (u + v) / (4 * (u * v)) by simpa [huvw] using this
    suffices 4 * (u * v) ≤ (u + v) * (u + v) by
      refine (div_le_div_iff₀ ?_ ?_).mpr ?_
      · exact add_pos hu hv
      · exact mul_pos four_pos (mul_pos hu hv)
      convert this using 1
      ring
    suffices 2 * (u * v) / (u + v) ≤ (u + v) / 2 by
      convert (div_le_div_iff₀ ?_ two_pos).mp this using 1
      · ring
      · exact add_pos hu hv
    exact h_hm_am hu hv

  calc _
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
  _ = (a * b + b * c + c * a) / 2 := by ring
  _ ≤ _ := by
    refine div_le_div_of_nonneg_right ?_ two_pos.le
    refine sub_nonneg.mp ?_
    calc _
    _ ≤ ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / 2 := by
      refine div_nonneg ?_ two_pos.le
      exact add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring
