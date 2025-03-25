-- https://cloud.kili-technology.com/label/projects/label/cm8ct0a8402be5kayhi3vzy7t

import Mathlib

open Real

/- Given x, y, z > 0$, and x + y + z = 1.
Prove (1/x^2 + x) * (1/y^2 + y) * (1/z^2 + z) ≥ (28/3)^3. -/

theorem inequalities_159432 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    ((1 / x ^ 2 + x) * (1 / y ^ 2 + y) * (1 / z ^ 2 + z)) ≥ (28 / 3) ^ 3 := by
  simp only [ge_iff_le, one_div]
  -- Note that `fun a ↦ log ((a ^ 2)⁻¹ + a)` is convex on `(0, 1]`.
  -- Re-arrange to apply Jensen's inequality to `(x + y + z) / 3`.
  -- This will provide the lower bound we need since `(x + y + z) / 3 = 3⁻¹` and
  -- `(3⁻¹ ^ 2)⁻¹ + 3⁻¹ = 3^2 + 1 / 3 = 28 / 3`.
  suffices log (28 / 3) ≤ 3⁻¹ * (log ((x ^ 2)⁻¹ + x) + log ((y ^ 2)⁻¹ + y) + log ((z ^ 2)⁻¹ + z)) by
    have h_pos {a : ℝ} (ha : 0 < a) : 0 < (a ^ 2)⁻¹ + a :=
      add_pos (by simp [sq_pos_of_pos ha]) ha
    refine (pow_le_iff_le_log (by norm_num) ?_).mpr ?_
    · exact mul_pos (mul_pos (h_pos hx) (h_pos hy)) (h_pos hz)
    convert (le_inv_mul_iff₀ (by norm_num)).mp this using 1
    rw [log_mul (mul_pos (h_pos hx) (h_pos hy)).ne' (h_pos hz).ne']
    rw [log_mul (h_pos hx).ne' (h_pos hy).ne']
  -- Apply Jensen's inequality.
  suffices ConvexOn ℝ (Set.Ioc 0 1) (fun x : ℝ ↦ log ((x ^ 2)⁻¹ + x)) by
    convert this.map_sum_le (p := fun i : Fin 3 ↦ match i with | 0 => x | 1 => y | 2 => z)
      (w := fun _ ↦ 3⁻¹) (t := .univ) ?_ ?_ ?_ using 1
    · calc log (28 / 3)
      _ = log ((3⁻¹ ^ 2)⁻¹ + 3⁻¹) := by norm_num
      _ = _ := by
        rw [← Finset.smul_sum]
        simp [Fin.sum_univ_three, hsum]
    · rw [← Finset.smul_sum]
      simp [Fin.sum_univ_three]
    · simp
    · simp
    · simp only [Finset.mem_univ, forall_const, Set.mem_Ioc, Fin.forall_fin_succ,
        Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff, and_true]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith
  -- Now it remains to demonstrate the claimed convexity.
  -- Rewrite the log as a difference of logs.
  suffices ConvexOn ℝ (Set.Ioc 0 1) (fun x ↦ log (x ^ 3 + 1) - 2 * log x) by
    refine this.congr ?_
    intro x ⟨hx, _⟩
    symm
    calc log ((x ^ 2)⁻¹ + x)
    _ = log ((x ^ 3 + 1) / (x ^ 2)) := by
      congr
      rw [add_div, div_eq_mul_inv, ← pow_sub₀ _ hx.ne' (by norm_num)]
      ring
    _ = log (x ^ 3 + 1) - 2 * log x := by
      rw [log_div (add_pos (pow_pos hx 3) one_pos).ne' (sq_pos_of_pos hx).ne']
      simp [log_pow]
  -- Eliminate the convex part, `-2 log x`.
  refine .sub ?_ ?_
  swap
  · refine ConcaveOn.smul zero_le_two ?_
    exact strictConcaveOn_log_Ioi.concaveOn.subset Set.Ioc_subset_Ioi_self (convex_Ioc 0 1)
  -- Finally, prove convexity using the second derivative.
  -- The first derivative is `d/dx log (x^3 + 1) = 3 x^2 / (x^3 + 1)`.
  -- The second derivative (excluding the constant) is `d/dx x^2 / (x^3 + 1)`:
  -- `[(x^3 + 1) (2x) - (x^2) (3x^2)] / (x^3 + 1)^2`
  -- `(2x^4 + 2x - 3x^4) / (x^3 + 1)^2`
  -- `x (2 - x^3) / (x^3 + 1)^2`
  -- We can see that this is nonnegative for `x^3 ≤ 2`.
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc 0 1) ?_ ?_ ?_ ?_
    (f' := fun x ↦ 3 * x ^ 2 / (x ^ 3 + 1)) (f'' := fun x ↦ 3 * x * (2 - x ^ 3) / (x ^ 3 + 1) ^ 2)
  · refine ((continuousOn_pow 3).add continuousOn_const).log ?_
    simp only [Set.mem_Ioc]
    exact fun x hx ↦ (add_pos (pow_pos hx.1 3) one_pos).ne'
  · simp only [interior_Ioc, Set.mem_Ioo]
    intro x hx
    refine .log ?_ (add_pos (pow_pos hx.1 3) one_pos).ne'
    exact (hasDerivWithinAt_pow 3 x _).add_const 1
  · simp only [interior_Ioc, Set.mem_Ioo]
    intro x hx
    convert HasDerivWithinAt.div (c' := 3 * (2 * x)) (d' := 3 * x ^ 2) ?_ ?_ ?_ using 1
    · ring
    · simpa using (hasDerivWithinAt_pow 2 x _).const_mul 3
    · exact (hasDerivWithinAt_pow 3 x _).add_const 1
    · exact (add_pos (pow_pos hx.1 3) one_pos).ne'
  -- Last of all, the nonnegativity of the second derivative.
  simp only [interior_Ioc, Set.mem_Ioo]
  intro x hx
  refine div_nonneg (mul_nonneg ?_ ?_) (sq_nonneg _)
  · linarith
  · rw [sub_nonneg]
    -- Show that `x < 1` satisfies `x ^ 3 ≤ 2`.
    exact le_trans (pow_le_pow_left₀ hx.1.le hx.2.le 3) (by norm_num)
