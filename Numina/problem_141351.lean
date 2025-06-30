-- https://cloud.kili-technology.com/label/projects/label/cmcboufzi00imueax7a210z7z

import Mathlib

open Real

/- Let $x_i > 0$ ($i = 1, 2, \cdots, n$), $a \in \mathbf{R}^{+}$ and
$\sum_{i=1}^{n} x_i = s \leqslant a$. Prove that:
$\prod_{i=1}^{n} \frac{a + x_i}{a - x_i} \geqslant \left(\frac{n a + s}{n a - s}\right)^n$. -/

theorem inequalities_141351 {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (a : ℝ) (ha : 0 < a) (s : ℝ) (hs : s = ∑ i, x i) (hsa : s ≤ a) :
    ((n * a + s) / (n * a - s)) ^ n ≤ ∏ i, (a + x i) / (a - x i) := by
  -- Note that the statement does hold for `n = 0` but not for `n = 1`
  -- since the denominator `a - x i` could be zero.
  have hs_pos : 0 < s := by
    rw [hs]
    refine Finset.sum_pos (by simpa) ?_
    rw [← Finset.card_ne_zero]
    simpa using Nat.not_eq_zero_of_lt hn

  have hxs (i) : x i < s := by
    suffices 0 < ∑ i ∈ Finset.univ.erase i, x i by simpa [hs]
    refine Finset.sum_pos (fun j _ ↦ hx j) ?_
    rw [Finset.erase_nonempty (Finset.mem_univ i)]
    rw [← Finset.one_lt_card_iff_nontrivial]
    simpa
  have h_elem_pos (i) : 0 < (a + x i) / (a - x i) :=
    div_pos (add_pos ha (hx i)) (by simpa using (hxs i).trans_le hsa)

  refine (log_le_log_iff ?_ ?_).mp ?_
  · refine pow_pos ?_ n
    refine div_pos ?_ ?_
    · refine add_pos (mul_pos ?_ ha) hs_pos
      simpa using Nat.zero_lt_of_lt hn
    · rw [sub_pos]
      refine lt_of_le_of_lt hsa ?_
      exact lt_mul_of_one_lt_left ha (by simpa using hn)
  · exact Finset.prod_pos fun i _ ↦ h_elem_pos i

  have hn_coe : 0 < (n : ℝ) := by simpa using Nat.zero_lt_of_lt hn
  rw [log_pow, log_prod _ _ fun i _ ↦ (h_elem_pos i).ne']
  suffices n * log ((a + s / n) / (a - s / n)) ≤ ∑ i : Fin n, log ((a + x i) / (a - x i)) by
    convert this using 3
    calc _
    _ = ((n * a + s) / n) / ((n * a - s) / n) := (div_div_div_cancel_right₀ hn_coe.ne' _ _).symm
    _ = _ := by simp [add_div, sub_div, hn_coe.ne']
  rw [← le_inv_mul_iff₀ hn_coe]

  suffices ConvexOn ℝ (Set.Ioo 0 a) fun x ↦ log ((a + x) / (a - x)) by
    have := this.map_sum_le (p := x) (t := Finset.univ) (w := fun _ ↦ (n⁻¹ : ℝ))
      (fun i _ ↦ by simp) (by simp [hn_coe.ne']) (fun i _ ↦ ⟨hx i, (hxs i).trans_le hsa⟩)
    simpa [hs, Finset.mul_sum, div_eq_inv_mul] using this

  suffices ConvexOn ℝ (Set.Ioo 0 a) fun x ↦ log (a + x) - log (a - x) by
    refine this.congr fun x hx ↦ ?_
    simp only [Set.mem_Ioo] at hx
    refine (log_div ?_ ?_).symm <;> linarith

  -- TODO: split into two separate results?
  have h_deriv (x : ℝ) (hx : x ∈ Set.Ioo 0 a) :
      HasDerivAt (fun x ↦ log (a + x) - log (a - x)) ((a + x)⁻¹ + (a - x)⁻¹) x := by
    suffices HasDerivAt (fun x ↦ log (a + x) - log (a - x)) (1 / (a + x) - -1 / (a - x)) x by
      simpa [neg_div]
    refine .sub ?_ ?_
    · refine .log ?_ ?_
      · exact (hasDerivAt_id x).const_add a
      · simp only [Set.mem_Ioo] at hx
        linarith
    · refine .log ?_ ?_
      · exact (hasDerivAt_id x).const_sub a
      · simp only [Set.mem_Ioo] at hx
        linarith

  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo 0 a) ?_ ?_ ?_ ?_
    (f' := fun x ↦ (a + x)⁻¹ + (a - x)⁻¹) (f'' := fun x ↦ -1 / (a + x) ^ 2 + -(-1) / (a - x) ^ 2)
  · exact HasDerivAt.continuousOn h_deriv
  · simp only [interior_Ioo]
    intro x hx
    refine HasDerivAt.hasDerivWithinAt ?_
    exact h_deriv x hx
  · simp only [interior_Ioo]
    intro x hx
    simp only [Set.mem_Ioo] at hx
    refine HasDerivAt.hasDerivWithinAt ?_
    refine .add ?_ ?_
    · refine HasDerivAt.inv ?_ (by linarith)
      exact (hasDerivAt_id x).const_add a
    · refine HasDerivAt.inv ?_ (by linarith)
      change HasDerivAt (fun x ↦ a - x) (-1) x
      exact (hasDerivAt_id x).const_sub a
  · intro x hx
    simp only [interior_Ioo, Set.mem_Ioo] at hx
    suffices ((a + x) ^ 2)⁻¹ ≤ ((a - x) ^ 2)⁻¹ by simpa [neg_div]
    refine inv_anti₀ ?_ ?_
    · rw [sq_pos_iff]
      linarith
    · rw [sq_le_sq₀] <;> linarith
