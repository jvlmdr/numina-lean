-- https://cloud.kili-technology.com/label/projects/label/cma3ygf29006zahayogw9nqez

import Mathlib

open Real

/- If for any $x \in(-\infty,-1)$, we have
$$
(m - m^{2}) 4^{x} + 2^{x} + 1 > 0,
$$
then the range of real number $m$ is? -/

theorem inequalities_148288 (m : ℝ) :
    (∀ x : ℝ, x < -1 → 0 < (m - m^2) * 4^x + 2^x + 1) ↔ m ∈ Set.Icc (-2) 3 := by
  -- Let `a = m - m^2` for ease of notation.
  generalize ha : m - m^2 = a

  calc _
  -- Rewrite such that only dependence on `x` is through `2 ^ x`.
  _ ↔ ∀ x : ℝ, x < -1 → 0 < a * (2 ^ x) ^ 2 + 2 ^ x + 1 := by
    refine forall₂_congr fun x hx ↦ ?_
    suffices (4 : ℝ) ^ x = (2 ^ x) ^ 2 by rw [this]
    calc _
    _ = (2 ^ 2 : ℝ) ^ x := by norm_num
    _ = _ := by
      simp only [← rpow_two, ← rpow_mul two_pos.le]
      rw [mul_comm x 2]
  -- Replace `x ∈ (-∞, -1)` with `t = 2^x ∈ (0, 1/2)`.
  _ ↔ ∀ t : ℝ, t ∈ (2 ^ · : ℝ → ℝ) '' Set.Iio (-1) → 0 < a * t ^ 2 + t + 1 :=
    Iff.symm Set.forall_mem_image
  _ ↔ ∀ t ∈ Set.Ioo 0 2⁻¹, 0 < a * t ^ 2 + t + 1 := by
    suffices (2 ^ · : ℝ → ℝ) '' Set.Iio (-1) = Set.Ioo 0 (2⁻¹ : ℝ) by rw [this]
    refine Set.BijOn.image_eq ?_
    refine Set.InvOn.bijOn (f' := logb 2) ?_ ?_ ?_
    · constructor
      · intro x
        simp
      · intro t
        simp only [Set.mem_Ioo, and_imp]
        intro ht _
        exact rpow_logb two_pos (by norm_num) ht
    · intro x
      simp only [Set.mem_Iio, Set.mem_Ioo]
      intro hx
      refine ⟨?_, ?_⟩
      · exact rpow_pos_of_pos two_pos x
      · simpa [← rpow_neg_one] using hx
    · intro t
      simp only [Set.mem_Ioo, Set.mem_Iio, and_imp]
      intro ht ht'
      suffices logb 2 t < logb 2 2⁻¹ by simpa using this
      refine ((strictMonoOn_logb one_lt_two).lt_iff_lt ?_ ?_).mpr ht'
      · simpa using ht
      · norm_num

  _ ↔ -6 ≤ a := by
    -- We can assume `a < 0` since the inequality is trivially satisfied for `0 ≤ a`.
    wlog ha_neg : a < 0
    · rw [not_lt] at ha_neg
      refine iff_of_true ?_ ?_
      · simp only [Set.mem_Ioo, and_imp]
        intro t ht _
        refine add_pos_of_nonneg_of_pos ?_ one_pos
        exact add_nonneg (mul_nonneg ha_neg (sq_nonneg t)) ht.le
      · exact le_trans (by norm_num) ha_neg
    -- Due to (strong) concavity of the quadratic, it suffices to ensure condition at boundaries.
    -- When `t = 0`, we have `0 < 1`.
    -- When `t = 1/2`, we have `0 < a/4 + 1/2 + 1 = a/4 + 3/2`.
    -- As the condition is trivially satisfied at `t = 0`, it suffices to consider `t = 1/2`.
    calc _
    _ ↔ 0 ≤ a * 2⁻¹ ^ 2 + 2⁻¹ + 1 := by
      constructor
      -- The reverse direction is easily proved using convexity.
      -- However, we don't have an iff theorem for the infimum of the image.
      · intro h
        -- Given that `a * t^2 + t + 1` is greater than zero on `(0, 1/2)`,
        -- we need to show that it is also greater than or equal to zero at `t = 1/2`.
        -- This should follow from continuity. Use the closure of the image of the set.
        have h_cont : Continuous (fun t ↦ a * t ^ 2 + t + 1) := by
          refine .add (.add ?_ continuous_id') continuous_const
          exact .mul continuous_const (continuous_pow 2)
        suffices ∀ t ∈ Set.Icc 0 2⁻¹, a * t ^ 2 + t + 1 ∈ Set.Ici 0 from this 2⁻¹ (by simp)
        suffices (fun t ↦ a * t ^ 2 + t + 1) '' Set.Icc 0 2⁻¹ ⊆ Set.Ici 0 from
          fun t ht ↦ this (Set.mem_image_of_mem _ ht)
        -- Rewrite closed invervals as closure of open intervals.
        suffices (fun t ↦ a * t ^ 2 + t + 1) '' closure (Set.Ioo 0 2⁻¹) ⊆ closure (Set.Ioi 0) by
          simpa using this
        -- Employ continuity of the function for the image of the closure.
        refine .trans (image_closure_subset_closure_image h_cont) ?_
        -- Combine the original assumption with monotonicity of taking the closure.
        refine closure_mono ?_
        rw [Set.subset_def, Set.forall_mem_image]
        exact h
      -- The reverse direction follows from (strict) concavity.
      · have h_concave : StrictConcaveOn ℝ Set.univ (fun t ↦ a * t ^ 2 + t + 1) := by
          refine .add_const ?_ 1
          refine .add_concaveOn ?_ (concaveOn_id convex_univ)
          refine strictConcaveOn_univ_of_deriv2_neg ?_ ?_
          · exact .mul continuous_const (continuous_pow 2)
          · intro x
            suffices a * 2 < 0 by simpa [deriv_const_mul_field (2 : ℝ)] using this
            linarith
        -- Employ strict concavity to show that all elements of the interval are positive.
        intro ha t ht
        refine lt_of_le_of_lt ?_ (h_concave.lt_on_openSegment (Set.mem_univ 0) (Set.mem_univ 2⁻¹)
          (by norm_num) (by simpa using ht))
        -- The left inequality is satisfied trivially, the right by assumption.
        exact le_min (by simp) ha

    -- Left inequality is always satisfied, hence only interested in the right.
    _ ↔ 0 ≤ a * 2⁻¹ ^ 2 + 2⁻¹ + 1 := by simp
    -- Now simple manipulation provides `-6 ≤ a`.
    _ ↔ 0 ≤ a / 4 + 3 / 2 := by
      refine propext_iff.mp ?_
      congr 1
      ring
    _ ↔ -(3 / 2) ≤ a / 4 := neg_le_iff_add_nonneg.symm
    _ ↔ -(3 / 2) * 4 ≤ a := le_div_iff₀ (by norm_num)
    _ ↔ _ := by norm_num

  -- Finally, obtain the condition in terms of `m` rather than `a`.
  _ ↔ -6 ≤ m - m ^ 2 := by rw [ha]
  _ ↔ -6 ≤ -(m ^ 2 - m) := by simp
  _ ↔ m ^ 2 - m - 6 ≤ 0 := by simp [add_comm]
  -- Factor the nonpositive quadratic.
  _ ↔ (m + 2) * (m - 3) ≤ 0 := by
    suffices m ^ 2 - m - 6 = (m + 2) * (m - 3) by rw [this]
    ring
  _ ↔ _ := by
    rw [mul_nonpos_iff, Set.mem_Icc]
    -- Eliminate the empty case.
    convert or_iff_left ?_ using 1
    · exact and_congr neg_le_iff_add_nonneg sub_nonpos.symm
    · intro h
      linarith  -- Contradiction: Cannot have `m ≤ -2` and `3 ≤ m`.
