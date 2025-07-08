-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9y000nueax58txwm3z

import Mathlib

open Real
open scoped Pointwise

/- Solve the system of equations:
$$
\left\{\begin{array}{l}
\frac{1}{\sqrt{1 + 2 x^2}}+\frac{1}{\sqrt{1 + 2 y^2}} = \frac{2}{\sqrt{1 + 2 x y}}, \\
\sqrt{x (1 - 2 x)} + \sqrt{y (1 - 2 y)} = \frac{2}{9}
\end{array} .\right.
$$
-/

lemma image_sqrt_Ioi {a : ℝ} (ha : 0 ≤ a) : ((fun x ↦ √x) '' Set.Ioi a) = Set.Ioi √a := by
  refine Set.Subset.antisymm ?_ ?_
  · refine StrictMonoOn.image_Ioi_subset ?_
    refine .mono ?_ (Set.Ici_subset_Ici.mpr ha)
    intro x hx y hy hxy
    simp
    exact sqrt_lt_sqrt hx hxy
  · intro x hx
    rw [Set.mem_Ioi] at hx
    rw [Set.mem_image]
    use x ^ 2
    split_ands
    · rw [Set.mem_Ioi]
      exact lt_sq_of_sqrt_lt hx
    · suffices 0 ≤ x by simp [this]
      exact (sqrt_nonneg a).trans hx.le

lemma strictConvexOn_inv_sqrt : StrictConvexOn ℝ (Set.Ioi 0) fun x ↦ (√x)⁻¹ := by
  refine StrictConvexOn.comp_strictConcaveOn (g := fun x ↦ x⁻¹) (f := fun x ↦ √x) ?_ ?_ ?_ ?_
  · suffices StrictConvexOn ℝ (Set.Ioi 0) fun x : ℝ ↦ x⁻¹ by simpa [image_sqrt_Ioi] using this
    suffices StrictConvexOn ℝ (Set.Ioi 0) fun x : ℝ ↦ x ^ (-1 : ℤ) by simpa
    refine strictConvexOn_zpow ?_ ?_ <;> norm_num
  · refine Real.strictConcaveOn_sqrt.subset ?_ (convex_Ioi 0)
    exact Set.Ioi_subset_Ici_self
  · refine StrictAntiOn.mono inv_strictAntiOn ?_
    rw [Set.image_subset_iff]
    intro x
    simp
  · intro x hx y hy
    simp only [Set.mem_Ioi] at hx hy
    simp [sqrt_inj hx.le hy.le]

lemma lemma_1 (x : ℝ) : deriv^[2] (fun x ↦ (√(1 + 2 * exp x))⁻¹) x =
    (1 + 2 * exp x) ^ (-5/2 : ℝ) * exp x * (exp x - 1) := by
  let g (x : ℝ) : ℝ := 1 + 2 * exp x
  let f (x : ℝ) : ℝ := (g x) ^ (-1 / 2 : ℝ)
  have hg (x) : 0 < g x := by simp [g, add_pos, exp_pos]

  have hg_deriv (x) : HasDerivAt g (2 * exp x) x :=
    .const_add 1 (.const_mul 2 (hasDerivAt_exp x))
  have hf_deriv (x) : HasDerivAt f (exp x * -g x ^ (-3 / 2 : ℝ)) x := by
    convert (hg_deriv x).rpow_const (p := -1/2) (.inl (hg x).ne') using 1
    calc _
    _ = exp x * -g x ^ (-1 / 2 - 1 : ℝ) := by norm_num
    _ = _ := by ring

  have hf_deriv2 (x) : HasDerivAt (fun x ↦ exp x * -g x ^ (-3/2 : ℝ))
      (g x ^ (-5/2 : ℝ) * exp x * (exp x - 1)) x := by
    convert (hasDerivAt_exp x).mul ((hg_deriv x).rpow_const (p := -3/2) (.inl (hg x).ne')).neg
      using 1
    calc _
    _ = exp x * g x ^ (-5/2 : ℝ) * (3 * exp x - g x) := by ring
    _ = exp x * (3 * exp x * g x ^ (-5/2 : ℝ) - g x ^ (-5/2 + 1 : ℝ)) := by
      rw [rpow_add_one (hg x).ne']
      ring
    _ = exp x * (3 * exp x * g x ^ (-3/2 - 1 : ℝ) - g x ^ (-3/2 : ℝ)) := by norm_num
    _ = _ := by ring

  calc _
  _ = deriv^[2] f x := by
    refine congrArg (deriv^[2] · x) ?_
    funext x
    simp [f, neg_div, rpow_neg (hg x).le, sqrt_eq_rpow]
  _ = deriv (deriv f) x := by simp
  _ = deriv (fun x ↦ exp x * -g x ^ (-3 / 2 : ℝ)) x := by
    congr
    funext x
    exact (hf_deriv x).deriv
  _ = g x ^ (-5/2 : ℝ) * exp x * (exp x - 1) := (hf_deriv2 x).deriv

lemma lemma_a : StrictConvexOn ℝ (Set.Ioi 0) fun x ↦ (√(1 + 2 * exp x))⁻¹ := by
  let g (x : ℝ) : ℝ := 1 + 2 * exp x
  let f (x : ℝ) : ℝ := (g x) ^ (-1 / 2 : ℝ)
  have hg (x) : 0 < g x := by simp [g, add_pos, exp_pos]

  suffices StrictConvexOn ℝ (Set.Ioi 0) f by
    refine this.congr fun x _ ↦ ?_
    unfold f
    rw [neg_div, rpow_neg (hg x).le, sqrt_eq_rpow]

  refine strictConvexOn_of_deriv2_pos' (convex_Ioi 0) ?_ ?_
  · refine Continuous.continuousOn ?_
    refine .rpow_const ?_ fun x ↦ .inl (hg x).ne'
    exact continuous_const.add (continuous_const.mul continuous_exp)

  have hg_deriv (x) : HasDerivAt g (2 * exp x) x :=
    .const_add 1 (.const_mul 2 (hasDerivAt_exp x))
  have hf_deriv (x) : HasDerivAt f (exp x * -g x ^ (-3 / 2 : ℝ)) x := by
    convert (hg_deriv x).rpow_const (p := -1/2) (.inl (hg x).ne') using 1
    calc _
    _ = exp x * -g x ^ (-1 / 2 - 1 : ℝ) := by norm_num
    _ = _ := by ring
  have hf_deriv2 (x) : HasDerivAt (fun x ↦ exp x * -g x ^ (-3/2 : ℝ))
      (g x ^ (-5/2 : ℝ) * exp x * (exp x - 1)) x := by
    convert (hasDerivAt_exp x).mul ((hg_deriv x).rpow_const (p := -3/2) (.inl (hg x).ne')).neg
      using 1
    calc _
    _ = exp x * g x ^ (-5/2 : ℝ) * (3 * exp x - g x) := by ring
    _ = exp x * (3 * exp x * g x ^ (-5/2 : ℝ) - g x ^ (-5/2 + 1 : ℝ)) := by
      rw [rpow_add_one (hg x).ne']
      ring
    _ = exp x * (3 * exp x * g x ^ (-3/2 - 1 : ℝ) - g x ^ (-3/2 : ℝ)) := by norm_num
    _ = _ := by ring

  intro x hx
  calc _
  _ = deriv (deriv f) x := by simp
  _ = deriv (fun x ↦ exp x * -g x ^ (-3 / 2 : ℝ)) x := by
    congr
    funext x
    exact (hf_deriv x).deriv
  _ = g x ^ (-5/2 : ℝ) * exp x * (exp x - 1) := (hf_deriv2 x).deriv
  _ > (0 : ℝ) := by
    refine mul_pos ?_ ?_
    · refine mul_pos ?_ (exp_pos x)
      exact rpow_pos_of_pos (hg x) (-5/2)
    simpa using hx


theorem algebra_101699 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h₁ : 1 / √(1 + 2 * x ^ 2) + 1 / √(1 + 2 * y ^ 2) = 2 / √(1 + 2 * x * y))
    (h₂ : √(x * (1 - 2 * x)) + √(y * (1 - 2 * y)) = 2 / 9) :
    x = y ∧ (x = 1 / 4 + √73 / 36 ∨ x = 1 / 4 - √73 / 36) := by

  suffices x = y by
    refine ⟨this, ?_⟩
    rcases this with rfl
    rw [← two_mul, div_eq_mul_inv, mul_right_inj' two_ne_zero] at h₂
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)] at h₂
    rw [← sq, inv_pow] at h₂
    -- Put in the form `a * (x * x) + b * x + c = 0` to use with `discrim`.
    replace h₂ : 2 * (x * x) + -1 * x + (9 ^ 2)⁻¹ = 0 := by
      convert sub_eq_zero.mpr h₂ using 1
      ring
    suffices x = (- -1 + √73 / 9) / (2 * 2) ∨ x = (- -1 - √73 / 9) / (2 * 2) by
      convert this using 2 <;> ring
    refine (quadratic_eq_zero_iff two_ne_zero ?_ x).mp h₂
    unfold discrim
    calc _
    _ = (73 / 9 ^ 2 : ℝ) := by ring
    _ = (√73 / 9) ^ 2 := by simp [div_pow]
    _ = _ := by ring

  -- TODO: extract this from `h₁`?
  have h_zero : x = 0 ↔ y = 0 := by
    constructor
    · rintro rfl
      suffices (√(1 + 2 * y ^ 2))⁻¹ = 1 by simpa
      suffices 1 + (√(1 + 2 * y ^ 2))⁻¹ = 2 by
        convert eq_sub_iff_add_eq'.mpr this
        norm_num
      simpa using h₁
    · rintro rfl
      suffices (√(1 + 2 * x ^ 2))⁻¹ = 1 by simpa
      suffices (√(1 + 2 * x ^ 2))⁻¹ + 1 = 2 by
        convert eq_sub_iff_add_eq.mpr this
        norm_num
      simpa using h₁

  have ⟨hx_ne, hy_ne⟩ : x ≠ 0 ∧ y ≠ 0 := by
    suffices ¬(x = 0 ∧ y = 0) by
      contrapose! this
      simpa [h_zero] using this
    rintro ⟨rfl, rfl⟩
    suffices 0 ≠ (2 / 9 : ℝ) from this (by simpa using h₂)
    norm_num

  have hx : 0 < x := lt_of_le_of_ne hx hx_ne.symm
  have hy : 0 < y := lt_of_le_of_ne hy hy_ne.symm

  suffices StrictConvexOn ℝ Set.univ fun u ↦ (√(1 + 2 * exp u))⁻¹ by
    have := this.map_sum_eq_iff (t := Finset.univ) (w := ![2⁻¹, 2⁻¹])
      (p := ![log (x ^ 2), log (y ^ 2)]) (by simp [Fin.forall_fin_two])
      (by simpa using add_halves (1 : ℝ)) fun i hi ↦ Set.mem_univ i
    have := this.mp (by
      -- Re-arrange `h₁` to represent a mean as required by `map_sum_eq_iff`.
      suffices (√(1 + 2 * x * y))⁻¹ = 2⁻¹ * (√(1 + 2 * x ^ 2))⁻¹ + 2⁻¹ * (√(1 + 2 * y ^ 2))⁻¹ by
        convert this using 1
        · simp [← log_mul hx.ne' hy.ne', exp_log (mul_pos hx hy), mul_assoc]
        · simp [exp_log (sq_pos_of_pos hx), exp_log (sq_pos_of_pos hy), -log_pow]
      -- Divide through by 2 to obtain this form.
      convert congrArg (· / 2) h₁.symm using 1 <;> ring)
    have hfx : 2 * log x = log x + log y := by simpa using this 0 (Finset.mem_univ 0)
    have hfy : 2 * log y = log x + log y := by simpa using this 1 (Finset.mem_univ 1)
    exact log_injOn_pos hx hy (by simpa using hfx.trans hfy.symm)

  -- Unfortunately, this does not hold.
  convert lemma_a using 1
  sorry
