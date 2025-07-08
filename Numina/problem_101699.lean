-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9y000nueax58txwm3z

import Mathlib

open Real

/- Solve the system of equations:
$$
\left\{\begin{array}{l}
\frac{1}{\sqrt{1 + 2 x^2}}+\frac{1}{\sqrt{1 + 2 y^2}} = \frac{2}{\sqrt{1 + 2 x y}}, \\
\sqrt{x (1 - 2 x)} + \sqrt{y (1 - 2 y)} = \frac{2}{9}
\end{array} .\right.
$$
-/

-- The second derivative of `(√(1 + 2 * exp x))⁻¹`.
-- This can be used to prove (strict) convex or concave.
-- Note that its sign depends on that of `exp x - 1` and hence that of `x`.
lemma lemma_1 (x : ℝ) : deriv^[2] (fun x ↦ (√(1 + 2 * exp x))⁻¹) x =
    (1 + 2 * exp x) ^ (-5/2 : ℝ) * exp x * (exp x - 1) := by
  -- Rewrite as the composition of `f ∘ g`.
  let g (x : ℝ) : ℝ := 1 + 2 * exp x
  let f (x : ℝ) : ℝ := (g x) ^ (-1/2 : ℝ)
  -- Take derivatives using `HasDerivAt`.
  have hg (x) : 0 < g x := by simp [g, add_pos, exp_pos]
  have hg_deriv (x) : HasDerivAt g (2 * exp x) x :=
    .const_add 1 (.const_mul 2 (hasDerivAt_exp x))
  have hf_deriv (x) : HasDerivAt f (exp x * -g x ^ (-3/2 : ℝ)) x := by
    convert (hg_deriv x).rpow_const (p := -1/2) (.inl (hg x).ne') using 1
    calc _
    _ = exp x * -g x ^ (-1/2 - 1 : ℝ) := by norm_num
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
  -- Put it all together.
  calc _
  _ = deriv^[2] f x := by
    refine congrArg (deriv^[2] · x) ?_
    funext x
    simp [f, neg_div, rpow_neg (hg x).le, sqrt_eq_rpow]
  _ = deriv (deriv f) x := by simp
  _ = deriv (fun x ↦ exp x * -g x ^ (-3/2 : ℝ)) x := by
    congr
    funext x
    exact (hf_deriv x).deriv
  _ = g x ^ (-5/2 : ℝ) * exp x * (exp x - 1) := (hf_deriv2 x).deriv

-- The function is therefore convex on `x < 0`.
lemma lemma_2 : StrictConcaveOn ℝ (Set.Iio 0) fun x ↦ (√(1 + 2 * exp x))⁻¹ := by
  have hg (x) : 0 < 1 + 2 * exp x := by simp [add_pos, exp_pos]
  refine strictConcaveOn_of_deriv2_neg' (convex_Iio 0) ?_ ?_
  · refine .inv₀ ?_ fun x _ ↦ sqrt_ne_zero'.mpr (hg x)
    refine Continuous.continuousOn ?_
    exact .sqrt <| continuous_const.add <| continuous_const.mul continuous_exp
  intro x hx
  rw [lemma_1]
  refine mul_neg_of_pos_of_neg ?_ ?_
  · exact mul_pos (rpow_pos_of_pos (hg x) _) (exp_pos x)
  · simpa using hx

-- Once we have constrained the domain to `0 < x, y < 1`, strong concavity provides equality.
lemma lemma_3 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx' : x < 1) (hy' : y < 1)
    (h : 1 / √(1 + 2 * x ^ 2) + 1 / √(1 + 2 * y ^ 2) = 2 / √(1 + 2 * x * y)) :
    x = y := by
  -- Apply Jensen's inequality to the average of `log (x^2)` and `log (y^2)`.
  have := lemma_2.map_sum_eq_iff (t := Finset.univ) (w := ![2⁻¹, 2⁻¹])
    (p := ![log (x ^ 2), log (y ^ 2)]) (by simp [Fin.forall_fin_two])
    (by simpa using add_halves (1 : ℝ))
    (by
      suffices 2 * log x < 0 ∧ 2 * log y < 0 by simpa [Fin.forall_fin_two]
      split_ands
      · exact mul_neg_of_pos_of_neg two_pos (log_neg hx (by linarith))
      · exact mul_neg_of_pos_of_neg two_pos (log_neg hy (by linarith)))
  have := this.mp (by
    -- Re-arrange `h₁` to represent a mean as required by `map_sum_eq_iff`.
    suffices (√(1 + 2 * x * y))⁻¹ = 2⁻¹ * (√(1 + 2 * x ^ 2))⁻¹ + 2⁻¹ * (√(1 + 2 * y ^ 2))⁻¹ by
      convert this using 1
      · simp [← log_mul hx.ne' hy.ne', exp_log (mul_pos hx hy), mul_assoc]
      · simp [exp_log (sq_pos_of_pos hx), exp_log (sq_pos_of_pos hy), -log_pow]
    -- Divide through by 2 to obtain this form.
    convert congrArg (· / 2) h.symm using 1 <;> ring)
  -- This provides `2 log x = log x + log y = 2 log y` and hence `x = y`.
  have hfx : 2 * log x = log x + log y := by simpa using this 0 (Finset.mem_univ 0)
  have hfy : 2 * log y = log x + log y := by simpa using this 1 (Finset.mem_univ 1)
  exact log_injOn_pos hx hy (by simpa using hfx.trans hfy.symm)

theorem algebra_101699 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hx' : 0 ≤ x * (1 - 2 * x)) (hy' : 0 ≤ y * (1 - 2 * y))
    (h₁ : 1 / √(1 + 2 * x ^ 2) + 1 / √(1 + 2 * y ^ 2) = 2 / √(1 + 2 * x * y))
    (h₂ : √(x * (1 - 2 * x)) + √(y * (1 - 2 * y)) = 2 / 9) :
    x = y ∧ (x = 1 / 4 + √73 / 36 ∨ x = 1 / 4 - √73 / 36) := by
  -- First, establish that `x` and `y` are both positive.
  -- From `h₁`, we establish that `x = 0 → y = 0` (and vice versa by symmetry).
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
  -- However, this is inconsistent with `h₂`, and hence neither are zero.
  have ⟨hx_ne, hy_ne⟩ : x ≠ 0 ∧ y ≠ 0 := by
    suffices ¬(x = 0 ∧ y = 0) by
      contrapose! this
      simpa [h_zero] using this
    rintro ⟨rfl, rfl⟩
    suffices 0 ≠ (2 / 9 : ℝ) from this (by simpa using h₂)
    norm_num
  replace hx : 0 < x := lt_of_le_of_ne hx hx_ne.symm
  replace hy : 0 < y := lt_of_le_of_ne hy hy_ne.symm

  -- Further, establish that `x` and `y` are bounded above (to make the square root valid).
  replace hx' : 2 * x ≤ 1 := by simpa using nonneg_of_mul_nonneg_right hx' hx
  replace hy' : 2 * y ≤ 1 := by simpa using nonneg_of_mul_nonneg_right hy' hy

  -- Use the strong concavity lemma to eliminate `y`.
  have hxy : x = y := lemma_3 hx hy (by linarith) (by linarith) h₁
  refine ⟨hxy, ?_⟩
  rcases hxy with rfl

  rw [← two_mul, div_eq_mul_inv, mul_right_inj' two_ne_zero] at h₂
  rw [sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)] at h₂
  rw [← sq, inv_pow] at h₂
  -- Put in the form `a * (x * x) + b * x + c = 0` for use with `discrim`.
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
