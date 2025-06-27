-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9y000mueax32tjiweo

import Mathlib

open Real

/- Prove that if $x > -1$ and $x \neq 0$, then
$$
\frac{2 |x|}{2 + x} < |\ln (1+x)| < \frac{|x|}{\sqrt{1 + x}}
$$
-/

lemma rpow_three_div_two {x : ℝ} (hx : 0 < x) : x ^ (3 / 2 : ℝ) = x * √x :=
  calc _
  _ = x ^ (1 + 1 / 2 : ℝ) := by norm_num
  _ = _ := by simp [rpow_add hx, sqrt_eq_rpow]

lemma rpow_three_div_two' {x : ℝ} (hx : 0 < x) : x ^ (3 / 2 : ℝ) = √x * x :=
  calc _
  _ = x ^ (1 / 2 + 1 : ℝ) := by norm_num
  _ = _ := by simp [rpow_add hx, sqrt_eq_rpow]

theorem inequalities_229436 {x : ℝ} (hx_gt : x > -1) (hx_ne : x ≠ 0) :
    2 * |x| / (2 + x) < |log (1 + x)| ∧ |log (1 + x)| < |x| / √(1 + x) := by

  have hx_one_add : 0 < 1 + x := by linarith

  have h₂ (x : ℝ) (hx : -1 < x) : HasDerivAt (fun x ↦ log (1 + x)) (1 / (1 + x)) x := by
    refine .log ?_ (by linarith)
    exact .const_add 1 (hasDerivAt_id' x)
  have h₁ (x : ℝ) (hx : -1 < x) :
      HasDerivAt (fun x ↦ 2 * x / (2 + x)) (4 / (2 + x) ^ 2) x := by
    convert HasDerivAt.div (.const_mul 2 (hasDerivAt_id' x)) (.const_add 2 (hasDerivAt_id' x)) ?_
      using 1
    · ring
    · linarith
  have h₃ (x : ℝ) (hx : -1 < x) :
      HasDerivAt (fun x ↦ x / √(1 + x)) ((2 + x) / (2 * (1 + x) ^ (3 / 2 : ℝ))) x := by
    convert HasDerivAt.div (hasDerivAt_id' x) (.sqrt (.const_add 1 (hasDerivAt_id' x)) ?_) ?_
      using 1
    · rw [sq_sqrt (by linarith)]
      -- Note: Could eliminate common factor of `1 + x` in numerator and denominator.
      rw [div_eq_div_iff]
      rotate_left
      · suffices (1 + x) ^ (3 / 2 : ℝ) ≠ 0 by simpa
        rw [rpow_ne_zero] <;> linarith
      · linarith
      rw [rpow_three_div_two (by linarith)]
      calc _
      _ = (2 * (1 + x) - x * 1) * (1 + x) := by ring
      _ = (2 * √(1 + x) ^ 2 - x * (√(1 + x) / √(1 + x))) * (1 + x) := by
        congr
        · rw [sq_sqrt (by linarith)]
        · rw [div_self]
          rw [sqrt_ne_zero']
          linarith
      _ = _ := by ring
    · linarith
    · rw [sqrt_ne_zero']  -- TODO: replace all the linariths?
      linarith

  let f := fun x : ℝ ↦ log (1 + x) - 2 * x / (2 + x)
  let g := fun x : ℝ ↦ x / √(1 + x) - log (1 + x)

  -- The sign of `log (1 + x)` matches the sign of `x`.
  have h_log_pos : 0 < log (1 + x) ↔ 0 < x := by simpa using log_pos_iff hx_one_add
  have h_log_neg : log (1 + x) < 0 ↔ x < 0 := by simpa using log_neg_iff hx_one_add

  have hf_deriv (x : ℝ) (hx : -1 < x) : HasDerivAt f (x ^ 2 / ((1 + x) * (2 + x) ^ 2)) x := by
    convert ((h₂ x hx).sub (h₁ x hx)) using 1
    rw [div_sub_div]
    rotate_left
    · linarith
    · refine pow_ne_zero 2 ?_
      linarith
    ring

  have hg_deriv (x : ℝ) (hx : -1 < x) :
      HasDerivAt g ((1 - √(1 + x)) ^ 2 / (2 * (1 + x) ^ (3 / 2 : ℝ))) x := by
    convert ((h₃ x hx).sub (h₂ x hx)) using 1
    calc _
    _ = (2 + x - 2 * √(1 + x)) / (2 * (1 + x) ^ (3 / 2 : ℝ)) := by
      congr 1
      rw [sub_sq, sq_sqrt (by linarith)]
      ring
    _ = _ := by
      rw [sub_div]
      congr 1
      calc _
      _ = 2 * √(1 + x) / (2 * √(1 + x) * (1 + x)) := by
        congr 1
        rw [rpow_three_div_two (by linarith)]
        ring
      _ = (1 + x)⁻¹ := by
        refine div_mul_cancel_left₀ ?_ (1 + x)
        simpa using sqrt_ne_zero'.mpr (by linarith)  -- TODO: surprising that this works?
      _ = _ := by simp

  have hf_cont : ContinuousOn f (Set.Ioi (-1)) :=
    HasDerivAt.continuousOn fun x hx ↦ hf_deriv x (Set.mem_Ioi.mp hx)
  have hg_cont : ContinuousOn g (Set.Ioi (-1)) :=
    HasDerivAt.continuousOn fun x hx ↦ hg_deriv x (Set.mem_Ioi.mp hx)

  cases lt_or_gt_of_ne hx_ne with
  | inr hx =>
    suffices f 0 < f x ∧ g 0 < g x by simpa [f, g, abs_of_pos, hx, h_log_pos.mpr hx]
    split_ands
    · suffices StrictMonoOn f (Set.Ici 0) from
        (this.lt_iff_lt (by simp) (by simpa using hx.le)).mpr hx
      refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) ?_
        (fun x hx ↦ (hf_deriv x ?_).hasDerivWithinAt) fun x hx ↦ ?_
      · refine hf_cont.mono ?_
        refine Set.Ici_subset_Ioi.mpr ?_
        exact neg_one_lt_zero
      · simp only [interior_Ici, Set.mem_Ioi] at hx
        linarith
      · simp only [interior_Ici, Set.mem_Ioi] at hx
        refine div_pos (pow_pos hx 2) ?_
        refine mul_pos ?_ (pow_pos ?_ 2) <;> linarith
    · suffices StrictMonoOn g (Set.Ici 0) from
        (this.lt_iff_lt (by simp) (by simpa using hx.le)).mpr hx
      refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) ?_
        (fun x hx ↦ (hg_deriv x ?_).hasDerivWithinAt) fun x hx ↦ ?_
      · refine hg_cont.mono ?_
        simp [Set.Ici_subset_Ioi]
      · simp only [interior_Ici, Set.mem_Ioi] at hx
        linarith
      · simp only [interior_Ici, Set.mem_Ioi] at hx
        refine div_pos ?_ ?_
        · rw [sq_pos_iff, sub_ne_zero]
          refine ne_of_lt ?_
          refine (lt_sqrt one_pos.le).mpr ?_
          simpa using hx
        · suffices 0 < (1 + x) ^ (3 / 2 : ℝ) by simpa
          exact rpow_pos_of_pos (by linarith) _

  | inl hx =>
    suffices f x < f 0 ∧ g x < g 0 by simpa [f, g, abs_of_neg, hx, h_log_neg.mpr hx, neg_div]
    split_ands
    · suffices StrictMonoOn f (Set.Ioc (-1) 0) from
        (this.lt_iff_lt (by simpa using ⟨hx_gt, hx.le⟩) (by simp)).mpr hx
      refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioc (-1) 0) ?_
        (fun x hx ↦ (hf_deriv x ?_).hasDerivWithinAt) fun x hx ↦ ?_
      · exact hf_cont.mono Set.Ioc_subset_Ioi_self
      · simp only [interior_Ioc, Set.mem_Ioo] at hx
        linarith
      · simp only [interior_Ioc, Set.mem_Ioo] at hx
        refine div_pos (sq_pos_of_neg hx.2) ?_
        refine mul_pos ?_ (pow_pos ?_ 2) <;> linarith
    · suffices StrictMonoOn g (Set.Ioc (-1) 0) from
        (this.lt_iff_lt (by simpa using ⟨hx_gt, hx.le⟩) (by simp)).mpr hx
      refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioc (-1) 0) ?_
        (fun x hx ↦ (hg_deriv x ?_).hasDerivWithinAt) fun x hx ↦ ?_
      · exact hg_cont.mono Set.Ioc_subset_Ioi_self
      · simp only [interior_Ioc, Set.mem_Ioo] at hx
        linarith
      · simp only [interior_Ioc, Set.mem_Ioo] at hx
        refine div_pos ?_ ?_
        · rw [sq_pos_iff, sub_ne_zero]
          refine ne_of_gt ?_
          refine (sqrt_lt' one_pos).mpr ?_
          simpa using hx.2
        · suffices 0 < (1 + x) ^ (3 / 2 : ℝ) by simpa
          exact rpow_pos_of_pos (by linarith) _
