-- https://cloud.kili-technology.com/label/projects/label/cmb4vlozi000xwgay881ypcn9

import Mathlib

open Polynomial

/- Let the temperature $T$ of an object be a function of time $t$:
$T(t) = a t^3 + b t^2  + c t + d$ ($a \neq 0$)$, where the temperature is in
${ }^{\circ} \mathrm{C}$ and the time is in hours, with $t = 0$ representing 12:00, and
positive $t$ values representing times after 12:00.
If the temperature of the object is measured to be $8^{\circ} \mathrm{C}$ at 8:00,
$60^{\circ} \mathrm{C}$ at 12:00, and $58^{\circ} \mathrm{C}$ at 13:00, and it is known that the
rate of change of the object's temperature at 8:00 and 16:00 is the same.
(1) Write the function relating the object's temperature $T$ to time $t$;
(2) At what time between 10:00 and 14:00 (inclusive) is the temperature of the object the highest?
And find the highest temperature. -/

theorem algebra_111609 {a b c d : ℝ} (ha : a ≠ 0)
    (f : ℝ[X]) (hf : f = C a * X ^ 3 + C b * X ^ 2 + C c * X + C d)
    (hf_0800 : f.eval (-4) = 8) (hf_1200 : f.eval 0 = 60) (hf_1300 : f.eval 1 = 58)
    (hf_deriv_eq : f.derivative.eval (-4) = f.derivative.eval 4) :
    (a = 1 ∧ b = 0 ∧ c = -3 ∧ d = 60) ∧
    (∀ x ∈ Set.Icc (-2) 2, f.eval x ≤ 62) ∧
    {x ∈ Set.Icc (-2) 2 | f.eval x = 62} = {-1, 2} := by
  -- The constant term is determined from `t = 0`.
  have hd : d = 60 := by simpa [hf] using hf_1200
  -- The X ^ 2 and X ^ 0 terms in the derivative cancel for `t = -4` and `t = 4`.
  have hb : b = 0 := by simpa [hf, neg_eq_iff_add_eq_zero] using hf_deriv_eq
  -- Now we have two equations for `a` and `c`:
  -- `a + c = -2`
  -- `16 a + c = 13`
  -- The difference gives `15 a = 15`, hence `a = 1` and `c = -3`.
  have ⟨ha, hc⟩ : a = 1 ∧ c = -3 := by
    simp only [hf, hb, hd, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hf_0800 hf_1300
    constructor <;> nlinarith
  refine ⟨⟨ha, hb, hc, hd⟩, ?_⟩

  replace hf : f = X ^ 3 - C 3 * X + C 60 := by simpa [ha, hb, hc, hd] using hf
  -- The derivative of `x ^ 3 - 3 x + c` is is `3 (x ^ 2 - 1)`,
  -- which is zero at `x = -1` and `x = 1`, negative in `(-1, 1)`, positive elsewhere.
  have hf' : deriv f.eval = (C 3 * (X ^ 2 - C 1) : ℝ[X]).eval := by
    funext x
    simpa [hf, mul_sub] using f.deriv

  -- The second derivative is `6 x`, which is negative for `x < 0` and positive for `x > 0`.
  -- Therefore, we have a strictly concave function on `x < 0` with maximum at `x = -1`,
  -- and a strictly convex function on `0 < x`.
  -- The maximum is obtained at both `x = -1` and at the boundary `x = 2`.
  have hf'' : deriv^[2] f.eval = (C 6 * X : ℝ[X]).eval := by
    simp only [Function.iterate_succ, Function.comp_apply, hf']
    funext x
    suffices 3 * (2 * x) = 6 * x by simpa
    ring
  have h_concave : StrictConcaveOn ℝ (Set.Iic 0) f.eval := by
    refine strictConcaveOn_of_deriv2_neg (convex_Iic 0) f.continuousOn fun x hx ↦ ?_
    suffices 6 * x < 0 by simpa [hf'']
    suffices x < 0 by linarith
    simpa using hx
  have h_convex : StrictConvexOn ℝ (Set.Ici 0) f.eval := by
    refine strictConvexOn_of_deriv2_pos (convex_Ici 0) f.continuousOn ?_
    intro x hx
    simpa [hf''] using hx

  -- Obtain `IsMaxOn` for `-2 ≤ x ≤ 0`.
  -- This will be combined with strict concavity to obtain uniqueness of the maximum.
  have h_isMaxOn_neg_one : IsMaxOn f.eval (Set.Icc (-2) 0) (-1) := by
    suffices IsMaxOn f.eval (Set.Iic 0) (-1) from this.on_subset Set.Icc_subset_Iic_self
    refine IsMaxOn.of_isLocalMaxOn_of_concaveOn (by norm_num) ?_ h_concave.concaveOn
    refine IsLocalMax.on ?_ _
    refine isLocalMax_of_deriv_Ioo (a := -2) (b := -1) (c := 0) (by norm_num) (by norm_num)
      f.continuousAt f.differentiableOn f.differentiableOn ?_ ?_
    · intro x hx
      rw [hf']
      suffices 1 ≤ |x| by simpa
      rw [Set.mem_Ioo] at hx
      rw [le_abs']
      exact Or.inl (by linarith)
    · intro x hx
      rw [hf']
      suffices 3 * (x ^ 2 - 1) ≤ 0 by simpa
      refine mul_nonpos_of_nonneg_of_nonpos (by norm_num) ?_
      suffices |x| ≤ 1 by simpa
      rw [Set.mem_Ioo] at hx
      rw [abs_le]
      constructor <;> linarith

  -- It will be useful to split the interval.
  have h_union : Set.Icc (-2) 0 ∪ Set.Ioc 0 2 = (Set.Icc (-2) 2 : Set ℝ) :=
    Set.Icc_union_Ioc_eq_Icc (by simp) (by simp)

  refine ⟨?_, ?_⟩
  -- First show that the function is bounded above on the interval.
  · intro x hx
    -- Split into the two cases.
    rw [← h_union, Set.mem_union] at hx
    cases hx with
    | inl hx =>
      -- For `-2 ≤ x ≤ 0`, bound above by `f (-1)`.
      calc _
      _ ≤ f.eval (-1) := h_isMaxOn_neg_one hx
      _ = _ := by norm_num [hf]  -- TODO: this everywhere
    | inr hx =>
      -- For `0 < x ≤ 2`, bound above by `f 2`.
      calc _
      _ ≤ max (f.eval 0) (f.eval 2) :=
        h_convex.convexOn.le_max_of_mem_Icc (by simp) (by simp) (Set.mem_Icc_of_Ioc hx)
      _ = _ := by norm_num [hf]
  -- Then it remains to show that no other points obtain the maximum.
  · ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨hx, h⟩
      -- Show that each maximum is unique within its interval.
      rw [← h_union, Set.mem_union] at hx
      refine hx.imp ?_ ?_
      · intro hx
        -- Use strict concavity to obtain uniqueness of the maximizer.
        replace h_concave := h_concave.subset (Set.Icc_subset_Iic_self) (convex_Icc (-2) 0)
        refine h_concave.eq_of_isMaxOn ?_ h_isMaxOn_neg_one hx (by norm_num)
        intro a ha
        simp only [Set.mem_setOf_eq]
        calc _
        _ ≤ f.eval (-1) := h_isMaxOn_neg_one ha
        _ = 62 := by norm_num [hf]
        _ = _ := h.symm
      · -- Use strict convexity to show other points are strictly less than the max endpoint.
        suffices x ∉ Set.Ioo 0 2 by
          intro hx
          simpa using Set.mem_diff_of_mem hx this
        contrapose! h
        refine ne_of_lt ?_
        calc _
        _ < eval 0 f ⊔ eval 2 f :=
          h_convex.lt_on_openSegment (Set.left_mem_Ici) (by simp) (by simp) (by simpa using h)
        _ = 62 := by norm_num [hf]
    -- The reverse direction is simple evaluation.
    · intro hx
      refine hx.elim ?_ ?_
      · rintro rfl
        rw [hf]
        norm_num
      · rintro rfl
        rw [hf]
        norm_num
