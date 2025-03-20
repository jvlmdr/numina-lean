-- https://cloud.kili-technology.com/label/projects/label/cm8ct07ju02725kaygbcpergf

import Mathlib

open Real

/- Given $f(x) = \cos 2 x + p |\cos x| + p, x \in \mathbb{R}$.
Let the maximum value of $f(x)$ be $h(p)$, then the expression for $h(p)$ is
$$ h(p) = \begin{cases} p - 1, & p < -2 \\ 2 p + 1, & p \ge 2. \end{cases} $$
-/
theorem algebra_114412 {f : ℝ → ℝ → ℝ} (hf : ∀ p x, f p x = cos (2 * x) + p * |cos x| + p)
    (g : ℝ → ℝ) (hg : ∀ p, g p = ⨆ x, f p x) :
    ∀ p, g p = if p < -2 then p - 1 else 2 * p + 1 := by
  intro p
  rw [hg]

  -- Suffices to consider one period of size `π`.
  -- Could eliminate half a period using `(f p).Even`.
  -- However, this complicates the proof and doesn't help with our approach.
  have hf_periodic : (f p).Periodic π := fun x ↦ by simp [hf, mul_add]
  -- Use the interval `[-π / 2, π / 2]` as this is the range on which `0 ≤ cos x`.
  suffices sSup (f p '' Set.Icc (-π / 2) (π / 2)) = if p < -2 then p - 1 else 2 * p + 1 by
    rw [← sSup_range, ← hf_periodic.image_Icc pi_pos (-π / 2)]
    convert this using 4
    ring

  -- Since `cos 2 x = 2 |cos x|² - 1`, we can rewrite `f` as a function of `|cos x|`.
  have hf_comp : f p = (fun c ↦ 2 * c ^ 2 + p * c + p - 1) ∘ (|cos ·|) := by
    funext x
    simp only [Function.comp_apply, hf, cos_two_mul, sq_abs]
    ring
  -- Furthermore, the function `x ↦ |cos x|` maps the interval `[-π / 2, π / 2]` to `[0, 1]`.
  have h_image : (|cos ·|) '' Set.Icc (-π / 2) (π / 2) = Set.Icc 0 1 := by
    ext c
    simp only [Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨x, _, hc⟩
      simpa [← hc] using abs_cos_le_one x
    · intro hc
      refine ⟨arccos c, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · refine le_trans ?_ (arccos_nonneg c)
          have _ := pi_nonneg
          linarith
        · exact arccos_le_pi_div_two.mpr hc.1
      · rw [Real.cos_arccos (by linarith) hc.2]
        exact abs_of_nonneg hc.1

  -- Since `f p x` is convex as a function of `|cos x|`, its max is attained at the boundary.
  have h_sSup_convexOn_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ConvexOn ℝ (Set.Icc a b) f) :
      sSup (f '' Set.Icc a b) = f a ⊔ f b := by
    rw [sSup_image']
    have : Nonempty (Set.Icc a b) := Set.nonempty_Icc_subtype hab
    have ha : a ∈ Set.Icc a b := ⟨le_refl a, hab⟩
    have hb : b ∈ Set.Icc a b := ⟨hab, le_refl b⟩
    refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
    · refine Subtype.forall.mpr fun x hx ↦ ?_
      exact hf.le_max_of_mem_Icc ha hb hx
    · intro y hy
      -- If `f a < f b` then the max is attained at `x = b`.
      cases lt_or_le (f a) (f b) with
      | inl h => use ⟨b, hb⟩, hy.trans_eq (sup_eq_right.mpr h.le)
      | inr h => use ⟨a, ha⟩, hy.trans_eq (sup_eq_left.mpr h)
  -- Prove that the quadratic function is convex from its second derivative.
  have h_convex : ConvexOn ℝ Set.univ (fun c ↦ 2 * c ^ 2 + p * c + p - 1) := by
    -- Establish the form of the derivative.
    have h_hasDerivAt (c) : HasDerivAt (fun c ↦ 2 * c ^ 2 + p * c + p - 1) (4 * c + p) c := by
      convert ((hasDerivAt_pow 2 c).const_mul 2).add <| ((hasDerivAt_id' c).const_mul p).add <|
          hasDerivAt_const c (p - 1) using 2 <;> ring
    have h_deriv := funext fun c ↦ (h_hasDerivAt c).deriv
    -- Prove convex using second derivative nonnegative.
    refine convexOn_univ_of_deriv2_nonneg ?_ ?_ ?_
    · exact fun c ↦ (h_hasDerivAt c).differentiableAt
    · rw [h_deriv]
      exact (differentiable_id'.const_mul 4).add_const p
    · intro c
      rw [Function.iterate_succ, Function.comp_apply, h_deriv, Function.iterate_one]
      rw [deriv_add_const, deriv_const_mul 4 differentiableAt_id']
      simp

  -- Put it all together.
  rw [hf_comp, Set.image_comp, h_image]
  rw [h_sSup_convexOn_Icc zero_le_one (h_convex.subset (Set.subset_univ _) (convex_Icc 0 1))]
  calc _
  -- Simplify the expressions.
  _ = (p - 1) ⊔ (2 * p + 1) := by congr 1 <;> ring
  -- Now it remains to show that `p < -2` is the condition that determines which is larger.
  _ = if p < -2 then p - 1 else 2 * p + 1 := by
    have hp_lt_iff : 2 * p + 1 < p - 1 ↔ p < -2 := by
      rw [← lt_sub_iff_add_lt, sub_sub]
      rw [two_mul, sub_eq_add_neg, _root_.add_lt_add_iff_left]
      norm_num
    simp only [← hp_lt_iff]
    symm
    refine ite_eq_iff'.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · simpa using h.le
    · simpa using h
