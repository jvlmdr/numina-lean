-- https://cloud.kili-technology.com/label/projects/label/cmcbouv7300miueaxn5qat9z9

import Mathlib

/- Let $a, b, c \in [0,1]$. Show that:
$$
\frac{a}{b+c+1} + \frac{b}{c+a+1} + \frac{c}{a+b+1} + (1-a)(1-b)(1-c) \leqslant 1
$$
-/

-- The function `1 / x` is strictly convex on `0 < x`.
lemma strictConvexOn_inv : StrictConvexOn ℝ (Set.Ioi 0) fun x : ℝ ↦ x⁻¹ :=
  strictConvexOn_of_deriv2_pos (convex_Ioi 0) (continuousOn_inv₀.mono <| by simp) fun x hx ↦ by
    simp only [interior_Ioi, Set.mem_Ioi] at hx
    simpa [Finset.range_succ] using pow_pos hx 3

-- The function `1 / x` is convex on `0 < x`.
lemma convexOn_inv : ConvexOn ℝ (Set.Ioi 0) fun x : ℝ ↦ x⁻¹ := strictConvexOn_inv.convexOn

theorem inequalities_102449 (a b c : ℝ)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    a / (b + c + 1) + b / (c + a + 1) + c / (a + b + 1) + (1 - a) * (1 - b) * (1 - c) ≤ 1 := by
  -- Define the left-hand side as a symmetric function `f` of three variables.
  let f (a b c : ℝ) : ℝ :=
    a / (b + c + 1) + b / (c + a + 1) + c / (a + b + 1) + (1 - a) * (1 - b) * (1 - c)
  change f a b c ≤ 1
  -- Obtain a proof of the symmetry.
  have hf_rotate (x y z) : f x y z = f y z x := by ring

  -- We will show that the function is convex in each variable, and hence attains its maximum
  -- at the endpoints of the interval [0, 1].
  -- First define a function `g` to represent the terms `b / (c + a + 1)` and `c / (a + b + 1)`.
  let g (a b c : ℝ) : ℝ := b / (1 + c + a)
  have hg_convex (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) :
      ConvexOn ℝ (Set.Icc 0 1) fun a : ℝ ↦ g a b c := by
    suffices ConvexOn ℝ (Set.Icc 0 1) fun a : ℝ ↦ b • (1 + c + a)⁻¹ by simpa [div_eq_mul_inv]
    refine .smul (by linarith) ?_
    refine .subset (convexOn_inv.comp_affineMap (.const ℝ ℝ (1 + c) + .id ℝ ℝ)) ?_ (convex_Icc 0 1)
    intro x hx
    simp only [Set.mem_Icc] at hx
    suffices 0 < 1 + c + x by simpa
    linarith
  -- Now show that `f` is convex with respect to the first variable.
  have hf_convex (b c : ℝ) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
      ConvexOn ℝ (Set.Icc 0 1) fun a : ℝ ↦ f a b c := by
    simp only [Set.mem_Icc] at hb hc
    unfold f
    refine .add ?_ ?_
    · refine .add (.add ?_ ?_) ?_
      · suffices ConvexOn ℝ (Set.Icc 0 1) fun a : ℝ ↦ (b + c + 1)⁻¹ • a by simpa [inv_mul_eq_div]
        refine .smul ?_ (convexOn_id (convex_Icc 0 1))
        rw [inv_nonneg]
        linarith
      · convert hg_convex b c hb.1 hc.1 using 2
        ring
      · convert hg_convex c b hc.1 hb.1 using 2
        ring
    · suffices ConvexOn ℝ (Set.Icc 0 1) fun a : ℝ ↦ ((1 - b) * (1 - c)) • (1 - a) by
        simpa [mul_rotate]
      refine .smul ?_ ?_
      · refine mul_nonneg ?_ ?_ <;> linarith
      · suffices ConvexOn ℝ (Set.Icc 0 1) fun a : ℝ ↦ -a + 1 by simpa [neg_add_eq_sub]
        refine .add_const ?_ _
        exact (concaveOn_id (convex_Icc 0 1)).neg

  -- For any `b, c`, the function `f a b c` obtain its maximum at either `a = 0` or `a = 1`.
  have hf_le (a b c : ℝ) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
      f a b c ≤ f 0 b c ⊔ f 1 b c :=
    (hf_convex b c hb hc).le_max_of_mem_Icc (by simp) (by simp) ha

  calc _
  _ ≤ f 0 b c ⊔ f 1 b c := hf_le a b c ha hb hc
  _ = f b c 0 ⊔ f b c 1 := by simp [← hf_rotate _ b c]
  _ ≤ (f 0 c 0 ⊔ f 1 c 0) ⊔ (f 0 c 1 ⊔ f 1 c 1) := by
    refine sup_le_sup ?_ ?_ <;> simp [hf_le, hb, hc]
  _ = (f c 0 0 ⊔ f c 0 1) ⊔ (f c 1 0 ⊔ f c 1 1) := by simp [← hf_rotate _ c]
  _ ≤ ((f 0 0 0 ⊔ f 1 0 0) ⊔ (f 0 0 1 ⊔ f 1 0 1)) ⊔
      ((f 0 1 0 ⊔ f 1 1 0) ⊔ (f 0 1 1 ⊔ f 1 1 1)) := by
    refine sup_le_sup (sup_le_sup ?_ ?_) (sup_le_sup ?_ ?_) <;> simp [hf_le, hc]
  _ = f 0 0 0 := by norm_num
  _ = _ := by simp [f]
