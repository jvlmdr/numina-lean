-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi3000o4nayo056dpb8

import Mathlib

open Real

/- Let the function $f : \mathbb{R} \rightarrow \mathbb{R}, f(x) = x + \log_{3}(1+3^{x})$.
Show that:
a) The function $f$ is invertible and $f^{-1}(x) < f(x)$
b) $f(n) ∈ \mathbb{R} \setminus \mathbb{Q}$ for all $n \in \mathbb{N}^{*}$. -/

theorem calculus_111982 (f : ℝ → ℝ) (hf : ∀ x, f x = x + logb 3 (1 + 3 ^ x)) :
    (∃ g : ℝ → ℝ, (g.LeftInverse f ∧ g.RightInverse f) ∧ ∀ x, g x < f x) ∧
    ∀ n, 0 < n → ¬∃ q : ℚ, f n = q := by

  -- y = f x = x + log_3 (1 + 3^x)
  -- 3^y = (3^x)^2 + (3^x)
  -- 0 = (3^x)^2 + (3^x) - 3^y where 0 < 3^x, 3^y.
  -- 3^x = (-1 ± √(1 + 4 * 3^y)) / 2
  -- x = log_3 (√(1 + 4 * 3^y) - 1) - log_3 2
  constructor
  · -- use fun y ↦ logb 3 ((-1 + √(1 + 4 * 3^y)) / 2)
    let g : ℝ → ℝ := fun y ↦ logb 3 ((√(4 * 3^y + 1) - 1) / 2)
    -- let g : ℝ → ℝ := fun y ↦ logb 3 (√(3 ^ y + 4⁻¹ : ℝ) - 2⁻¹)
    have h_inv (x y : ℝ) : y = f x ↔ x = g y := by
      rw [hf]
      unfold g
      calc y = x + logb 3 (1 + 3 ^ x)
      _ ↔ (3 ^ y : ℝ) = 3 ^ (x + logb 3 (1 + 3 ^ x)) :=
        (strictMono_rpow_of_base_gt_one (by norm_num)).injective.eq_iff.symm
      _ ↔ (3 ^ y : ℝ) = 3 ^ x * (1 + 3 ^ x) := by
        refine Eq.congr_right ?_
        rw [rpow_add three_pos, rpow_logb three_pos (by norm_num)]
        refine add_pos_of_pos_of_nonneg one_pos ?_
        exact rpow_nonneg (by norm_num) x
      _ ↔ (3 ^ y : ℝ) = (3 ^ x + 2⁻¹) ^ 2 - 4⁻¹ := by
        refine Eq.congr_right ?_
        ring
      _ ↔ (3 ^ y + 4⁻¹ : ℝ) = (3 ^ x + 2⁻¹) ^ 2 := eq_sub_iff_add_eq
      _ ↔ √(3 ^ y + 4⁻¹ : ℝ) = √((3 ^ x + 2⁻¹) ^ 2) := by
        symm
        refine sqrt_inj ?_ (sq_nonneg _)
        refine add_nonneg (rpow_nonneg ?_ y) ?_ <;> norm_num
      _ ↔ √(3 ^ y + 4⁻¹ : ℝ) = 3 ^ x + 2⁻¹ := by
        refine Eq.congr_right ?_
        refine sqrt_sq ?_
        refine add_nonneg (rpow_nonneg ?_ x) ?_ <;> norm_num
      _ ↔ √(3 ^ y + 4⁻¹) - 2⁻¹ = (3 ^ x : ℝ) := sub_eq_iff_eq_add.symm
      _ ↔ 2⁻¹ * (√(4 * 3 ^ y + 1) - 1) = (3 ^ x : ℝ) := by
        refine Eq.congr_left ?_
        simp only [mul_sub, mul_one]
        congr
        calc _
        _ = √(2⁻¹ ^ 2 * (4 * 3 ^ y + 1)) := congrArg sqrt (by ring)
        _ = _ := by simp

      _ ↔ (√(4 * 3 ^ y + 1) - 1) / 2 = (3 ^ x : ℝ) := by rw [inv_mul_eq_div]
      _ ↔ (3 ^ x : ℝ) = (√(4 * 3 ^ y + 1) - 1) / 2 := eq_comm
      _ ↔ logb 3 ((√(4 * 3 ^ y + 1) - 1) / 2) = x := by
        symm
        refine logb_eq_iff_rpow_eq three_pos (by norm_num) ?_
        suffices √1 < √(4 * 3 ^ y + 1) by simpa using this
        refine sqrt_lt_sqrt one_pos.le ?_
        simpa using rpow_pos_of_pos three_pos y

      -- _ ↔ 3 ^ x = √(3 ^ y + 4⁻¹ : ℝ) - 2⁻¹ := eq_comm
      -- _ ↔ logb 3 (√(3 ^ y + 4⁻¹ : ℝ) - 2⁻¹) = x := by
      --   symm
      --   refine logb_eq_iff_rpow_eq three_pos (by norm_num) ?_
      --   rw [sub_pos, lt_sqrt (by norm_num)]
      --   convert lt_add_of_pos_left 4⁻¹ (rpow_pos_of_pos three_pos y)
      --   norm_num
      -- _ ↔ _ := eq_comm

      _ ↔ _ := eq_comm

    use g
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact fun x ↦ .symm <| (h_inv x _).mp rfl
    · exact fun y ↦ .symm <| (h_inv _ y).mpr rfl
    · suffices hg_mono : StrictMono g by
        suffices ∀ x, x < f x by
          intro x
          calc _
          _ < g (f x) := hg_mono (this x)
          _ = x := ((h_inv x _).mp rfl).symm
          _ < _ := this x
        intro x
        rw [hf, lt_add_iff_pos_right]
        refine logb_pos (by norm_num) ?_
        rw [lt_add_iff_pos_right]
        exact rpow_pos_of_pos three_pos x
      unfold g
      intro a b hab
      refine logb_lt_logb (by norm_num) ?_ ?_
      · suffices √1 < √(4 * 3 ^ a + 1) by simpa using this
        refine sqrt_lt_sqrt one_pos.le ?_
        simpa using rpow_pos_of_pos three_pos a
      refine div_lt_div_of_pos_right ?_ two_pos
      rw [sub_lt_sub_iff_right]
      refine sqrt_lt_sqrt ?_ ?_
      · refine add_nonneg ?_ zero_le_one
        simpa using rpow_nonneg three_pos.le a
      simpa using hab

  · sorry
