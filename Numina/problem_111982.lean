-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi3000o4nayo056dpb8

import Mathlib

open Real

/- Let the function $f : \mathbb{R} \rightarrow \mathbb{R}, f(x) = x + \log_{3}(1+3^{x})$.
Show that:
a) The function $f$ is invertible and $f^{-1}(x) < f(x)$
b) $f(n) ∈ \mathbb{R} \setminus \mathbb{Q}$ for all $n \in \mathbb{N}^{*}$. -/

theorem calculus_111982 (f : ℝ → ℝ) (hf : ∀ x, f x = x + logb 3 (1 + 3 ^ x)) :
    (∃ g : ℝ → ℝ, (g.LeftInverse f ∧ g.RightInverse f) ∧ ∀ x, g x < f x) ∧
    ∀ n : ℕ, n ≠ 0 → Irrational (f n) := by
  constructor
  · -- Find `g` such that `f x = y ↔ g y = x`:
    -- y = f x = x + log_3 (1 + 3^x)
    -- 3^y = (3^x)^2 + (3^x)
    -- 0 = (3^x)^2 + (3^x) - 3^y where 0 < 3^x, 3^y
    -- 3^x = (-1 ± √(1 + 4 * 3^y)) / 2
    -- x = log_3 (√(1 + 4 * 3^y) - 1) - log_3 2 = g x
    let g : ℝ → ℝ := fun y ↦ logb 3 ((√(4 * 3^y + 1) - 1) / 2)
    use g
    have h_inv (x y : ℝ) : f x = y ↔ g y = x := by
      rw [hf]
      unfold g
      calc x + logb 3 (1 + 3 ^ x) = y
      _ ↔ y = x + logb 3 (1 + 3 ^ x) := eq_comm
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

    have h_leftInv : g.LeftInverse f := fun x ↦ (h_inv x (f x)).mp rfl
    have h_rightInv : g.RightInverse f := fun y ↦ (h_inv (g y) y).mpr rfl
    refine ⟨⟨h_leftInv, h_rightInv⟩, ?_⟩
    -- The inverse function is a reflection about y = x.
    -- Therefore, x < f x implies g x < x < f x.
    suffices ∀ x, x < f x by
      intro x
      calc _
      _ < f (g x) := this (g x)
      _ = x := h_rightInv x
      _ < _ := this x
    intro x
    rw [hf, lt_add_iff_pos_right]
    refine logb_pos (by norm_num) ?_
    rw [lt_add_iff_pos_right]
    exact rpow_pos_of_pos three_pos x

  · -- Prove that `f n` is irrational for `n` a positive natural number.
    intro n hn
    suffices Irrational (logb 3 (1 + 3 ^ n)) by simpa [hf] using this
    suffices ∀ (q : ℚ), ↑q ≠ logb 3 (1 + 3 ^ n) by simpa [Irrational] using this
    intro q hq
    -- Need to find a contradiction in:
    --   a / b = log_3 (1 + 3 ^ n)
    --   3 ^ (a / b) = 1 + 3 ^ n
    --   3 ^ a = (1 + 3 ^ n) ^ b
    -- This is not possible, since 3 divides the left but not the right.
    -- We will need to establish that `a` is positive; follows from `q` being positive.
    have hq_pos : 0 < q := by
      suffices 0 < (q : ℝ) from Rat.cast_pos.mp this
      rw [hq]
      exact logb_pos (by norm_num) (by simp)
    -- Establish contradiction given the equality.
    suffices 3 ^ q.num.natAbs = (1 + 3 ^ n) ^ q.den by
      -- Start from `3 ∣ 3 ^ n` and `¬3 ∣ 1`.
      suffices 3 ∣ (1 + 3 ^ n) by
        simpa using (Nat.dvd_add_iff_left (dvd_pow_self 3 hn)).mpr this
      suffices 3 ∣ (1 + 3 ^ n) ^ q.den from Nat.prime_three.dvd_of_dvd_pow this
      rw [← this]
      refine dvd_pow_self 3 ?_
      simpa using hq_pos.ne'
    -- Now establish the equality.
    -- Move from `ℕ` back to `ℝ` to use `logb`.
    suffices ((3 ^ q.num.natAbs : ℕ) : ℝ) = ↑((1 + 3 ^ n) ^ q.den : ℕ) from Nat.cast_inj.mp this
    -- Take power of `1 / q.den` on both sides.
    suffices (3 : ℝ) ^ (q.num.natAbs / q.den * q.den : ℝ) = (1 + 3 ^ n) ^ (q.den : ℝ) by
      simpa using this
    rw [rpow_mul three_pos.le]
    congr
    -- Compare to condition from `logb`.
    convert (logb_eq_iff_rpow_eq three_pos (by norm_num) ?_).mp hq.symm
    rotate_left
    · refine add_pos ?_ ?_ <;> simp
    -- Move back to `ℚ` and compare to `q.num / q.den`.
    suffices q.num.natAbs / q.den = q by simpa using congrArg (Rat.cast : ℚ → ℝ) this
    convert Rat.num_div_den q
    suffices q.num.natAbs = q.num from congrArg (Int.cast : ℤ → ℚ) this
    simpa using hq_pos.le
