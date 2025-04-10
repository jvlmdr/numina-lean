-- https://cloud.kili-technology.com/label/projects/label/cm91j40co0088seayzby00k9l

import Mathlib

/- Given the sequence $\{a_{n}\}$ satisfies $3 a_{n+1} + a_{n} = 4$ ($n \geqslant 1$) and
$a_{1} = 9$, with the sum of its first $n$ terms being $S_{n}$, then the smallest integer $n$
that satisfies the inequality $|S_{n} - n - 6\| < \frac{1}{125}$ is what? -/

theorem algebra_287054 {a : ℕ → ℝ} (ha : ∀ n, 3 * a (n + 1) + a n = 4) (ha1 : a 0 = 9) :
    IsLeast {n | |∑ k in Finset.range n, a k - n - 6| < 125⁻¹} 7 := by

  -- We have a geometric recursion for the sequence `fun n ↦ (a n) - 1`.
  have ha' (n) : 3 * (a (n + 1) - 1) = -(a n - 1) := by
    suffices 3 * a (n + 1) - 3 = 1 - a n by simpa [mul_sub] using this
    rw [sub_eq_sub_iff_add_eq_add]
    convert ha n
    norm_num
  -- Establish an explicit form for `(a n) - 1`.
  have ha_geo (n : ℕ) : a n - 1 = 8 * (-3⁻¹) ^ n := by
    induction n with
    | zero =>
      rw [ha1]
      norm_num
    | succ n IH =>
      -- Expand `(-3⁻¹) ^ (n + 1)` and introduce the inductive hypothesis.
      rw [pow_succ, ← mul_assoc, ← IH]
      refine (mul_right_inj' three_ne_zero).mp ?_
      convert ha' n using 1
      ring

  -- Obtain a closed form expression for the sum of the first `n` terms.
  have hs (n) : ∑ k in Finset.range n, a k - n = 6 * (1 - (-3⁻¹) ^ n) := by
    calc _
    _ = ∑ k in Finset.range n, (a k - 1) := by simp [Finset.sum_sub_distrib]
    _ = 8 * ∑ k in Finset.range n, (-3⁻¹) ^ k := by simp [ha_geo, Finset.mul_sum]
    _ = _ := by
      rw [geom_sum_eq (by norm_num)]
      ring

  -- Prove that the condition is equivalent to `7 ≤ n`.
  convert isLeast_Ici
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  calc _
  _ ↔ 6 * (3 ^ n)⁻¹ < (125⁻¹ : ℝ) := by simp [hs, mul_sub, abs_mul, abs_inv]
  _ ↔ (750 : ℝ) < 3 ^ n := by
    rw [mul_inv_lt_iff₀ (pow_pos three_pos n)]
    rw [lt_inv_mul_iff₀ (by norm_num)]
    norm_num
  _ ↔ ((750 : ℕ) : ℝ) < ((3 ^ n : ℕ) : ℝ) := by simp
  _ ↔ 750 < 3 ^ n := Nat.cast_lt
  _ ↔ 6 < n := by
    rw [Nat.lt_pow_iff_log_lt (by norm_num) (by norm_num)]
    simp [Nat.log]
