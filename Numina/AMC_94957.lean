-- https://cloud.kili-technology.com/label/projects/label/cm84mq01l023oiev540fv5klg
-- https://artofproblemsolving.com/wiki/index.php/2021_Fall_AMC_12B_Problems/Problem_21

import Mathlib

open scoped Real
open Complex

/- For real numbers $x$, let
$$
P(x) = 1 + \cos(x) + i \sin(x) - \cos(2 x) - i \ sin(2 x) + \cos(3 x) + i \sin(3 x)
$$
where $i = \sqrt{-1}$. For how many values of $x$ with $0 \leq x < 2 \pi$ does $P(x) = 0$?
(A) 0
(B) 1
(C) 2
(D) 3
(E) 4 -/

theorem algebra_94957 {p : ℝ → ℂ}
    (hp : ∀ x, p x = 1 + cos x + I * sin x - cos (2 * x) - I * sin (2 * x) +
      cos (3 * x) + I * sin (3 * x)) :
    {x | 0 ≤ x ∧ x < 2 * π ∧ p x = 0}.encard = 0 := by
  suffices ∀ x, p x ≠ 0 by simp [this]
  intro x

  -- Rewrite as intersection of a complex cubic with the unit circle.
  suffices ∀ a, abs a = 1 → 1 + a - a ^ 2 + a ^ 3 ≠ 0 from
    calc _
    _ = 1 + exp (x * I) - exp (2 * x * I) + exp (3 * x * I) := by
      simp only [hp, exp_mul_I]
      ring
    _ = 1 + exp (x * I) - exp (x * I) ^ 2 + exp (x * I) ^ 3 := by
      simp [← exp_nat_mul, mul_assoc]
    _ ≠ 0 := this (cexp (x * I)) (abs_exp_ofReal_mul_I x)
  intro a ha

  -- Note that we can re-write `a^3 + a = a^2 (a + a⁻¹)` with `a + a⁻¹ = 2 * a.re` for `|a| = 1`.
  -- This means that we have `r • a ^ 2 = -1` with `r = 2 * a.re - 1` real.
  intro h
  obtain ⟨r, hra⟩ : ∃ r : ℝ, r • a ^ 2 = -1 := by
    use 2 * a.re - 1
    suffices 1 + (2 * a.re - 1) • a ^ 2 = 0 from (neg_eq_of_add_eq_zero_right this).symm
    calc _
    _ = 1 + a ^ 2 * (a + a⁻¹ - 1) := by
      suffices a + a⁻¹ = 2 * a.re by simp [this, mul_comm (a ^ 2)]
      -- Use `a⁻¹ = conj a / |a| ^ 2` and `|a| = 1`.
      calc _
      _ = a + starRingEnd ℂ a := by
        rw [inv_def]
        simp [normSq_eq_abs, ha]
      _ = _ := by simp [add_conj]
    -- Expand the factored expression.
    _ = 1 + (a ^ 3 + a - a ^ 2) := by simp [mul_sub, mul_add, pow_succ]
    _ = 1 + a - a ^ 2 + a ^ 3 := by ring
    _ = 0 := h

  -- Since `a` has norm 1 and `|r| |a|^2 = 1`, we have `r = 1` or `r = -1`.
  have hr : r = 1 ∨ r = -1 := by
    refine eq_or_eq_neg_of_abs_eq ?_
    simpa [ha] using congrArg abs hra

  -- Having derived this constraint on `a ^ 2`, we restore the negative goal.
  -- Collect terms of `a ^ 2` to simplify the solution.
  suffices 1 + a * (a ^ 2 + 1) - a ^ 2 ≠ 0 from this (.trans (by ring) h)
  cases hr with
  | inl hr =>
    have ha_eq : a ^ 2 = -1 := by simpa [hr] using hra
    simp [ha_eq]
  | inr hr =>
    have ha_eq : a ^ 2 = 1 := by simpa [hr] using hra
    suffices ‖a‖ ≠ 0 by simpa [ha_eq] using this
    simp [ha]
