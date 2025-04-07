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

  -- Rewrite as intersection of complex cubic with unit circle.
  suffices ∀ a : ℂ, ‖a‖ = 1 → 1 + a - a ^ 2 + a ^ 3 ≠ 0 from
    calc _
    _ = 1 + exp (x * I) - exp (2 * x * I) + exp (3 * x * I) := by
      simp only [hp, exp_mul_I]
      ring
    _ = 1 + exp (x * I) - exp (x * I) ^ 2 + exp (x * I) ^ 3 := by
      simp [← exp_nat_mul, mul_assoc]
    _ ≠ 0 := this (cexp (x * I)) (norm_exp_ofReal_mul_I x)
  intro a ha

  intro h

  have h_alt : 1 - a ^ 2 + a * (a ^ 2 + 1) = 0 := .trans (by ring) h
  revert h_alt
  simp only [imp_false]

  have h : 1 + a ^ 2 * (a + a⁻¹ - 1) = 0 :=
    calc _
    _ = 1 + (a ^ 3 + a - a ^ 2) := by
      rw [mul_sub, mul_add, mul_one]
      congr
      simp [sq]
    _ = 1 + a - a ^ 2 + a ^ 3 := by ring
    _ = 0 := h

  have h_re : (a + a⁻¹) = 2 * a.re :=
    calc _
    _ = a + starRingEnd ℂ a := by simp [inv_def, Complex.normSq_eq_norm_sq, ha]
    _ = _ := by simp [Complex.add_conj]

  have h : ∃ r : ℝ, 1 + a ^ 2 * r = 0 := by
    use 2 * a.re - 1
    calc _
    _ = 1 + a ^ 2 * (a + a⁻¹ - 1) := by simp [h_re]
    _ = _ := h

  have h : ∃ r : ℝ, r • a ^ 2 = -1 := by
    simp
    refine h.imp fun r hr ↦ ?_
    suffices r * a ^ 2 + 1 = 0 from (neg_eq_of_add_eq_zero_left this).symm
    convert hr using 1
    ring

  rcases h with ⟨r, h⟩

  have : r = 1 ∨ r = -1 := by
    simp [norm_eq_abs] at ha  -- TODO: Revise!
    refine eq_or_eq_neg_of_abs_eq ?_
    simpa [ha] using congrArg (‖·‖) h

  cases this with
  | inl hr =>
    simp [hr] at h
    simp [h]
  | inr hr =>
    rw [hr] at h
    simp only [neg_smul, one_smul, neg_inj] at h
    simp [h]

    suffices ‖a‖ ≠ 0 by simpa using this
    simp [ha]
