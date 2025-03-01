-- https://cloud.kili-technology.com/label/projects/label/cm7eniew000gxzz87zqykno8f

import Mathlib

open Real

/- A geometric sequence (a_n) has a_1 = sin x, a_2 = cos x, a_3 = tan x for some real number x.
For what value of n does a_n = 1 + cos x?
(A) 4
(B) 5
(C) 6
(D) 7
(E) 8 -/

theorem algebra_94341 {x : ℝ} (a : ℕ → ℝ) {r : ℝ} (ha : ∀ n, a n = a 0 * r ^ n)
    (ha0 : a 0 = sin x) (ha1 : a 1 = cos x) (ha2 : a 2 = tan x)
    (h_cos : cos x ≠ 0) :
    a 7 = 1 + cos x := by
  -- Note: Include additional assumption that `cos x ≠ 0`.
  -- Normally we would be able to deduce this from `a 2 = tan x`, since `cos x = 0`
  -- would imply that the geometric sequence is (impossibly) `±1, 0, ±∞`.
  -- However, in Mathlib, `tan x = sin x / cos x` is equal to zero when `cos x = 0`.

  -- First show that sin x ≠ 0, otherwise the whole sequence is zero.
  have h_sin : sin x ≠ 0 := by
    have h := ha0 ▸ ha1.symm.trans (ha 1)
    contrapose! h
    cases sin_eq_zero_iff_cos_eq.mp h with
    | inl h' => simp [h, h']
    | inr h' => simp [h, h']
  -- Obtain r.
  have hr : r = cos x / sin x := by
    suffices r = a 1 / a 0 from ha0 ▸ ha1 ▸ this
    rw [ha 1, pow_one, ha0]
    exact (mul_div_cancel_left₀ _ h_sin).symm
  -- Extract information from the from the third term.
  -- a 2 = tan x
  -- sin x * (cos x / sin x) ^ 2 = sin x / cos x
  -- cos x ^ 3 = sin x ^ 2
  -- (Not true in general for all x.)
  have ha2' : cos x ^ 3 = sin x ^ 2 := by
    have := ha0 ▸ hr ▸ (ha 2).symm.trans ha2
    rw [tan_eq_sin_div_cos, div_pow, mul_div, div_eq_div_iff (pow_ne_zero 2 h_sin) h_cos,
      mul_assoc, mul_eq_mul_left_iff] at this
    cases this with
    | inl h => exact h
    | inr h => contradiction
  -- Right hand side must be a single term of powers of sin and cos.
  -- Start with the identity cos ^ 2 + sin ^ 2 = 1.
  -- cos x ^ 2 + cos x ^ 3 = 1
  -- cos x ^ 2 * (1 + cos x) = 1
  -- 1 + cos x = 1 / cos x ^ 2
  calc _
  _ = sin x * (cos x / sin x) ^ 7 := by rw [ha, ha0, hr]
  _ = cos x ^ 7 / sin x ^ 6 := by
    rw [mul_comm, div_pow, div_mul]
    congr
    exact div_eq_of_eq_mul h_sin rfl
  _ = (cos x ^ 3 / sin x ^ 2) ^ 3 * (1 / cos x ^ 2) := by
    rw [div_pow, div_mul_div_comm]
    simp only [← pow_mul, Nat.reduceMul]
    refine (div_eq_div_iff ?_ ?_).mpr ?_
    · exact pow_ne_zero 6 h_sin
    · exact mul_ne_zero (pow_ne_zero 6 h_sin) (pow_ne_zero 2 h_cos)
    ring
  _ = 1 / cos x ^ 2 := by
    refine mul_left_eq_self₀.mpr (.inl ?_)
    rw [ha2']
    rw [div_self (pow_ne_zero 2 h_sin)]
    simp only [one_pow]
  _ = 1 + cos x := by
    rw [div_eq_iff (pow_ne_zero 2 h_cos)]
    refine (cos_sq_add_sin_sq x).symm.trans ?_
    rw [add_mul]
    congr
    · simp
    · rw [← ha2']
      ring
