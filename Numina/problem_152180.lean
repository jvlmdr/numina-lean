-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9y0018ueaxg313m0vl

import Mathlib

open Complex Finset
open scoped Real

/- Simplify: $C_{n}^{0} \sin \alpha - C_{n}^{1} \sin (\alpha + \theta) + \cdots +
  (-1)^{n} C_{n}^{n} \sin (\alpha+n \theta)$. -/

-- Copied from newer version of Mathlib.
lemma Complex.exp_neg_pi_div_two_mul_I : exp (-π / 2 * I) = -I := by
  rw [← cos_add_sin_I, neg_div, cos_neg, cos_pi_div_two, sin_neg, sin_pi_div_two, zero_add, neg_mul,
    one_mul]

-- Rewrite the subtraction as a product using a complex exponential.
-- Use double-angle identities and take out `sin (θ / 2)` as common factor.
lemma lemma_1 (θ : ℂ) : 1 - cexp (θ * I) = -2 * sin (θ / 2) * I * cexp (θ / 2 * I) :=
  calc _
  _ = 1 - cos θ - sin θ * I := by
    rw [exp_mul_I]
    ring
  _ = 1 - cos (2 * (θ / 2)) - sin (2 * (θ / 2)) * I := by congr <;> ring
  _ = 2 * sin (θ / 2) ^ 2 - 2 * sin (θ / 2) * cos (θ / 2) * I := by
    congr 1
    · rw [cos_two_mul, sin_sq]
      ring
    · rw [sin_two_mul]
  _ = 2 * sin (θ / 2) * (sin (θ / 2) - cos (θ / 2) * I) := by ring
  _ = 2 * sin (θ / 2) * (sin (θ / 2) * ((-I) * I) - cos (θ / 2) * I) := by simp
  _ = _ := by
    rw [exp_mul_I]
    ring

-- Recognize the sum as a binomial expansion of `(1 - cexp (θ * I)) ^ n`.
-- Use the above lemma to rewrite the base.
lemma lemma_2 (n : ℕ) (α θ : ℂ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * n.choose k * cexp ((α + k * θ) * I) =
      2 ^ n * sin (θ / 2) ^ n * cexp ((α + n * (θ - π) / 2) * I) :=
  calc _
  _ = ∑ k ∈ range (n + 1), (-1) ^ k * n.choose k * cexp (α * I) * cexp (θ * I) ^ k := by
    simp [add_mul, exp_add, mul_assoc, exp_nat_mul]
  _ = cexp (α * I) * (-cexp (θ * I) + 1) ^ n := by
    rw [add_pow, mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    ring
  _ = cexp (α * I) * (1 - cexp (θ * I)) ^ n := by rw [sub_eq_neg_add]
  _ = cexp (α * I) * (2 * sin (θ / 2) * (-I * cexp (θ / 2 * I))) ^ n := by
    rw [lemma_1]
    ring
  -- Replace `-I` with `exp (-π / 2 * I)`.
  _ = cexp (α * I) * (2 * sin (θ / 2) * cexp (θ / 2 * I + -π / 2 * I)) ^ n := by
    congr
    rw [exp_add, exp_neg_pi_div_two_mul_I]
    ring
  -- Expand the power.
  _ = 2 ^ n * sin (θ / 2) ^ n * (cexp (α * I) * cexp (θ / 2 * I + -π / 2 * I) ^ n) := by
    simp only [mul_pow]
    ring
  -- Merge the `cexp` factors.
  _ = _ := by
    rw [← exp_nat_mul, ← exp_add]
    congr
    ring

theorem algebra_152180 {n : ℕ} (α θ : ℝ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * n.choose k * Real.sin (α + k * θ) =
    2 ^ n * Real.sin (θ / 2) ^ n * Real.sin (α + n * (θ - π) / 2 ) := by
  -- Take the imagingary part of both sides of the above lemma.
  convert congrArg im (lemma_2 n α θ) using 1
  · calc _
    _ = (∑ k ∈ range (n + 1), ((-1) ^ k * n.choose k : ℝ) * cexp ((α + k * θ : ℝ) * I)).im := by
      simp only [im_sum, mul_im, ofReal_re, ofReal_im, exp_ofReal_mul_I_im, exp_ofReal_mul_I_re]
      simp
    _ = _ := by
      simp
  · calc _
    _ = ((2 ^ n : ℝ) * ↑(Real.sin (θ / 2) ^ n) * cexp (↑(α + n * (θ - π) / 2) * I)).im := by
      simp only [mul_re, mul_im, ofReal_re, ofReal_im, exp_ofReal_mul_I_im, exp_ofReal_mul_I_re]
      simp
    _ = _  := by
      simp
