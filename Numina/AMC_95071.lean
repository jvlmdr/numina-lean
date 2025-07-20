-- https://cloud.kili-technology.com/label/projects/label/cm7eniblv00c2zz87b9biya5m
-- https://artofproblemsolving.com/wiki/index.php/2001_AMC_12_Problems/Problem_13

import Mathlib

/- The parabola with equation $p(x) = a x^2 + b x + c$ and vertex $(h, k)$
is reflected about the line $y = k$.
This results in the parabola with equation $q(x) = d x^2 + e x + f$.
Which of the following equals $a + b + c + d + e + f$?
(A) $2 b$
(B) $2 c$
(C) $2 a + 2 b$
(D) $2 h$
(E) $2 k$ -/

theorem algebra_95071 {a b c d e f k : ℝ} {p q : ℝ → ℝ}
    (hp : ∀ x, p x = a * x ^ 2 + b * x + c) (hq : ∀ x, q x = d * x ^ 2 + e * x + f)
    (hpq : ∀ x, q x - k = -(p x - k)) :
    a + b + c + d + e + f = 2 * k := by
  -- From q - k = -(p - k), we have q = 2k - p.
  simp_rw [sub_eq_iff_eq_add] at hpq
  -- Use the fact that a + b + c = p 1.
  calc a + b + c + d + e + f
  _ = p 1 + q 1 := by rw [hp, hq]; ring
  _ = 2 * k := by rw [hpq]; ring
