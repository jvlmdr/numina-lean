-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi300044nay8rcqzvfe

import Mathlib

/- Let $a$ be an integer. Show that 5 divides $a^2$ if and only if 5 divides $a$. -/

theorem number_theory_110877 (a : ℤ) : 5 ∣ a ^ 2 ↔ 5 ∣ a := by
  rw [sq]
  -- The reverse direction is trivial: if 5 ∣ a, then 5 ∣ a * a.
  refine ⟨?_, fun h ↦ h.mul_right a⟩
  intro h
  -- Use Euclid's lemma: if a prime divides a product,
  -- then it must divide one of the factors (which are identical for `a * a`).
  simpa using Int.Prime.dvd_mul' Nat.prime_five h
