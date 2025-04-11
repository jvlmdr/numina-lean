-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi300144nayat1gd68h

import Mathlib

/- Let's prove that if the number $\overline{a b c}$ written in the decimal system
is divisible by 7, then the fraction $\frac{\overline{b c} + 16 a}{\overline{b c} - 61 a}$
can be simplified by 7. -/

theorem number_theory_214766 {a b c : ℤ}
    (h : 7 ∣ (100 * a + 10 * b + c)) :
    7 ∣ (b * 10 + c + 16 * a) ∧ 7 ∣ (b * 10 + c - 61 * a) := by
  refine ⟨?_, ?_⟩
  · -- Rewrite `16 a = 100 a - 7 (12 a)`.
    convert Int.dvd_sub h (Int.dvd_mul_right 7 (12 * a)) using 1
    ring
  · -- Rewrite `-61 a = 100 a - 7 (23 a)`.
    convert Int.dvd_sub h (Int.dvd_mul_right 7 (23 * a)) using 1
    ring
