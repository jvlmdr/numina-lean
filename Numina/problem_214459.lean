-- https://cloud.kili-technology.com/label/projects/label/cm91j40co0088seayzby00k9l

import Mathlib

/- For the elements of the sequence $a_{n}$, it holds that $a_{1} = 1337$,
and furthermore, that $a_{2 n + 1} = a_{2 n} = n - a_{n}$ for every positive integer $n$.
Determine the value of $a_{2004}$. -/

theorem algebra_214459 (a : ℕ → ℤ) (ha1 : a 1 = 1337)
    (ha_odd : ∀ n, a (2 * n + 1) = a (2 * n)) (ha_even : ∀ n, a (2 * n) = n - a n) :
    a 2004 = 2004 :=
  -- Apply the recursive equations to reduce the index until we reach a base case.
  calc a 2004
  _ = 1002 - a 1002 := by simp [ha_even 1002]
  _ = 1002 - (501 - a 501) := by simp [ha_even 501]
  _ = 501 + a 501 := by ring
  _ = 501 + (250 - a 250) := by simp [ha_odd 250, ha_even 250]
  _ = 751 - a 250 := by ring
  _ = 751 - (125 - a 125) := by simp [ha_even 125]
  _ = 626 + a 125 := by ring
  _ = 626 + (62 - a 62) := by simp [ha_odd 62, ha_even 62]
  _ = 688 - a 62 := by ring
  _ = 688 - (31 - a 31) := by simp [ha_even 31]
  _ = 657 + a 31 := by ring
  _ = 657 + (15 - a 15) := by simp [ha_odd 15, ha_even 15]
  _ = 672 - a 15 := by ring
  _ = 672 - (7 - a 7) := by simp [ha_odd 7, ha_even 7]
  _ = 665 + a 7 := by ring
  _ = 665 + (3 - a 3) := by simp [ha_odd 3, ha_even 3]
  _ = 668 - a 3 := by ring
  _ = 668 - (1 - a 1) := by simp [ha_odd 1, ha_even 1]
  _ = 667 + a 1 := by ring
  _ = 2004 := by simp [ha1]
