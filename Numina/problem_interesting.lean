-- https://cloud.kili-technology.com/label/projects/label/cm91j40cn006useayzzxf48z8

import Mathlib

/- A natural number $n$ is interesting if the sum of the digits of $n$ is equal to the
sum of the digits of $3 n+11$. Verify that there are infinitely many interesting numbers. -/

theorem number_theory_255881 :
    {n | (Nat.digits 10 n).sum = (Nat.digits 10 (3 * n + 11)).sum}.Infinite := by
  -- Observe that 8 is interesting: 3 * 8 + 11 = 35, 3 + 5 = 8.
  -- Consider numbers of the form `a 10^k + 8`.
  -- For k ≥ 2, we have `3 (a 10^k + 8) = (3 a) 10^k + 35`.
  -- This is satisfied by a = 9: 9 * 3 = 27, 2 + 7 = 9.
  rw [Set.infinite_iff_exists_gt]
  intro m
  -- Choose some `k` such that `m < 10 ^ (k + 2)`.
  let k := Nat.log 10 m
  use 8 + 10 ^ (k + 2) * 9
  constructor
  · rw [Set.mem_setOf_eq]
    calc _
    _ = (Nat.digits 10 8 ++ List.replicate (k + 1) 0 ++ Nat.digits 10 9).sum := by
      congr
      symm
      rw [Nat.digits_append_zeroes_append_digits (by norm_num) (by norm_num)]
      congr 1
      suffices (Nat.digits 10 8).length = 1 by
        rw [this]
        ring
      simp
    _ = (Nat.digits 10 35 ++ List.replicate k 0 ++ Nat.digits 10 27).sum := by simp
    _ = _ := by
      congr
      calc _
      _ = Nat.digits 10 (35 + 10 ^ (k + 2) * 27) := by
        rw [Nat.digits_append_zeroes_append_digits (by norm_num) (by norm_num)]
        congr 1
        suffices (Nat.digits 10 35).length = 2 by
          rw [this]
          ring
        simp
      _ = _ := by
        congr 1
        ring
  · -- Show that `k` provides a number larger than `m`.
    calc _
    _ < 10 ^ (Nat.log 10 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
    _ ≤ 10 ^ (Nat.log 10 m + 2) := by simp [Nat.pow_le_pow_of_le]
    _ = 10 ^ (k + 2) := rfl
    _ ≤ 10 ^ (k + 2) * 9 := by simp
    _ ≤ 8 + 10 ^ (k + 2) * 9 := by simp
