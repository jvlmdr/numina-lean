-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi3001k4nayfsn5w9y9

import Mathlib

/- Does the number 11⋯1 (1000 ones) have a ten-digit divisor, all digits of which are different? -/

theorem number_theory_211660 : ¬∃ n, (Nat.digits 10 n).length = 10 ∧ (Nat.digits 10 n).Nodup ∧
    n ∣ Nat.ofDigits 10 (List.replicate 1000 1) := by
  simp only [not_exists, not_and]
  intro n h_len h_nodup

  -- Since 10 % 3 = 1, divisibility by 3 can be assessed from the sum of the digits.
  -- The digits of 11⋯1 have sum 1000, which is not divisible by 3.
  suffices 3 ∣ n by
    suffices h : ¬3 ∣ Nat.ofDigits 10 (List.replicate 1000 1) from mt this.trans h
    rw [Nat.dvd_iff_dvd_digits_sum 3 10 (by norm_num)]
    rw [Nat.digits_ofDigits 10 (by norm_num)]
    rotate_left
    · intro x hx
      rw [List.eq_of_mem_replicate hx]
      norm_num
    · intro hl
      rw [List.getLast_replicate]
      exact one_ne_zero
    rw [List.sum_replicate]
    norm_num

  -- The digits of n are a permutation of {0, 1, …, 9}, with sum 45, divisible by 3.
  suffices (Nat.digits 10 n).sum = 45 by
    rw [Nat.dvd_iff_dvd_digits_sum 3 10 (by norm_num), this]
    norm_num

  -- Obtain digits as a `Finset` to use `Finset.sum_range_id`.
  suffices (Nat.digits 10 n).toFinset = Finset.range 10 by
    calc _
    _ = ((Nat.digits 10 n).map id).sum := by simp
    _ = ∑ x in (Nat.digits 10 n).toFinset, x := (List.sum_toFinset _ h_nodup).symm
    _ = ∑ x in Finset.range 10, x := by rw [this]
    _ = 10 * (10 - 1) / 2 := Finset.sum_range_id 10
    _ = 45 := by norm_num

  -- Set of digits is equal to {0, 1, …, 9} since it is a subset with equal cardinality.
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro x hx
    rw [List.mem_toFinset] at hx
    rw [Finset.mem_range]
    exact Nat.digits_lt_base' hx
  · simp [List.toFinset_card_of_nodup h_nodup, h_len]
