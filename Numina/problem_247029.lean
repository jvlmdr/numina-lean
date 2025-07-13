-- https://cloud.kili-technology.com/label/projects/label/cmcbovi8d00sgueax16w7yma5

import Mathlib

open Finset

/- If $n$ is a natural number greater than 1, such that
$$
\left[\frac{n}{1}\right] + \left[\frac{n}{2}\right] + \ldots + \left[\frac{n}{n}\right] =
2 + \left[\frac{n-1}{1}\right] + \left[\frac{n-1}{2}\right] + \ldots + \left[\frac{n-1}{n-1}\right]
$$
then $n$ is a prime number. Prove it! -/

theorem number_theory_247029 (n : ℕ) :
    ∑ k ∈ Icc 1 n, n / k = 2 + ∑ k ∈ Icc 1 (n - 1), (n - 1) / k → n.Prime := by
  -- We can handle the cases `n = 0`, `n = 1` and introduce the assumption that `2 ≤ n`.
  wlog hn : 1 < n
  · rw [not_lt] at hn
    interval_cases n <;> simp

  intro h
  -- Unfolding the terms `k = 1` and `k = n` from the sums, we can cancel `n + 1` on both sides.
  have h : ∑ k ∈ Ioo 1 n, n / k = ∑ k ∈ Ioo 1 n, (n - 1) / k := by
    rw [← add_right_inj (n + 1)]
    convert h using 1
    · calc _
      _ = n + ∑ k ∈ Ioo 1 n, n / k + 1 := by ring
      _ = ∑ k ∈ Icc 1 n, n / k := by
        rw [← sum_Ico_add_right hn.le, ← left_add_sum_Ioo hn]
        suffices 0 < n by simp [this]
        linarith
    · calc _
      _ = 2 + (n - 1) + ∑ k ∈ Ioo 1 n, (n - 1) / k := by
        congr 1
        rw [← Nat.add_sub_assoc hn.le]
        simp [add_comm]
      _ = 2 + ∑ k ∈ Ico 1 n, (n - 1) / k := by
        rw [← left_add_sum_Ioo hn]
        simp [add_assoc]
      _ = _ := by
        congr
        rw [Nat.sub_add_cancel hn.le]

  -- Prove by contradiction.
  -- If there is a number (prime factor) `p < n` that divides `n`,
  -- then `⌊(n - 1) / p⌋` will be strictly less than `⌊n / p⌋`.
  -- Note that we already have `⌊(n - 1) / k⌋ ≤ ⌊n / k⌋` for all `k`.
  rw [Nat.prime_def]
  refine ⟨hn, ?_⟩
  contrapose! h
  refine ne_of_gt ?_
  refine sum_lt_sum ?_ (h.imp ?_)
  · intro k hi
    gcongr
    simp
  · -- Show that the corresponding term for `k = p` is strictly less.
    intro p ⟨hp_dvd, hp⟩
    -- Establish that `p ≠ 0` (and hence `2 ≤ p`).
    have hp_zero : p ≠ 0 := by
      refine ne_zero_of_dvd_ne_zero ?_ hp_dvd
      exact Nat.not_eq_zero_of_lt hn
    refine And.intro ?_ ?_
    · -- Show that `p` lies in the interval `1 < p < n`.
      rw [mem_Ioo]
      refine And.intro ?_ ?_
      · exact (Nat.two_le_iff p).mpr ⟨hp_zero, hp.1⟩
      · refine lt_of_le_of_ne ?_ hp.2
        exact Nat.le_of_dvd (by linarith) hp_dvd
    · -- Substitute `n + 1` for `n` to eliminate `n - 1` for easier manipulation.
      cases n with
      | zero => contradiction
      | succ n => simp [Nat.div_lt_div_of_lt_of_dvd hp_dvd]
