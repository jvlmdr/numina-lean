-- https://cloud.kili-technology.com/label/projects/label/cmb4vlozi000kwgay2bt83mw9

import Mathlib

open Finset

/- Let $p > 3$ be a prime number. Show that $p^{2}$ is a divisor of
$$
\sum_{k=1}^{p-1} k^{2 p + 1}
$$
-/

-- Simplify the expression for the sum of powers modulo `p ^ 2`.
-- Use two times the sum and compare the sum to its reflection.
lemma two_mul_sum_pow_two_mul_add_one_modEq (p : ℕ) :
    2 * ∑ k ∈ Ico 1 p, k ^ (2 * p + 1) ≡
      p * ∑ k ∈ Ico 1 p, k ^ (2 * p) [MOD p ^ 2] := by
  -- Switch to `ZMod`, where congruence is equality and we have `CommRing` for `sub_pow`.
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_pow]
  calc _
  _ = ∑ k ∈ Ico 1 p, (k ^ (2 * p + 1) + ↑(p - k) ^ (2 * p + 1) : ZMod (p ^ 2)) := by
    rw [two_mul, sum_add_distrib]
    rw [sum_Ico_reflect (fun k ↦ (k ^ (2 * p + 1) : ZMod (p ^ 2))) 1 (p.le_add_right 1)]
    simp
  _ = _ := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk ↦ ?_
    rw [mem_Ico] at hk
    -- Use `x ≤ p` to cast the subtraction to `ZMod (p ^ 2)`.
    rw [Nat.cast_sub hk.2.le]
    calc _
    _ = ∑ i ∈ range (2 * p + 1), ((-1) ^ (i + 1 + (2 * p + 1)) * p ^ (i + 1) * k ^ (2 * p - i) *
        (2 * p + 1).choose (i + 1) : ZMod (p ^ 2)) := by
      -- Expand power of difference. Extricate and cancel the first term.
      rw [sub_pow, sum_range_succ']
      simp [neg_one_pow_eq_pow_mod_two (2 * p + 1), Nat.add_mod]
    -- Swap the addition for easier simplification of the power of -1.
    _ = ∑ i ∈ range (2 * p + 1), ((-1) ^ (2 * (p + 1) + i) * p ^ (i + 1) * k ^ (2 * p - i) *
        (2 * p + 1).choose (i + 1) : ZMod (p ^ 2)) :=
      sum_congr rfl fun i _ ↦ by ring
    -- Separate the second term and show that the remaining terms are (congruent to) zero.
    _ = (p * k ^ (2 * p) * (2 * p + 1) : ZMod (p ^ 2)) := by
      rw [sum_range_succ', sum_eq_zero]
      ·  simp [neg_one_pow_eq_pow_mod_two (2 * (p + 1))]
      intro x hx
      suffices (p ^ (x + 2) : ZMod (p ^ 2)) = 0 by simp [this]
      suffices (p ^ 2 : ZMod (p ^ 2)) = 0 by simp [pow_add, this]
      suffices (↑(p ^ 2) : ZMod (p ^ 2)) = 0 by simpa only [Nat.cast_pow] using this
      simp
    -- Gather the constant factors together and simplify under modulo.
    _ = (p * (2 * p + 1) * k ^ (2 * p) : ZMod (p ^ 2)) := by ring
    _ = _ := by
      congr
      calc _
      _ = (2 * p ^ 2 + p : ZMod (p ^ 2)) := by ring
      _ = (2 * ↑(p ^ 2) + p : ZMod (p ^ 2)) := by rw [Nat.cast_pow]
      _ = _ := by simp

-- The sum of squares is a product that is divisible by 6.
-- It is easier to simplify expressions with addition only in the natural numbers.
lemma six_mul_sum_range_succ_sq (n : ℕ) :
    6 * ∑ k ∈ range (n + 1), k ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [sum_range_succ, mul_add, IH]
    ring

-- The expression for the sum of squares using subtraction.
lemma six_mul_sum_range_sq (n : ℕ) :
    6 * ∑ k in range n, k ^ 2 = n * (n - 1) * (2 * n - 1) := by
  cases n with
  | zero => simp
  | succ n => simpa [mul_comm n] using six_mul_sum_range_succ_sq n

-- Any prime number greater than 3 is coprime to 6.
lemma coprime_six_of_prime_of_three_lt {p : ℕ} (h_prime : p.Prime) (h_gt : 3 < p) :
    p.Coprime 6 := by
  cases le_or_lt p 6 with
  | inl h =>
    interval_cases p
    · contradiction  -- 4 is not prime
    · norm_num  -- 5 and 6 are coprime
    · contradiction  -- 6 is not prime
  | inr h => exact Nat.coprime_of_lt_prime (by norm_num) h h_prime

theorem number_theory_262514 (p : ℕ) (hp : p.Prime) (h : 3 < p) :
    p ^ 2 ∣ ∑ k ∈ Ico 1 p, k ^ (2 * p + 1) := by
  -- Since `p` is not 2, it suffices to show that `p ^ 2` divides two times the sum.
  suffices p ^ 2 ∣ 2 * ∑ k ∈ Ico 1 p, k ^ (2 * p + 1) by
    refine Nat.Coprime.dvd_of_dvd_mul_left ?_ this
    rw [Nat.coprime_two_right]
    refine Odd.pow ?_
    refine Nat.Prime.odd_of_ne_two hp ?_
    linarith
  -- Apply the congruence for two times the sum.
  rw [← Nat.modEq_zero_iff_dvd]
  refine .trans (two_mul_sum_pow_two_mul_add_one_modEq p) ?_
  rw [Nat.modEq_zero_iff_dvd]
  -- Cancel `p` from both sides of the divisibility condition.
  rw [sq]
  refine Nat.mul_dvd_mul_left p ?_
  -- Apply Fermat's little theorem to cancel factors of `k ^ (p - 1)` in each term of the sum.
  rw [← Nat.modEq_zero_iff_dvd]
  suffices ∑ k ∈ Ico 1 p, k ^ 2 ≡ 0 [MOD p] by
    refine .trans ?_ this
    rw [← ZMod.natCast_eq_natCast_iff]
    -- Apply Fermat's little theorem to show that `(k ^ 2) ^ p = k ^ 2` in `ZMod p`.
    -- This is achieved using `ZMod.pow_card` (a simp lemma) where `p` is known to be prime.
    haveI : Fact (p.Prime) := ⟨hp⟩
    simp [pow_mul]
  rw [Nat.modEq_zero_iff_dvd]
  -- Rewrite sum on `Ico` as sum on `range`.
  suffices p ∣ ∑ k ∈ range p, k ^ 2 by simpa [sum_range_eq_add_Ico _ hp.pos] using this
  -- The sum of squares is `p (p - 1) (2 p - 1) / 6`.
  -- Clearly `p` divides the numerator; it suffices to show that `p` is coprime to 6.
  suffices p ∣ 6 * ∑ k ∈ range p, k ^ 2 from
    Nat.Coprime.dvd_of_dvd_mul_left (coprime_six_of_prime_of_three_lt hp h) this
  simp [six_mul_sum_range_sq, mul_assoc]
