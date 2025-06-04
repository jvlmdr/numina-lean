-- https://cloud.kili-technology.com/label/projects/label/cma3ygf2a007nahayyvhz3gtk
-- https://web.archive.org/web/20041210123510/http://www.kalva.demon.co.uk/soviet/ssoln/ssol9220.html

import Mathlib

/- Find all integers $k > 1$ such that for some distinct positive integers $a, b$, the number
$k^a + 1$ can be obtained from $k^b + 1$ by reversing the order of its (decimal) digits. -/

lemma digits_pow_add_one_of_ne_zero {b : ℕ} (hb : 1 < b) {n : ℕ} (hn : n ≠ 0) :
    Nat.digits b (b ^ n + 1) = 1 :: (List.replicate (n - 1) 0 ++ [1]) := by
  calc _
  _ = Nat.digits b (1 + b ^ n) := by rw [add_comm]
  _ = Nat.digits b 1 ++ List.replicate (n - 1) 0 ++ Nat.digits b 1 := by
    rw [Nat.digits_append_zeroes_append_digits hb one_pos]
    congr 1
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    simp [hb, hn]
  _ = _ := by simp [hb]

-- Need to exclude the case where `n = 0` and `b = 2`, where `2 ^ 0 + 1 = 2 = 10 (base 2)`.
lemma digits_pow_add_one_palindrome {b : ℕ} (hb : 1 < b) (n : ℕ) (h : b ≠ 2 ∨ n ≠ 0) :
    (Nat.digits b (b ^ n + 1)).Palindrome := by
  refine .of_reverse_eq ?_
  cases n with
  | zero =>
    cases h with
    | inl h =>
      suffices 2 < b by simp [this]
      exact Nat.lt_of_le_of_ne hb h.symm
    | inr h => contradiction
  | succ n =>
    rw [digits_pow_add_one_of_ne_zero hb (by simp)]
    simp

lemma reverse_palindrome (l : List ℕ) : l.reverse.Palindrome ↔ l.Palindrome := by
  simp [List.Palindrome.iff_reverse_eq, eq_comm]

lemma strictMono_len_digits_pow_add_one_of_base_lt {b : ℕ} (hb : 1 < b) {k : ℕ} (hk : b < k)
    {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x < y) :
    (Nat.digits b (k ^ x + 1)).length < (Nat.digits b (k ^ y + 1)).length := by
  simp only [Nat.digits_len b _ hb (Nat.add_one_ne_zero _)]
  rw [add_lt_add_iff_right]
  suffices (k ^ x + 1) * b ≤ k ^ y + 1 by
    refine le_trans ?_ (Nat.log_monotone this)
    rw [Nat.log_mul_base hb (Nat.add_one_ne_zero _)]
  -- Use `b * (k ^ x + 1) ≤ (b + 1) * k ^ x + 1 ≤ k ^ (x + 1) + 1 ≤ k ^ y + 1`.
  calc _
  _ = b * k ^ x + b := by ring
  _ ≤ b * k ^ x + (k ^ x + 1) := by
    suffices b ≤ k ^ x + 1 by gcongr
    calc _
    _ ≤ k := hk.le
    _ ≤ k ^ x := Nat.le_self_pow hx k
    _ ≤ k ^ x + 1 := by simp
  _ = (b + 1) * k ^ x + 1 := by ring
  _ ≤ k * k ^ x + 1 := by gcongr; linarith
  _ = k ^ (x + 1) + 1 := by ring
  _ ≤ _ := by gcongr <;> linarith

lemma base_le_of_not_digits_palindrome (b : ℕ) {x : ℕ} (hx : ¬(Nat.digits b x).Palindrome) :
    b ≤ x := by
  contrapose! hx
  cases x with
  | zero => simpa using List.Palindrome.nil
  | succ x => simpa [Nat.digits_of_lt _ _ _ hx] using List.Palindrome.singleton _


theorem number_theory_125818 (k : ℕ) (hk_gt : 1 < k) :
    (∃ a b, 0 < a ∧ 0 < b ∧ a ≠ b ∧
      Nat.digits 10 (k ^ a + 1) = (Nat.digits 10 (k ^ b + 1)).reverse) ↔
    k = 3 := by
  -- First confirm that `k = 3` is a solution from `2^3 + 1 = 28`, `2^4 + 1 = 82`.
  -- This follows from simple evaluation.
  refine ⟨?_, fun hk ↦ ⟨3, 4, by simp [hk]⟩⟩
  intro ⟨a, b, ha, hb, h_ne, h_dig⟩
  -- Use symmetry to assume `a < b` without loss of generality.
  wlog hab : a < b generalizing a b
  · rw [not_lt] at hab
    refine this b a hb ha h_ne.symm ?_ ?_
    · simpa using congrArg List.reverse h_dig.symm
    · exact lt_of_le_of_ne hab h_ne.symm

  -- We know that both numbers cannot be palindromes, as this would imply `a = b`.
  have hb_npal : ¬(Nat.digits 10 (k ^ b + 1)).Palindrome := by
    refine mt (fun h ↦ ?_) h_ne
    suffices k ^ a = k ^ b from Nat.pow_right_injective hk_gt this
    rw [h.reverse_eq] at h_dig
    simpa using Nat.digits.injective 10 h_dig
  have ha_npal : ¬(Nat.digits 10 (k ^ a + 1)).Palindrome := by
    simpa only [h_dig, reverse_palindrome]

  -- Eliminate the case where `k = 10` as the number is a palindrome.
  have hk_ne : k ≠ 10 := by
    refine mt (fun hk ↦ ?_) hb_npal
    rw [hk]
    exact digits_pow_add_one_palindrome (by norm_num) b (by simp)
  -- We cannot have `k > 10` as `k ^ b + 1` will have more digits than `k ^ a + 1`.
  have hk_le : k ≤ 10 := by
    refine le_of_not_lt fun hk_gt ↦ ?_
    suffices (Nat.digits 10 (k ^ a + 1)).length ≠ (Nat.digits 10 (k ^ b + 1)).length by
      refine this ?_
      simpa using congrArg List.length h_dig
    refine ne_of_lt ?_
    exact strictMono_len_digits_pow_add_one_of_base_lt (by norm_num) hk_gt ha.ne' hb.ne' hab
  -- Combine these results into `k < 10`. TODO: Do we need this?
  have hk_lt : k < 10 := Nat.lt_of_le_of_ne hk_le hk_ne

  -- The numbers `k ^ _ + 1` must be at least 10, otherwise they are trivial palindromes.
  have ha_pow_ge : 10 ≤ k ^ a + 1 := base_le_of_not_digits_palindrome 10 ha_npal
  -- Clearly `k ^ a + 1` cannot be 10; this would imply the first digit of `k ^ b + 1` is 0.
  have ha_pow_ne : k ^ a + 1 ≠ 10 := by
    intro ha_pow
    refine Nat.getLast_digit_ne_zero 10 (m := k ^ b + 1) (by simp) ?_
    suffices Nat.digits 10 (k ^ b + 1) = [1, 0] by
      simp only [this]
      simp
    calc _
    _ = (Nat.digits 10 (k ^ a + 1)).reverse := List.reverse_eq_iff.mp h_dig.symm
    _ = _ := by simp [ha_pow]
  -- Combining these, we have `10 < k ^ a + 1`.
  have ha_pow_gt : 10 < k ^ a + 1 := Nat.lt_of_le_of_ne ha_pow_ge ha_pow_ne.symm

  have hb_pow_gt : 10 < k ^ b + 1 := Nat.lt_of_le_of_ne sorry sorry

  -- Since `k ^ a + 1` and `k ^ b + 1` have the same number of digits,
  -- `k ^ b + 1` cannot exceed `10 * (k ^ a + 1)`.
  have hb_pow_lt_ten_mul : k ^ b + 1 < 10 * (k ^ a + 1) := by
    -- TODO: clean up?
    suffices k ^ b + 1 < 10 * 10 ^ Nat.log 10 (k ^ a + 1) by
      refine lt_of_lt_of_le this ?_
      gcongr
      exact Nat.pow_log_le_self 10 (by simp)
    suffices Nat.log 10 (k ^ b + 1) < Nat.log 10 (k ^ a + 1) + 1 by
      rw [← pow_succ', Nat.lt_pow_iff_log_lt (by norm_num) (by simp)]
      exact this
    rw [Nat.lt_add_one_iff]
    -- This follows from the fact that they have the same number of digits.
    refine ge_of_eq ?_
    simpa [Nat.digits_len 10, -Nat.digits_of_two_le_of_pos] using congrArg List.length h_dig

  -- From this, we can see that we cannot have `2 * a < b`.
  have hba : b ≤ 2 * a := by
    refine le_of_not_lt fun hab ↦ ?_
    -- To find a contradiction, we will show that `k ^ a < 10`.
    suffices k ^ a < 10 from ha_pow_gt.not_le this
    suffices k ^ a * (k ^ a + 1) < 10 * (k ^ a + 1) from Nat.lt_of_mul_lt_mul_right this
    calc _
    _ ≤ k ^ a * k ^ (a + 1) := by
      gcongr
      cases k with
      | zero => contradiction
      | succ k =>
        rw [pow_succ', add_mul]
        gcongr
        · simpa using hk_gt
        · simpa using Nat.one_le_pow' a k
    _ = k ^ (2 * a + 1) := by ring
    _ ≤ k ^ b := by
      gcongr
      · exact hk_gt.le
      · exact hab
    _ < k ^ b + 1 := by simp
    _ < _ := hb_pow_lt_ten_mul
  -- ...from which we obtain `b - a ≤ a`.
  have hba : b - a ≤ a := by
    refine Nat.sub_le_of_le_add ?_
    simpa [two_mul] using hba

  have : k ^ b + 1 > (k ^ a + 1) * (k ^ (b - a) - 1) := by
    calc _
    _ > k ^ b - 1 := Nat.sub_lt_succ _ 1
    _ ≥ k ^ b - (k ^ a - k ^ (b - a)) - 1 := by
      gcongr
      simp
    _ = k ^ b + k ^ (b - a) - k ^ a - 1 := by
      congr 1
      refine tsub_tsub_eq_add_tsub_of_le ?_
      gcongr
      exact hk_gt.le
    _ = _ := by
      suffices k ^ b = k ^ a * k ^ (b - a) by simp [mul_tsub, Nat.sub_add_eq, add_mul, this]
      rw [← pow_add]
      simp [hab.le]

  have : k ^ (b - a) - 1 < 9 := by
    refine Nat.lt_of_le_of_ne ?_ ?_
    · sorry
    · sorry

  have hk : k = 3 ∨ k = 6 ∨ k = 9 := by
    suffices 3 ∣ k by
      revert this  -- TODO: ok?
      interval_cases k <;> norm_num
    suffices 3 ∣ k ^ a from Nat.prime_three.dvd_of_dvd_pow this
    suffices 9 ∣ k ^ a from Nat.dvd_of_pow_dvd one_le_two this
    sorry

  refine hk.resolve_right fun hk ↦ ?_

  sorry
