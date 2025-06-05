-- https://cloud.kili-technology.com/label/projects/label/cma3ygf2a007nahayyvhz3gtk
-- https://web.archive.org/web/20041210123510/http://www.kalva.demon.co.uk/soviet/ssoln/ssol9220.html

import Mathlib

/- Find all integers $k > 1$ such that for some distinct positive integers $a, b$, the number
$k^a + 1$ can be obtained from $k^b + 1$ by reversing the order of its (decimal) digits. -/

-- The number `b ^ (n + 1) + 1` is 100⋯01 (with `n` zeros) in base `b`.
lemma digits_succ_base_pow_succ {b : ℕ} (hb : 1 < b) (n : ℕ) :
    b.digits (b ^ (n + 1) + 1) = 1 :: (List.replicate n 0 ++ [1]) := by
  simpa [hb, add_comm 1] using (@Nat.digits_append_zeroes_append_digits b n 1 1 hb one_pos).symm

-- -- The number `b ^ n + 1` is 100⋯01 (with `n - 1` zeros) in base `b` for `n ≠ 0`.
-- lemma digits_succ_base_pow_of_ne_zero {b : ℕ} (hb : 1 < b) {n : ℕ} (hn : n ≠ 0) :
--     b.digits (b ^ n + 1) = 1 :: (List.replicate (n - 1) 0 ++ [1]) := by
--   suffices 1 ≤ n by simpa [this] using digits_succ_base_pow_succ hb (n - 1)
--   simpa [Nat.one_le_iff_ne_zero]

-- Need to exclude the case where `n = 0` and `b = 2`, where `2 ^ 0 + 1 = 2 = 10 (base 2)`.
lemma digits_pow_add_one_palindrome {b : ℕ} (hb : 1 < b) (n : ℕ) (h : b ≠ 2 ∨ n ≠ 0) :
    (b.digits (b ^ n + 1)).Palindrome := by
  refine .of_reverse_eq ?_
  cases n with
  | zero =>
    cases h with
    | inl h =>
      suffices 2 < b by simp [this]
      exact Nat.lt_of_le_of_ne hb h.symm
    | inr h => contradiction
  | succ n => simp [digits_succ_base_pow_succ hb]

-- The reverse of a list is a palindrome iff the list is a palindrome.
lemma reverse_palindrome (l : List ℕ) : l.reverse.Palindrome ↔ l.Palindrome := by
  simp [List.Palindrome.iff_reverse_eq, eq_comm]

lemma strictMono_len_digits_pow_add_one_of_base_lt {b : ℕ} (hb : 1 < b) {k : ℕ} (hk : b < k)
    {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x < y) :
    (b.digits (k ^ x + 1)).length < (b.digits (k ^ y + 1)).length := by
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

lemma base_le_of_not_digits_palindrome (b : ℕ) {x : ℕ} (hx : ¬(b.digits x).Palindrome) :
    b ≤ x := by
  contrapose! hx
  cases x with
  | zero => simpa using List.Palindrome.nil
  | succ x => simpa [Nat.digits_of_lt _ _ _ hx] using List.Palindrome.singleton _

-- -- Defined in analogy to `List.exists_cons_of_ne_nil`.
-- lemma exist_concat_of_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) :
--     ∃ (s : List α) (x : α), l = s ++ [x] := by
--   obtain ⟨x, s, h⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr hl)
--   use s.reverse, x
--   simpa using h

lemma nine_dvd_sub_of_digits_eq {x y : ℕ} (h : (Nat.digits 10 x).sum = (Nat.digits 10 y).sum) :
    (9 : ℤ) ∣ y - x := by
  refine Nat.modEq_iff_dvd.mp ?_
  calc _
  _ ≡ (Nat.digits 10 x).sum [MOD 9] := Nat.modEq_nine_digits_sum x
  _ ≡ (Nat.digits 10 y).sum [MOD 9] := by rw [h]
  _ ≡ _ [MOD 9] := (Nat.modEq_nine_digits_sum y).symm

-- Could be useful?
-- TODO: Remove if not.
lemma nine_dvd_tsub_of_digits_eq {x y : ℕ} (h : (Nat.digits 10 x).sum = (Nat.digits 10 y).sum) :
    9 ∣ y - x := by
  cases le_or_lt y x with
  | inl hxy => simp [hxy]
  | inr hxy =>
    suffices (9 : ℤ) ∣ ↑(y - x) from Int.ofNat_dvd.mp this
    rw [Nat.cast_sub hxy.le]
    exact nine_dvd_sub_of_digits_eq h


-- The last digit of a number is the number divided by `10 ^ (m - 1)`
lemma digits_getLast_eq_div_base_pow {b : ℕ} (hb : 1 < b) {n : ℕ} (h_nil : b.digits n ≠ []) :
    (b.digits n).getLast h_nil = n / b ^ ((b.digits n).length - 1) := by
  symm
  simpa [List.drop_length_sub_one h_nil, Nat.ofDigits_digits] using
    Nat.ofDigits_div_pow_eq_ofDigits_drop ((b.digits n).length - 1)
      (Nat.zero_lt_of_lt hb) (b.digits n) fun _ ↦ Nat.digits_lt_base hb

-- Iff version of `Nat.div_eq_of_lt_le`.
lemma nat_div_eq_iff {k x y : ℕ} (h : 0 < k) : x / k = y ↔ y * k ≤ x ∧ x < (y + 1) * k := by
  rw [Nat.eq_iff_le_and_ge, and_comm]
  refine and_congr ?_ ?_
  · rw [Nat.le_div_iff_mul_le h]
  · rw [← Nat.lt_add_one_iff, Nat.div_lt_iff_lt_mul h]

lemma digits_getLast_eq_iff_mem_Ico {b : ℕ} (hb : 1 < b) {n : ℕ} (h_nil : b.digits n ≠ []) (x : ℕ) :
    (b.digits n).getLast h_nil = x ↔
    n ∈ Set.Ico (x * b ^ ((b.digits n).length - 1)) ((x + 1) * b ^ ((b.digits n).length - 1)) := by
  rw [digits_getLast_eq_div_base_pow hb]
  rw [nat_div_eq_iff (Nat.pow_pos <| Nat.zero_lt_of_lt hb)]
  simp

lemma pow_eq_iff_eq_of_factorization_eq_one (n p x : ℕ) (hp : p.Prime)
    (h : n.factorization p = 1) :
    (∃ k, x ^ k = n) ↔ x = n := by
  constructor
  · intro ⟨k, hn⟩
    have h : (x ^ k).factorization p = 1 := by rw [hn, h]
    -- TODO: clean up
    have ⟨hk, h⟩ : k = 1 ∧ x.factorization p = 1 := by simpa using h
    simpa [hk] using hn
  · intro h
    use 1
    simp [h]

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

  have h_x_mul_lt_y : k ^ b + 1 > (k ^ a + 1) * (k ^ (b - a) - 1) := by
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

  -- TODO: use this form above
  replace h_mul_x_lt_y : (k ^ (b - a) - 1) * (k ^ a + 1) < k ^ b + 1 := by
    simpa [mul_comm] using h_x_mul_lt_y

  have hz_lt : k ^ (b - a) - 1 < 9 := by
    refine Nat.lt_of_le_of_ne ?_ ?_
    · suffices k ^ (b - a) - 1 < 10 from Nat.le_of_lt_succ this
      -- TODO: if only used here, move inside?
      simpa using lt_trans (h_mul_x_lt_y) hb_pow_lt_ten_mul
    · suffices k ^ (b - a) ≠ 10 by simpa
      -- Since 10 contains factors with multiplicity one, the only way to satisfy
      -- `k ^ r = 10` is with `k = 10`. This is a contradiction since `k < 10`.
      intro h
      suffices k = 10 by simp [this] at hk_lt
      refine (pow_eq_iff_eq_of_factorization_eq_one 10 2 k Nat.prime_two ?_).mp ⟨_, h⟩
      suffices Nat.factorization (2 * 5) 2 = 1 by simpa
      rw [Nat.factorization_mul_of_coprime] <;> norm_num

  have hk : k = 3 ∨ k = 6 ∨ k = 9 := by
    suffices 3 ∣ k by
      revert this  -- TODO: ok?
      interval_cases k <;> norm_num
    suffices 3 ∣ k ^ a from Nat.prime_three.dvd_of_dvd_pow this
    -- suffices 9 ∣ k ^ a from Nat.dvd_of_pow_dvd one_le_two this
    -- suffices 9 ∣ (k ^ b - a)

    -- TODO: use 9 here?
    -- We can't put both 3's in `k ^ (b - a) - 1 < 9`, hence we must have `3 ∣ k ^ a`.
    suffices 3 ^ 2 ∣ (k ^ (b - a) - 1) * k ^ a by
      -- TODO: Possible to avoid multiple uses? Or move outside even?
      have h₁ : 0 < k ^ (b - a) - 1 := by
        rw [tsub_pos_iff_lt]
        calc _
        _ < k := hk_gt
        _ ≤ k ^ (b - a) := by
          refine Nat.le_self_pow ?_ k
          simpa [Nat.sub_ne_zero_iff_lt] using hab
      have h₂ : k ^ a ≠ 0 := pow_ne_zero _ (Nat.not_eq_zero_of_lt hk_gt)

      rw [Nat.prime_three.dvd_iff_one_le_factorization h₂]

      rw [Nat.prime_three.pow_dvd_iff_le_factorization (mul_ne_zero h₁.ne' h₂)] at this
      rw [Nat.factorization_mul h₁.ne' h₂] at this
      rw [Finsupp.add_apply] at this
      suffices (k ^ (b - a) - 1).factorization 3 < 2 by linarith
      suffices ¬3 ^ 2 ∣ k ^ (b - a) - 1 by
        rw [Nat.prime_three.pow_dvd_iff_le_factorization h₁.ne'] at this
        simpa using this
      exact Nat.not_dvd_of_pos_of_lt h₁ hz_lt

    -- TODO: cleanup
    have : (k ^ (b - a) - 1) * k ^ a = (k ^ b + 1) - (k ^ a + 1) := by
      calc _
      _ = k ^ (b - a + a) - k ^ a := by simp [pow_add, tsub_mul]
      _ = k ^ b - k ^ a := by simp [hab.le]
      _ = _ := by simp

    suffices 9 ∣ (k ^ (b - a) - 1) * k ^ a by simpa
    rw [this]
    refine nine_dvd_tsub_of_digits_eq ?_
    -- rw [Nat.cast_sub sorry]
    -- refine nine_dvd_sub_of_digits_eq ?_
    simpa only [List.sum_reverse] using congrArg List.sum h_dig

  refine hk.resolve_right fun hk ↦ ?_

  have : 5 ≤ k ^ (b - a) - 1 := by
    suffices 6 ≤ k ^ (b - a) from le_tsub_of_add_le_right this
    suffices 6 ≤ k by
      refine le_trans this (Nat.le_self_pow ?_ k)
      simpa [Nat.sub_ne_zero_iff_lt]
    suffices ∀ k, k = 6 ∨ k = 9 → 6 ≤ k from this k hk
    simp

  replace h_mul_x_lt_y : 5 * (k ^ a + 1) < k ^ b + 1 := by
    refine lt_of_le_of_lt ?_ h_mul_x_lt_y
    gcongr

  -- Since `k ^ b + 1 > (k ^ (b - a) - 1) * (k ^ a + 1)` and `k ^ (b - a) - 1 ≥ 5`, the first digit
  -- of `k ^ a + 1` must be 1. Otherwise, `k ^ b + 1` would have more digits than `k ^ a + 1`.
  -- Due to the reverse relation, this means that the last digit of `k ^ b + 1` is 1.
  -- Therefore, the last digit of `k ^ b` is 0. This is impossible: it implies that `10 ∣ k ^ b`.
  have h_not_ten_dvd : ¬10 ∣ k ^ b := by
    change ¬2 * 5 ∣ k ^ b
    suffices ¬5 ∣ k ^ b from mt dvd_of_mul_left_dvd this
    suffices ¬5 ∣ k from mt Nat.prime_five.dvd_of_dvd_pow this
    suffices ∀ k, k = 6 ∨ k = 9 → ¬5 ∣ k from this k hk
    norm_num

  have h_len : (Nat.digits 10 (k ^ a + 1)).length = (Nat.digits 10 (k ^ b + 1)).length := by
    simpa using congrArg List.length h_dig

  have hx_nil : Nat.digits 10 (k ^ a + 1) ≠ [] := by simp
  --   exact Nat.le_of_lt_succ ha_pow_ge
  have hx_getLast : (Nat.digits 10 (k ^ a + 1)).getLast hx_nil = 1 := by
    rw [digits_getLast_eq_iff_mem_Ico (by norm_num)]
    -- generalize hm : (Nat.digits 10 (k ^ a + 1)).length = m
    -- We know that `k ^ b + 1` has the same number of digits as `k ^ a + 1`.
    -- We have `5 * (k ^ a + 1) < k ^ b + 1 < 10 ^ (m + 1)` and `10 ^ (m - 1) ≤ k ^ a + 1`.
    -- Therefore, `k ^ a + 1 < 10 ^ (m + 1) / 5 = 2 * 10 ^ m`.
    simp only [one_mul, Nat.reduceAdd, Set.mem_Ico]
    constructor
    -- The lower bound is simply from the order of magnitude.
    · suffices 10 ^ ((Nat.digits 10 (k ^ a + 1)).length - 1 + 1) ≤ 10 * (k ^ a + 1) by
        simpa [Nat.pow_succ']
      rw [Nat.sub_add_cancel (by simp)]
      exact Nat.base_pow_length_digits_le 10 _ (by norm_num) (by simp)
    -- TODO: Comment here.
    · have : 5 * (k ^ a + 1) < 10 ^ (Nat.digits 10 (k ^ a + 1)).length := by
        calc _
        _ < k ^ b + 1 := h_mul_x_lt_y
        _ < 10 ^ (Nat.digits 10 (k ^ b + 1)).length :=
          Nat.lt_base_pow_length_digits'
        _ = _ := by rw [h_len]
      -- TODO: Might be easier to multiply on right?
      suffices 5 * (k ^ a + 1) < 5 * (2 * 10 ^ ((Nat.digits 10 (k ^ a + 1)).length - 1)) by
        simpa
      convert this using 1  -- TODO: Combine?
      calc _
      _ = 10 ^ ((Nat.digits 10 (k ^ a + 1)).length - 1 + 1) := by ring
      _ = _ := by simp

  have hy_nil : Nat.digits 10 (k ^ b + 1) ≠ [] := by simp
  have hy_head : (Nat.digits 10 (k ^ b + 1)).head hy_nil = 1 := by
    rw [List.head_eq_getLast_reverse]
    simpa only [h_dig] using hx_getLast
  have hy_mod : (k ^ b + 1) % 10 = 1 := by simpa using hy_head
  have hy_mod : k ^ b ≡ 0 [MOD 10] := Nat.ModEq.add_right_cancel' 1 hy_mod
  have hy_mod : 10 ∣ k ^ b := Nat.dvd_of_mod_eq_zero hy_mod

  exact h_not_ten_dvd hy_mod
