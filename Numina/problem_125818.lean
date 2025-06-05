-- https://cloud.kili-technology.com/label/projects/label/cma3ygf2a007nahayyvhz3gtk
-- https://web.archive.org/web/20041210123510/http://www.kalva.demon.co.uk/soviet/ssoln/ssol9220.html

import Mathlib

/- Find all integers $k > 1$ such that for some distinct positive integers $a, b$, the number
$k^a + 1$ can be obtained from $k^b + 1$ by reversing the order of its (decimal) digits. -/

-- The number `b ^ (n + 1) + 1` is 100⋯01 (with `n` zeros) in base `b`.
lemma digits_succ_base_pow_succ {b : ℕ} (hb : 1 < b) (n : ℕ) :
    b.digits (b ^ (n + 1) + 1) = 1 :: (List.replicate n 0 ++ [1]) := by
  simpa [hb, add_comm 1] using (@Nat.digits_append_zeroes_append_digits b n 1 1 hb one_pos).symm

-- The number `b ^ n + 1` is 100⋯01 (with `n - 1` zeros) in base `b` for `n ≠ 0`.
lemma digits_succ_base_pow_of_ne_zero {b : ℕ} (hb : 1 < b) {n : ℕ} (hn : n ≠ 0) :
    b.digits (b ^ n + 1) = 1 :: (List.replicate (n - 1) 0 ++ [1]) := by
  suffices 1 ≤ n by simpa [this] using digits_succ_base_pow_succ hb (n - 1)
  simpa [Nat.one_le_iff_ne_zero]

-- The number of digits in `k ^ · + 1` in base `b` is *strictly* increasing for `b < k`.
lemma strictMono_len_digits_succ_pow_of_base_lt {b : ℕ} (hb : 1 < b) {k : ℕ} (hk : b < k)
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

-- Extend this result to include `b = k`.
lemma strictMono_len_digits_succ_pow_of_base_le {b : ℕ} (hb : 1 < b) {k : ℕ} (hk : b ≤ k)
    {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x < y) :
    (b.digits (k ^ x + 1)).length < (b.digits (k ^ y + 1)).length := by
  refine hk.eq_or_lt.elim ?_ fun hk ↦ strictMono_len_digits_succ_pow_of_base_lt hb hk hx hy hxy
  rintro rfl
  -- Replace `x, y` with `x + 1, y + 1`.
  obtain ⟨x, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hx
  obtain ⟨y, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hy
  simpa [digits_succ_base_pow_succ hb] using hxy

-- The difference of two numbers is divisible by 9 if the sum of their digits is equal.
lemma nine_dvd_sub_of_digits_eq {x y : ℕ} (h : (Nat.digits 10 x).sum = (Nat.digits 10 y).sum) :
    (9 : ℤ) ∣ y - x := by
  refine Nat.modEq_iff_dvd.mp ?_
  calc _
  _ ≡ (Nat.digits 10 x).sum [MOD 9] := Nat.modEq_nine_digits_sum x
  _ ≡ (Nat.digits 10 y).sum [MOD 9] := by rw [h]
  _ ≡ _ [MOD 9] := (Nat.modEq_nine_digits_sum y).symm

-- The same result using truncated subtraction; trivial since any numbers divides zero.
lemma nine_dvd_tsub_of_digits_eq {x y : ℕ} (h : (Nat.digits 10 x).sum = (Nat.digits 10 y).sum) :
    9 ∣ y - x := by
  cases le_or_lt y x with
  | inl hxy => simp [hxy]
  | inr hxy =>
    suffices (9 : ℤ) ∣ ↑(y - x) from Int.ofNat_dvd.mp this
    rw [Nat.cast_sub hxy.le]
    exact nine_dvd_sub_of_digits_eq h

-- The last digit of a number is its division by `b ^ (m - 1)` where `m` is the number of digits.
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

-- The last digit of a number corresponds to an interval in which the number lies.
lemma digits_getLast_eq_iff_mem_Ico {b : ℕ} (hb : 1 < b) {n : ℕ} (h_nil : b.digits n ≠ []) (x : ℕ) :
    (b.digits n).getLast h_nil = x ↔
    n ∈ Set.Ico (x * b ^ ((b.digits n).length - 1)) ((x + 1) * b ^ ((b.digits n).length - 1)) := by
  rw [digits_getLast_eq_div_base_pow hb]
  rw [nat_div_eq_iff (Nat.pow_pos <| Nat.zero_lt_of_lt hb)]
  simp

-- TODO: clean up. should be easier... k * factorization ≠ 0?
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

-- If two numbers have the same number of digits, then each must be less than `b` times the other.
lemma lt_base_mul_of_digits_len_eq {b : ℕ} (hb : 1 < b) {x y : ℕ} (h_zero : x ≠ 0 ∨ y ≠ 0)
    (h_len : (Nat.digits b x).length = (Nat.digits b y).length) : y < b * x := by
  -- Since `x, y` have the same number of digits, it suffices to show that either is not zero.
  have ⟨hx, hy⟩ : x ≠ 0 ∧ y ≠ 0 := by
    suffices x ≠ 0 ↔ y ≠ 0 by refine h_zero.elim ?_ ?_ <;> simp [this]
    suffices (b.digits x).length ≠ 0 ↔ (b.digits y).length ≠ 0 by
      simpa [Nat.digits_ne_nil_iff_ne_zero] using this
    rw [h_len]
  -- Use the fact that `b.log (b * n) = b.log n + 1`.
  suffices y < b * b ^ b.log x by
    refine lt_of_lt_of_le this ?_
    gcongr
    exact Nat.pow_log_le_self b hx
  suffices y < b ^ (b.log x + 1) by simpa [pow_succ']
  suffices b.log y < b.log x + 1 from (Nat.lt_pow_iff_log_lt hb hy).mpr this
  rw [Nat.lt_add_one_iff]
  -- This follows from the fact that they have the same number of digits.
  refine ge_of_eq ?_
  simpa [Nat.digits_len, hb, hx, hy] using h_len

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

  -- Properties of the digits which are unaffected by the reversal:
  have h_len : (Nat.digits 10 (k ^ a + 1)).length = (Nat.digits 10 (k ^ b + 1)).length := by
    simpa only [List.length_reverse] using congrArg List.length h_dig
  have h_sum : (Nat.digits 10 (k ^ a + 1)).sum = (Nat.digits 10 (k ^ b + 1)).sum := by
    simpa only [List.sum_reverse] using congrArg List.sum h_dig

  -- We cannot have `10 ≤ k` as `k ^ b + 1` will have more digits than `k ^ a + 1`.
  have hk_lt : k < 10 := by
    contrapose! h_len with hk_ge
    refine ne_of_lt ?_
    exact strictMono_len_digits_succ_pow_of_base_le (by norm_num) hk_ge ha.ne' hb.ne' hab

  -- Observe that the function `k ^ · + 1` is strictly increasing, hence injective.
  have hf_strictMono : StrictMono (k ^ · + 1) := (pow_right_strictMono₀ hk_gt).add_const 1
  -- The number `k ^ a + 1` must be at *least* 10, otherwise its digits are a (trivial) palindrome
  -- and therefore it is equal to `k ^ b + 1`.
  have hfa_ge : 10 ≤ k ^ a + 1 := by
    contrapose! h_ne with hfa
    suffices k ^ a + 1 = k ^ b + 1 from hf_strictMono.injective this
    refine Nat.digits.injective 10 ?_
    have ha_dig := Nat.digits_of_lt 10 _ (by simp) hfa
    rw [← List.reverse_inj, ← h_dig, ha_dig]
    simp
  -- Furthermore, `k ^ a + 1` cannot be equal to 10: the first digit of `k ^ b + 1` would be 0.
  have hfa_ne : k ^ a + 1 ≠ 10 := by
    refine mt (fun ha_pow ↦ ?_) (Nat.getLast_digit_ne_zero 10 (m := k ^ b + 1) (by simp))
    suffices Nat.digits 10 (k ^ b + 1) = [1, 0] by simp [this, -Nat.digits_of_two_le_of_pos]
    calc _
    _ = (Nat.digits 10 (k ^ a + 1)).reverse := List.reverse_eq_iff.mp h_dig.symm
    _ = _ := by simp [ha_pow]
  -- Combining these, we have `10 < k ^ a + 1`.
  have hfa_gt : 10 < k ^ a + 1 := Nat.lt_of_le_of_ne hfa_ge hfa_ne.symm

  -- Since `k ^ a + 1 < k ^ b + 1` have the same number of digits, we can also bound
  -- `k ^ b + 1` from above using `10 * (k ^ a + 1)`.
  have hfb_lt_mul_hfa : k ^ b + 1 < 10 * (k ^ a + 1) :=
    lt_base_mul_of_digits_len_eq (by norm_num) (by simp) h_len

  -- From this, we determine an upper bound on `b`.
  have hba : b ≤ 2 * a := by
    -- Show that `2 * a < b` leads to a contradiction.
    refine le_of_not_lt fun hab ↦ ?_
    -- To find a contradiction, we will prove `k ^ a < 10`.
    suffices k ^ a < 10 from hfa_gt.not_le this
    -- This follows from `k ^ a * (k ^ a + 1) ≤ k ^ b < 10 * (k ^ a + 1)`.
    -- In fact we can prove the strict version of this inequality.
    suffices k ^ a * (k ^ a + 1) < k ^ b + 1 from
      Nat.lt_of_mul_lt_mul_right (lt_trans this hfb_lt_mul_hfa)
    calc _
    _ ≤ k ^ a * k ^ (a + 1) := Nat.mul_le_mul_left (k ^ a) (Nat.pow_lt_pow_succ hk_gt)
    _ = k ^ (2 * a + 1) := by ring
    _ ≤ k ^ b := Nat.pow_le_pow_of_le hk_gt hab
    _ < _ := lt_add_one _

  -- This is equivalent to `b - a ≤ a`.
  -- We use this to bound `k ^ (b - a) ≤ k ^ a`.
  have hba_sub : b - a ≤ a := by
    refine Nat.sub_le_of_le_add ?_
    simpa [two_mul] using hba

  -- Introduce a constant `z = k ^ (b - a) - 1` and show that `z * f a < f b`.
  let z := k ^ (b - a) - 1
  have hz : z ≠ 0 := by
    suffices 1 < k ^ (b - a) from Nat.sub_ne_zero_iff_lt.mpr this
    refine lt_of_lt_of_le hk_gt (Nat.le_self_pow ?_ k)
    exact Nat.sub_ne_zero_iff_lt.mpr hab
  -- Provide an expression for `z` in `ℤ` using non-truncated subtraction.
  have hz_int : (z : ℤ) = k ^ (b - a) - 1 := by
    suffices 1 ≤ k ^ (b - a) by simp [Nat.cast_sub this]
    exact Nat.one_le_pow _ k (Nat.zero_lt_of_lt hk_gt)
  -- Show that `z * (k ^ a + 1) < k ^ b + 1`.
  have hz_mul_fa_lt_fb : z * (k ^ a + 1) < k ^ b + 1 := by
    -- Here it will be easier to work in `ℤ`.
    suffices (z : ℤ) * (k ^ a + 1) < k ^ b + 1 by simpa [← Int.ofNat_lt]
    rw [hz_int]
    calc  _
    _ = (k ^ (b - a + a) + k ^ (b - a) - k ^ a - 1 : ℤ) := by ring
    _ = (k ^ b + k ^ (b - a) - k ^ a - 1 : ℤ) := by rw [Nat.sub_add_cancel hab.le]
    _ ≤ (k ^ b - 1 : ℤ) := by
      suffices k ^ (b - a) ≤ k ^ a by simpa using Int.ofNat_le.mpr this
      exact Nat.pow_le_pow_of_le hk_gt hba_sub
    _ < _ := by linarith

  -- We can see that `z < 10` by combining lower and upper bounds on `k ^ b + 1`:
  -- `z * (k ^ a + 1) < k ^ b + 1 < 10 * (k ^ a + 1)`.
  have hz_lt : z < 10 := by simpa using lt_trans hz_mul_fa_lt_fb hfb_lt_mul_hfa
  -- We can further establish that `z ≠ 9`.
  have hz_ne : z ≠ 9 := by
    unfold z
    suffices k ^ (b - a) ≠ 10 by simpa
    -- Since 10 contains factors with multiplicity one, the only way to satisfy
    -- `k ^ r = 10` is with `k = 10`. This is a contradiction since `k < 10`.
    refine mt (fun h ↦ ?_) hk_lt.ne
    -- TODO: clean up?
    refine (pow_eq_iff_eq_of_factorization_eq_one 10 2 k Nat.prime_two ?_).mp ⟨_, h⟩
    suffices Nat.factorization (2 * 5) 2 = 1 by simpa
    rw [Nat.factorization_mul_of_coprime] <;> norm_num
  -- Combine these to obtain `z < 9`.
  have hz_lt : z < 9 := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hz_lt) hz_ne

  -- Note that `z` multiplied by `k ^ a` gives `f b - f a`.
  have hz_mul_eq_sub : z * k ^ a = (k ^ b + 1) - (k ^ a + 1) := by
    unfold z
    calc _
    _ = k ^ (b - a + a) - k ^ a := by simp [pow_add, tsub_mul]
    _ = _ := by simp [hab.le]
  -- Since these numbers have the same digit sum, their difference is divisible by 9.
  have hz_dvd : 9 ∣ z * k ^ a := by
    rw [hz_mul_eq_sub]
    exact nine_dvd_tsub_of_digits_eq h_sum

  -- Since `z < 9`, this means that `k ^ a` (and hence `k`) must be divisible by 3.
  have hk : 3 ∣ k := by
    suffices 3 ∣ k ^ a from Nat.prime_three.dvd_of_dvd_pow this
    change 3 ^ 2 ∣ z * k ^ a at hz_dvd
    -- We can't put both 3's in `z < 9`, hence we must have at least `3 ∣ k ^ a`.
    -- Need both factors to be non-zero for factorization.
    have hk_pow : k ^ a ≠ 0 := pow_ne_zero _ (Nat.not_eq_zero_of_lt hk_gt)
    rw [Nat.prime_three.dvd_iff_one_le_factorization hk_pow]
    rw [Nat.prime_three.pow_dvd_iff_le_factorization (mul_ne_zero hz hk_pow),
      Nat.factorization_mul hz hk_pow, Finsupp.add_apply] at hz_dvd
    -- It will suffice to show that the multiplicity of 3 in `z` does not exceed one.
    suffices z.factorization 3 < 2 by linarith
    suffices ¬3 ^ 2 ∣ z by
      rw [Nat.prime_three.pow_dvd_iff_le_factorization hz] at this
      simpa using this
    exact Nat.not_dvd_of_pos_of_lt (Nat.zero_lt_of_ne_zero hz) hz_lt

  -- Since we have `1 < k < 10` and `3 ∣ k`, there are only three possibilities.
  have hk : k = 3 ∨ k = 6 ∨ k = 9 := by
    revert hk
    interval_cases k <;> norm_num
  -- It suffices to exclude the cases `k = 6` and `k = 9`.
  refine hk.resolve_right fun hk ↦ ?_

  -- Since `z = k ^ (b - a) - 1` and `6 ≤ k`, we know `5 ≤ z`.
  have hz : 5 ≤ z := by
    suffices 6 ≤ k ^ (b - a) from le_tsub_of_add_le_right this
    suffices 6 ≤ k by
      refine le_trans this (Nat.le_self_pow ?_ k)
      exact Nat.sub_ne_zero_iff_lt.mpr hab
    suffices ∀ k, k = 6 ∨ k = 9 → 6 ≤ k from this k hk
    simp
  -- This provides a new inequality relating `f a` and `f b`.
  replace hz_mul_fa_lt_fb : 5 * (k ^ a + 1) < k ^ b + 1 := by
    refine lt_of_le_of_lt ?_ hz_mul_fa_lt_fb
    gcongr

  -- Since `5 * f a < f b`, the first digit of `f a` must be 1.
  -- Otherwise `f b` will have more digits than `f a`.
  have hfa_nil : Nat.digits 10 (k ^ a + 1) ≠ [] := by simp
  have hfa_getLast : (Nat.digits 10 (k ^ a + 1)).getLast hfa_nil = 1 := by
    -- Rewrite equality of the first digit as membership in an interval.
    rw [digits_getLast_eq_iff_mem_Ico (by norm_num)]
    simp only [one_mul, Nat.reduceAdd, Set.mem_Ico]
    constructor
    · -- The lower bound for the first digit to be 1 is simply the order of magnitude.
      -- Multiply by 10 on both sides to match the form of `Nat.base_pow_length_digits_le`.
      suffices 10 ^ ((Nat.digits 10 (k ^ a + 1)).length - 1 + 1) ≤ 10 * (k ^ a + 1) by
        simpa [Nat.pow_succ']
      rw [Nat.sub_add_cancel (by simp)]
      exact Nat.base_pow_length_digits_le 10 _ (by norm_num) (by simp)
    · -- For the upper bound, we need to combine the constraints
      -- `5 * f a < f b < 10 ^ (m + 1)` and `10 ^ m ≤ f a`,
      -- where `m + 1` is the number of digits.
      -- First multiply by 5 on either side.
      refine Nat.lt_of_mul_lt_mul_left (a := 5) ?_
      -- Then combine the new inequality with the upper bound from the number of digits of `b`.
      refine lt_trans hz_mul_fa_lt_fb ?_
      convert @Nat.lt_base_pow_length_digits 10 (k ^ b + 1) (by norm_num) using 1
      rw [h_len]
      calc _
      _ = 10 ^ ((Nat.digits 10 (k ^ b + 1)).length - 1 + 1) := by ring
      _ = _ := by simp

  -- Due to the reverse relation, this means that the last digit of `f b = k ^ b + 1` is 1.
  simp only [h_dig, List.getLast_reverse] at hfa_getLast
  -- This implies that the last digit of `k ^ b = k ^ b + 1 - 1` is 0.
  -- This provides the contradiction: we cannot have `10 ∣ k ^ b` with `k ∈ {6, 9}` and `b ≠ 0`.
  have h_not_ten_dvd : ¬10 ∣ k ^ b := by
    -- This follows from the fact that `5` is not a divisor of `k`.
    change ¬2 * 5 ∣ k ^ b
    suffices ¬5 ∣ k ^ b from mt dvd_of_mul_left_dvd this
    suffices ¬5 ∣ k from mt Nat.prime_five.dvd_of_dvd_pow this
    suffices ∀ k, k = 6 ∨ k = 9 → ¬5 ∣ k from this k hk
    norm_num
  refine h_not_ten_dvd ?_
  suffices k ^ b ≡ 0 [MOD 10] from Nat.dvd_of_mod_eq_zero this
  suffices (k ^ b + 1) % 10 = 1 from Nat.ModEq.add_right_cancel' 1 this
  simpa using hfa_getLast
