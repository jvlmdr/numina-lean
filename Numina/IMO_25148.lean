-- https://cloud.kili-technology.com/label/projects/review/cmauuk3x3000f1ray7uzjtqp7

import Mathlib

open Nat List

/- Each positive integer $a$ undergoes the following procedure in order to obtain
the number $d = d(a)$:
(1) move the last digit of $a$ to the first position to obtain the number $b$;
(2) square $b$ to obtain the number $c$;
(3) move the first digit of $c$ to the end to obtain the number $d$.
(All the numbers in the problem are considered to be represented in base 10.)
For example, for $a=2003$, we have $b=3200, c=10240000$, and $d = 02400001 = 2400001 = d(2003)$.
Find all numbers $a$ for which $d(a) = a^{2}$. -/

def d (a : ℕ) : ℕ :=
  ofDigits 10 <| rotateRight <| digits 10 <|
  (ofDigits 10 <| rotate (n := 1) <| digits 10 a) ^ 2

-- Rotate a single element right.
lemma rotateRight_concat (l : List ℕ) (x : ℕ) :
    rotateRight (l ++ [x]) = x :: l := by
  unfold rotateRight
  cases l <;> simp

-- Rotate a single element left.
lemma rotate_cons (l : List ℕ) (x : ℕ) :
    (x :: l).rotate 1 = l ++ [x] := by
  unfold rotate
  cases l <;> simp

-- Lower bound on the integer log of a square.
lemma le_log_sq {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : 2 * log b n ≤ log b (n ^ 2) := by
  refine le_log_of_pow_le hb ?_
  rw [mul_comm, pow_mul]
  gcongr
  exact pow_log_le_self b hn

-- Upper bound on the integer log of a square.
lemma log_sq_le {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b (n ^ 2) ≤ 2 * log b n + 1 := by
  suffices log b (n ^ 2) < 2 * (log b n + 1) from le_of_lt_succ this
  refine Nat.log_lt_of_lt_pow (by simpa) ?_
  rw [mul_comm, pow_mul]
  gcongr
  exact lt_pow_succ_log_self hb n

-- The log of a square is either `2 log n` or `2 log n + 1`.
lemma log_sq_eq_or_eq {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b (n ^ 2) = 2 * log b n ∨ log b (n ^ 2) = 2 * log b n + 1 :=
  le_and_le_add_one_iff.mp ⟨le_log_sq hb hn, log_sq_le hb hn⟩

-- Lower bound on the number of digits in a square.
lemma le_len_digits_sq {b : ℕ} (hb : 1 < b) (n : ℕ) :
    2 * (digits b n).length ≤ (digits b (n ^ 2)).length + 1 := by
  cases n with
  | zero => simp
  | succ n => simpa [digits_len, hb, mul_add] using le_log_sq hb n.add_one_ne_zero

-- Upper bound on the number of digits in a square.
lemma len_digits_sq_le {b : ℕ} (hb : 1 < b) (n : ℕ) :
    (digits b (n ^ 2)).length ≤ 2 * (digits b n).length := by
  cases n with
  | zero => simp
  | succ n => simpa [digits_len, hb, mul_add] using log_sq_le hb n.add_one_ne_zero

-- If `n` has `k + 1` digits and `n ^ 2` has `m + 1` digits, then `m` is either `2 k` or `2 k + 1`.
lemma len_eq_or_eq_of_digits_eq_concat {b : ℕ} (hb : 1 < b) {n : ℕ}
    {lx : List ℕ} {x : ℕ} (hx : digits b n = lx ++ [x])
    {ly : List ℕ} {y : ℕ} (hy : digits b (n ^ 2) = ly ++ [y]) :
    ly.length = 2 * lx.length ∨ ly.length = 2 * lx.length + 1 := by
  have hn_zero : n ≠ 0 := by
    suffices digits b n ≠ [] from digits_ne_nil_iff_ne_zero.mp this
    simp [hx]
  suffices log b (n ^ 2) = ly.length ∧ log b n = lx.length by
    rw [← this.1, ← this.2]
    exact log_sq_eq_or_eq hb hn_zero
  constructor
  · suffices log b (n ^ 2) + 1 = ly.length + 1 by simpa using this
    convert congrArg length hy using 1
    · simp [digits_len, hb, hn_zero]
    · simp
  · suffices log b n + 1 = lx.length + 1 by simpa using this
    convert congrArg length hx using 1
    · simp [digits_len, hb, hn_zero]
    · simp

-- Given that `n` has `k + 1` digits and leading digit `x`, it must lie in the range
-- `x * b ^ k ≤ n < (x + 1) * b ^ k`.
-- This is similar to `Nat.log_eq_iff` except it accounts for the leading digit.
lemma mem_Ico_of_digits_eq_concat {b : ℕ} (hb : 1 < b) (n x : ℕ) (l : List ℕ)
    (hn_digits : digits b n = l ++ [x]) :
    n ∈ Set.Ico (x * b ^ l.length) ((x + 1) * b ^ l.length) := by
  have hn : n = x * b ^ l.length + ofDigits b l := by
    convert congrArg (ofDigits b) hn_digits using 1
    · simp [ofDigits_digits]
    · simp only [ofDigits_append, ofDigits_singleton]
      ring
  rw [hn]
  refine ⟨?_, ?_⟩
  · simp
  · suffices ofDigits b l < b ^ l.length by simpa [add_mul] using this
    refine ofDigits_lt_base_pow_length hb fun d hd ↦ ?_
    suffices d ∈ digits b n from digits_lt_base hb this
    simpa [hn_digits] using mem_append_left [x] hd

-- When we square a `(k + 1)`-digit number `n` with leading digit `x`, the result may have either
-- `2 k` or `2 k + 1` digits. The map from `n` to the leading digit of `n ^ 2` is monotonic except
-- when the number of digits in `n ^ 2` transitions from `2 k` to `2 k + 1`.

-- If `n ^ 2` has `2 k` digits, then its leading digit `y` must be at least `x ^ 2` and
-- less than `(x + 1) ^ 2`.
lemma mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul {b : ℕ} (hb : 1 < b) (n : ℕ)
    {lx : List ℕ} {x : ℕ} (hx : digits b n = lx ++ [x])
    {ly : List ℕ} {y : ℕ} (hy : digits b (n ^ 2) = ly ++ [y])
    (h_len : ly.length = 2 * lx.length) :
    y ∈ Finset.Ico (x ^ 2) ((x + 1) ^ 2) := by
  have hx_mem := mem_Ico_of_digits_eq_concat hb n x lx hx
  have hy_mem := mem_Ico_of_digits_eq_concat hb (n ^ 2) y ly hy
  rw [h_len] at hy_mem
  simp only [Finset.mem_inter, Finset.mem_Ico]
  refine ⟨?_, ?_⟩
  · suffices x ^ 2 < y + 1 from le_of_lt_succ this
    suffices x ^ 2 * b ^ (2 * lx.length) < (y + 1) * b ^ (2 * lx.length) from
      Nat.lt_of_mul_lt_mul_right this
    convert lt_of_le_of_lt (Nat.pow_le_pow_left hx_mem.1 2) hy_mem.2 using 1
    ring
  · suffices y * b ^ (2 * lx.length) < (x + 1) ^ 2 * b ^ (2 * lx.length) from
      Nat.lt_of_mul_lt_mul_right this
    convert lt_of_le_of_lt hy_mem.1 (Nat.pow_lt_pow_left hx_mem.2 two_ne_zero) using 1
    ring

-- If `n ^ 2` has `2 k + 1` digits, then its leading digit `y` must be at least `x ^ 2 / b` and
-- less than `(x + 1) ^ 2 ⌈/⌉ b`, where `⌈/⌉` denotes division with upwards rounding.
lemma mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul_add_one {b : ℕ} (hb : 1 < b) (n : ℕ)
    {lx : List ℕ} {x : ℕ} (hx : digits b n = lx ++ [x])
    {ly : List ℕ} {y : ℕ} (hy : digits b (n ^ 2) = ly ++ [y])
    (h_len : ly.length = 2 * lx.length + 1) :
    y ∈ Finset.Ico (x ^ 2 / b) ((x + 1) ^ 2 ⌈/⌉ b) := by
  have hx_mem := mem_Ico_of_digits_eq_concat hb n x lx hx
  have hy_mem := mem_Ico_of_digits_eq_concat hb (n ^ 2) y ly hy
  rw [h_len] at hy_mem
  simp only [← Finset.Ico_inter_Ico, Finset.mem_inter, Finset.mem_Ico]
  refine ⟨?_, ?_⟩
  · suffices x ^ 2 / b < y + 1 from le_of_lt_succ this
    rw [div_lt_iff_lt_mul (zero_lt_of_lt hb)]
    suffices x ^ 2 * b ^ (2 * lx.length) < (y + 1) * b * b ^ (2 * lx.length) from
      Nat.lt_of_mul_lt_mul_right this
    convert lt_of_le_of_lt (Nat.pow_le_pow_left hx_mem.1 2) hy_mem.2 using 1 <;> ring
  · rw [ceilDiv_eq_add_pred_div]
    change y + 1 ≤ ((x + 1) ^ 2 + b - 1) / b
    rw [Nat.le_div_iff_mul_le (zero_lt_of_lt hb)]
    suffices y * b + 1 ≤ (x + 1) ^ 2 by
      convert add_le_add_right this (b - 1) using 1
      · rw [← add_tsub_assoc_of_le hb.le]
        simp [add_mul]
      · rw [add_tsub_assoc_of_le hb.le]
    change y * b < (x + 1) ^ 2
    suffices y * b * b ^ (2 * lx.length) < (x + 1) ^ 2 * b ^ (2 * lx.length) from
      Nat.lt_of_mul_lt_mul_right this
    convert lt_of_le_of_lt hy_mem.1 (Nat.pow_lt_pow_left hx_mem.2 two_ne_zero) using 1 <;> ring

-- Determine that `m = 2 k` using the condition on the leading digit.
lemma len_eq_two_mul_of_digits_sq_eq_concat_of_not_mem_Ico {b : ℕ} (hb : 1 < b) {n : ℕ}
    {lx : List ℕ} {x : ℕ} (hn_dig : digits b n = lx ++ [x])
    {ly : List ℕ} {y : ℕ} (hn2_dig : digits b (n ^ 2) = ly ++ [y])
    (hy : y ∉ Finset.Ico (x ^ 2 / b) ((x + 1) ^ 2 ⌈/⌉ b)) :
    ly.length = 2 * lx.length := by
  contrapose! hy with hy_len
  refine mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul_add_one hb n hn_dig hn2_dig ?_
  exact (len_eq_or_eq_of_digits_eq_concat hb hn_dig hn2_dig).resolve_left hy_len

-- Determine that `m = 2 k + 1` using the condition on the leading digit.
lemma len_eq_two_mul_add_one_of_digits_sq_eq_concat_of_not_mem_Ico {b : ℕ} (hb : 1 < b) {n : ℕ}
    {lx : List ℕ} {x : ℕ} (hn_dig : digits b n = lx ++ [x])
    {ly : List ℕ} {y : ℕ} (hn2_dig : digits b (n ^ 2) = ly ++ [y])
    (hy : y ∉ Finset.Ico (x ^ 2) ((x + 1) ^ 2)) :
    ly.length = 2 * lx.length + 1 := by
  contrapose! hy with hy_len
  refine mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul hb n hn_dig hn2_dig ?_
  exact (len_eq_or_eq_of_digits_eq_concat hb hn_dig hn2_dig).resolve_right hy_len

-- There are two (mutually exclusive) cases for the leading digit and length of the square.
lemma digits_sq_of_eq_concat {b : ℕ} (hb : 1 < b) (n : ℕ)
    {lx : List ℕ} {x : ℕ} (hn_dig : digits b n = lx ++ [x])
    {ly : List ℕ} {y : ℕ} (hn2_dig : digits b (n ^ 2) = ly ++ [y]) :
    ly.length = 2 * lx.length ∧ y ∈ Finset.Ico (x ^ 2) ((x + 1) ^ 2) ∨
    ly.length = 2 * lx.length + 1 ∧ y ∈ Finset.Ico (x ^ 2 / b) ((x + 1) ^ 2 ⌈/⌉ b) := by
  refine (len_eq_or_eq_of_digits_eq_concat hb hn_dig hn2_dig).imp ?_ ?_
  · refine fun hy_len ↦ ⟨hy_len, ?_⟩
    exact mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul hb n hn_dig hn2_dig hy_len
  · refine fun hy_len ↦ ⟨hy_len, ?_⟩
    exact mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul_add_one hb n hn_dig hn2_dig hy_len

-- Determine the number of digits in the square from a lower bound on the first digit.
lemma len_digits_sq_eq_of_le_getLast_sq {b : ℕ} (hb : 1 < b) (n : ℕ)
    (hx : ∀ h, b ≤ (digits b n).getLast h ^ 2) :
    (digits b (n ^ 2)).length = 2 * (digits b n).length := by
  cases eq_or_ne n 0 with
  | inl hn => simp [hn]
  | inr hn =>
    have hn_nil : digits b n ≠ [] := digits_ne_nil_iff_ne_zero.mpr hn
    have hn2_nil : digits b (n ^ 2) ≠ [] := digits_ne_nil_iff_ne_zero.mpr (pow_ne_zero 2 hn)
    specialize hx hn_nil
    obtain ⟨lx, x, hn_dig⟩ : ∃ (l : List ℕ) (x : ℕ), digits b n = l ++ [x] :=
      ⟨_, _, .symm <| dropLast_concat_getLast <| hn_nil⟩
    obtain ⟨ly, y, hn2_dig⟩ : ∃ (l : List ℕ) (x : ℕ), digits b (n ^ 2) = l ++ [x] :=
      ⟨_, _, .symm <| dropLast_concat_getLast <| hn2_nil⟩
    suffices ly.length = 2 * lx.length + 1 by simpa [hn2_dig, hn_dig, mul_add]
    refine len_eq_two_mul_add_one_of_digits_sq_eq_concat_of_not_mem_Ico hb hn_dig hn2_dig ?_
    rw [Finset.mem_Ico]
    refine not_and_of_not_left _ ?_
    rw [not_le]
    calc _
    _ < b := by
      suffices y ∈ digits b (n ^ 2) from digits_lt_base hb this
      simp [hn2_dig]
    _ ≤ x ^ 2 := by simpa [hn_dig] using hx

-- Determine the number of digits in the square from an upper bound on the first digit.
lemma len_digits_sq_eq_of_getLast_add_one_sq_lt {b : ℕ} (hb : 1 < b) (n : ℕ)
    (hx : ∀ h, ((digits b n).getLast h + 1) ^ 2 < b) :
    (digits b (n ^ 2)).length = 2 * (digits b n).length - 1 := by
  cases eq_or_ne n 0 with
  | inl hn => simp [hn]
  | inr hn =>
    have hn_nil : digits b n ≠ [] := digits_ne_nil_iff_ne_zero.mpr hn
    have hn2_nil : digits b (n ^ 2) ≠ [] := digits_ne_nil_iff_ne_zero.mpr (pow_ne_zero 2 hn)
    specialize hx hn_nil
    obtain ⟨lx, x, hn_dig⟩ : ∃ (l : List ℕ) (x : ℕ), digits b n = l ++ [x] :=
      ⟨_, _, .symm <| dropLast_concat_getLast <| hn_nil⟩
    obtain ⟨ly, y, hn2_dig⟩ : ∃ (l : List ℕ) (x : ℕ), digits b (n ^ 2) = l ++ [x] :=
      ⟨_, _, .symm <| dropLast_concat_getLast <| hn2_nil⟩
    suffices ly.length = 2 * lx.length by simpa [hn2_dig, hn_dig, mul_add]
    refine len_eq_two_mul_of_digits_sq_eq_concat_of_not_mem_Ico hb hn_dig hn2_dig ?_
    rw [Finset.mem_Ico]
    refine not_and_of_not_right _ ?_
    rw [not_lt, ceilDiv_le_iff_le_mul (zero_lt_of_lt hb)]
    have hx : (x + 1) ^ 2 < b := by simpa [hn_dig] using hx
    have hy : y = (digits b (n ^ 2)).getLast hn2_nil := by simp [hn2_dig]
    calc _
    _ ≤ b := hx.le
    _ ≤ _ := by
      refine Nat.le_mul_of_pos_right b ?_
      refine zero_lt_of_ne_zero ?_
      simpa [hy] using getLast_digit_ne_zero b (pow_ne_zero 2 hn)


-- The number constructed from repeated zeros is zero, regardless of base or length.
lemma ofDigits_replicate_zero (b n : ℕ) : ofDigits b (replicate n 0) = 0 := by
  induction n with
  | zero => simp
  | succ n IH => simp [replicate_succ, ofDigits_cons, IH]

-- Taking `digits` of `ofDigits` gives the same list without trailing zeros.
lemma reverse_digits_ofDigits_eq_dropWhile_reverse {b : ℕ} (hb : 1 < b) (l : List ℕ)
    (hl : ∀ x ∈ l, x < b) :
    reverse (digits b (ofDigits b l)) = dropWhile (· = 0) l.reverse := by
  induction l using reverseRecOn with
  | nil => simp
  | append_singleton l x IH =>
    cases x with
    | zero => simpa [ofDigits_append] using IH fun i hi ↦ hl i (mem_append_left [0] hi)
    | succ x => simpa using digits_ofDigits b hb (l ++ [x.succ]) hl (by simp)

-- Taking `digits` of `ofDigits` gives a list that is no longer than the original list.
lemma digits_ofDigits_len_le_len (b : ℕ) (hb : 1 < b) (l : List ℕ) (hl : ∀ x ∈ l, x < b) :
    (digits b (ofDigits b l)).length ≤ l.length := by
  suffices (digits b (ofDigits b l)).reverse.length ≤ l.reverse.length by simpa
  rw [reverse_digits_ofDigits_eq_dropWhile_reverse hb l hl]
  exact (dropWhile_sublist _).length_le

-- The number of trailing zeros in a list of digits.
lemma takeWhile_eq_zero_reverse_eq_replicate_sub_length_digits_ofDigits {b : ℕ} (hb : 1 < b)
    (l : List ℕ) (hl : ∀ x ∈ l, x < b) :
    takeWhile (· = 0) l.reverse = replicate (l.length - (digits b (ofDigits b l)).length) 0 := by
  induction l using reverseRecOn with
  | nil => simp
  | append_singleton l x IH =>
    cases x with
    | zero =>
      replace hl : ∀ x ∈ l, x < b := fun x hx ↦ hl x (mem_append_left [0] hx)
      simp [ofDigits_append, IH hl, replicate_succ,
        Nat.sub_add_comm (digits_ofDigits_len_le_len b hb l hl)]
    | succ x => simp [digits_ofDigits b hb (l ++ [x.succ]) hl (by simp)]

-- A list of digits can be restored by appending zeros.
lemma digits_ofDigits_append_zeroes_eq_self {b : ℕ} (hb : 1 < b) (l : List ℕ)
    (hl : ∀ x ∈ l, x < b) :
    digits b (ofDigits b l) ++ replicate (l.length - (digits b (ofDigits b l)).length) 0 = l := by
  rw [← reverse_inj]
  simp only [reverse_append, reverse_replicate]
  convert takeWhile_append_dropWhile (p := (· = 0)) (l := l.reverse) using 2
  · rw [takeWhile_eq_zero_reverse_eq_replicate_sub_length_digits_ofDigits hb l hl]
  · rw [reverse_digits_ofDigits_eq_dropWhile_reverse hb l hl]


lemma ten_pow_eq_nine_mul_replicate_add_one (n : ℕ) :
    10 ^ n = 9 * ofDigits 10 (replicate n 1) + 1 := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [Nat.pow_succ, IH, replicate_succ, ofDigits_cons]
    ring

lemma ten_pow_sub_one_eq_nine_mul (n : ℕ) :
    10 ^ n - 1 = 9 * ofDigits 10 (replicate n 1) :=
  Nat.sub_eq_of_eq_add (ten_pow_eq_nine_mul_replicate_add_one n)

-- The key lemma that lets us obtain an explicit form for `x`.
lemma eq_iff_digits_eq_replicate_two_mul {s k : ℕ} (hs_ne : s ≠ 0) (hs_lt : 2 * s < 10) (x : ℕ) :
    x + 2 * s * 10 ^ k = 2 * s + 10 * x ↔ digits 10 x = replicate k (2 * s) := by
  calc x + 2 * s * 10 ^ k = 2 * s + 10 * x
  _ ↔ 2 * s * 10 ^ k + x = 10 * x + 2 * s := by simp [add_comm]
  _ ↔ 2 * s * 10 ^ k = 10 * x + 2 * s - x := by
    rw [eq_tsub_iff_add_eq_of_le]
    refine le_add_right ?_
    exact Nat.le_mul_of_pos_left x (by norm_num)
  _ ↔ 2 * s * 10 ^ k = 10 * x - x + 2 * s := by
    rw [Nat.sub_add_comm]
    exact Nat.le_mul_of_pos_left x (by norm_num)
  _ ↔ 2 * s * 10 ^ k - 2 * s = 10 * x - x := by
    rw [tsub_eq_iff_eq_add_of_le]
    exact Nat.le_mul_of_pos_right (2 * s) (by simp)
  _ ↔ 2 * s * (10 ^ k - 1) = (10 - 1) * x := by
    simp only [mul_tsub, tsub_mul]
    simp
  _ ↔ 2 * s * (ofDigits 10 (replicate k 1)) * 9 = x * 9 := by
    simp [ten_pow_sub_one_eq_nine_mul, mul_comm _ 9, ← mul_assoc]
  _ ↔ 2 * s * (ofDigits 10 (replicate k 1)) = x := Nat.mul_left_inj (by norm_num)
  _ ↔ _ := by
    simp only [mul_ofDigits, map_replicate, mul_one]
    constructor
    · intro h
      convert congrArg (digits 10) h.symm using 1
      refine (digits_ofDigits 10 (by norm_num) _ ?_ ?_).symm
      · simp [hs_lt]
      · simp [hs_ne]
    · intro h
      convert congrArg (ofDigits 10) h.symm
      simp [ofDigits_digits]


-- Defined in analogy to `List.exists_cons_of_ne_nil`.
lemma exists_concat_of_ne_nil {α : Type*} {l : List α} :
    l ≠ [] → ∃ (x : α) (lx : List α), l = lx ++ [x] := by
  intro hl
  obtain ⟨x, lx, h⟩ := exists_cons_of_ne_nil (reverse_ne_nil_iff.mpr hl)
  exact ⟨x, lx.reverse, reverse_eq_cons_iff.mp h⟩


theorem number_theory_25148 {a : ℕ} (ha : a ≠ 0) :
    d a = a ^ 2 ↔ a ∈ {1, 2, 3} ∪ Set.range (fun n ↦ ofDigits 10 (1 :: replicate (n + 1) 2)) := by
  unfold d

  calc _
  -- Introduce variables for `b` and the digits of `a` and `c = b ^ 2`.
  _ ↔ ∃ (b : ℕ) (la lc : List ℕ),
      digits 10 a = la ∧ b = ofDigits 10 (la.rotate 1) ∧
      digits 10 (b ^ 2) = lc ∧ a ^ 2 = ofDigits 10 lc.rotateRight := by
    simp only [eq_comm (a := a ^ 2)]
    simp

  -- Separate the digit being moved from the rest of the list.
  _ ↔ ∃ (b : ℕ) (la lc : List ℕ) (s f : ℕ) (lx ly : List ℕ),
      digits 10 a = la ∧ b = ofDigits 10 (la.rotate 1) ∧
      digits 10 (b ^ 2) = lc ∧ a ^ 2 = ofDigits 10 lc.rotateRight ∧
      la = s :: lx ∧ lc = ly ++ [f] := by
    refine exists₃_congr fun b la lc ↦ ?_
    simp only [exists_and_left, exists_and_right, and_congr_right_iff, iff_self_and]
    intro ha_dig hb hb2_dig ha2
    constructor
    · refine exists_cons_of_ne_nil ?_
      rw [← ha_dig]
      exact digits_ne_nil_iff_ne_zero.mpr ha
    · refine exists_concat_of_ne_nil ?_
      contrapose! ha with hlc
      simpa [hlc] using ha2

  -- Re-order variables and eliminate `la, lc`; rewrite rotations.
  _ ↔ ∃ (b s f : ℕ) (lx ly : List ℕ) (la lc : List ℕ),
      ((digits 10 a = la ∧ b = ofDigits 10 (la.rotate 1)) ∧ la = s :: lx) ∧
      (digits 10 (b ^ 2) = lc ∧ a ^ 2 = ofDigits 10 lc.rotateRight) ∧ lc = ly ++ [f] := by
    refine exists_congr fun b ↦ ?_
    constructor
    · intro ⟨la, lc, s, f, lx, ly, ha, hb, hb2, ha2, hla, hlc⟩
      exact ⟨s, f, lx, ly, la, lc, ⟨⟨ha, hb⟩, hla⟩, ⟨hb2, ha2⟩, hlc⟩
    · intro ⟨s, f, lx, ly, la, lc, ⟨⟨ha, hb⟩, hla⟩, ⟨hb2, ha2⟩, hlc⟩
      exact ⟨la, lc, s, f, lx, ly, ha, hb, hb2, ha2, hla, hlc⟩

  _ ↔ ∃ (b s f : ℕ) (lx ly : List ℕ),
      (digits 10 a = s :: lx ∧ b = ofDigits 10 (lx ++ [s])) ∧
      digits 10 (b ^ 2) = ly ++ [f] ∧ a ^ 2 = ofDigits 10 (f :: ly) := by
    simp [rotate_cons, rotateRight_concat]

  -- We have `s ≠ 0` and hence `digits 10 b = lx ++ [s]`.
  -- If `s = 0`, then `a` has `k + 1` digits, `b` has at most `k` digits,
  -- `c = b ^ 2` has at most `2 * k` digits, and therefore so does `d` (where `k = lx.length`).
  -- However, `d = a ^ 2` has at least `2 * k + 1` digits.
  _ ↔ ∃ (b s f : ℕ) (lx ly : List ℕ),
      (digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s]) ∧
      digits 10 (b ^ 2) = ly ++ [f] ∧ a ^ 2 = ofDigits 10 (f :: ly) := by
    refine exists₃_congr fun b s f ↦ ?_
    simp only [exists_and_left, exists_and_right, and_congr_left_iff, forall_exists_index, and_imp]
    intro ly hb2 ha2
    refine exists_congr fun lx ↦ ?_
    simp only [and_congr_right_iff]
    intro ha_dig  -- TODO: rename `ha` to `ha_zero`
    -- The reverse direction is trivial.
    refine ⟨?_, fun hb ↦ hb ▸ (ofDigits_digits 10 b).symm⟩
    intro hb
    suffices s ≠ 0 by
      rw [hb]
      refine digits_ofDigits 10 (by norm_num) _ ?_ ?_
      · intro i hi
        suffices i ∈ digits 10 a from digits_lt_base' this
        simpa [ha_dig, or_comm] using hi
      · simpa using this
    -- Establish contradiction when `s = 0`.
    intro hs
    -- Compare the minimum number of digits obtained by squaring `a`...
    suffices (digits 10 (a ^ 2)).length ≤ 2 * lx.length by
      refine this.not_lt ?_
      rw [lt_iff_add_one_le]
      simpa [ha_dig, mul_add] using le_len_digits_sq (b := 10) (by norm_num) a
    -- ...with the maximum number of digits obtained by rotating `b ^ 2`.
    calc (digits 10 (a ^ 2)).length
    _ ≤ (f :: ly).length := by
      rw [ha2]
      refine digits_ofDigits_len_le_len 10 (by norm_num) (f :: ly) ?_
      intro i hi
      suffices i ∈ digits 10 (b ^ 2) from digits_lt_base' this
      simpa [hb2, or_comm] using hi
    _ = (digits 10 (b ^ 2)).length := by simp [hb2]
    _ ≤ 2 * (digits 10 b).length := len_digits_sq_le (by norm_num) b
    _ ≤ _ := by
      gcongr
      convert digits_ofDigits_len_le_len 10 (by norm_num) lx ?_
      · simpa [hs, ofDigits_append] using hb
      · intro i hi
        suffices i ∈ digits 10 a from digits_lt_base' this
        simp [ha_dig, hi]

  -- Identify the `s, f` pairs which are feasible.
  -- Introduce conditions on `s, f` which can be shown to hold.
  -- From `d = (...f) = a ^ 2 = (...s) ^ 2` we know that `s ^ 2 % 10 = f`.
  -- From `c = (f...) = b ^ 2 = (s...) ^ 2` we have the constraints outlined above.
  _ ↔ ∃ (b s f : ℕ) (lx ly : List ℕ),
      (digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s]) ∧
      (digits 10 (b ^ 2) = ly ++ [f] ∧ a ^ 2 = ofDigits 10 (f :: ly)) ∧
      s ^ 2 % 10 = f ∧
      (ly.length = 2 * lx.length ∧ f ∈ Finset.Ico (s^2) ((s + 1)^2) ∨
        ly.length = 2 * lx.length + 1 ∧ f ∈ Finset.Ico (s^2 / 10) ((s + 1)^2 ⌈/⌉ 10)) ∧
      f ∈ Finset.Ico 1 10 := by
    refine exists₅_congr fun b s f lx ly ↦ ?_
    simp only [and_congr_right_iff, iff_self_and, and_imp]
    intro ha hb hb2 ha2
    refine ⟨?_, digits_sq_of_eq_concat (by norm_num) b hb hb2, ?_⟩
    · calc _
      _ = a ^ 2 % 10 := by
        convert congrArg (ofDigits 10 · ^ 2 % 10) ha.symm using 1
        · simp [ofDigits_cons, pow_mod]
        · simp [ofDigits_digits]
      _ = _ := by
        suffices f < 10 by simpa [ha2, ofDigits_cons] using this
        suffices f ∈ digits 10 (b ^ 2) from digits_lt_base' this
        simp [hb2]
    · rw [Finset.mem_Ico]
      constructor
      · rw [one_le_iff_ne_zero]
        convert getLast_digit_ne_zero 10 (m := b ^ 2) ?_
        · simp [hb2]
        · suffices digits 10 (b ^ 2) ≠ [] from digits_ne_nil_iff_ne_zero.mp this
          simp [hb2]
      · suffices f ∈ digits 10 (b ^ 2) from digits_lt_base' this
        simp [hb2]

  -- Eliminate the right side of the disjunction.
  -- The left side of the disjunction holds for `s = 1, 2, 3` (`f = 1, 4, 9`).
  -- s        =   1    2   3   4   5   6   7   8   9
  -- s^2 % 10 =   1    4   9   6   5   6   9   4   1
  -- f        ∈ 1-3  4-8   9   ∅   ∅   ∅   ∅   ∅   ∅
  -- The right side of the disjunction does not hold for any `s`.
  -- s        =  1  2  3    4    5    6    7    8    9
  -- s^2 % 10 =  1  4  9    6    5    6    9    4    1
  -- f        ∈  ∅  ∅  1  1-2  2-3  3-4  4-6  6-8  8-9
  _ ↔ ∃ (b s f : ℕ) (lx ly : List ℕ),
      (digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s]) ∧
      (digits 10 (b ^ 2) = ly ++ [f] ∧ a ^ 2 = ofDigits 10 (f :: ly)) ∧
      s ^ 2 % 10 = f ∧
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      ly.length = 2 * lx.length := by
    refine exists₅_congr fun b s f lx ly ↦ ?_
    simp only [and_congr_right_iff, and_imp]
    -- Substitute `f = s ^ 2 % 10`.
    rintro ha hb hb2 ha2 rfl
    -- We can use `interval_cases` to check the conditions on `s` using `simp`.
    -- We could also introduce `0 < s` here, but it is not necessary.
    have hs_lt : s < 10 := by
      suffices s ∈ digits 10 a from digits_lt_base' this
      simp [ha]
    interval_cases s <;> simp

  -- Since `s ^ 2 < 10`, we can replace `f = s ^ 2 % 10` with `s ^ 2`.
  -- Re-order and simplify.
  _ ↔ ∃ (b s f : ℕ) (lx ly : List ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧ s ^ 2 % 10 = f ∧
      (digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s]) ∧
      (digits 10 (b ^ 2) = ly ++ [f] ∧ a ^ 2 = ofDigits 10 (f :: ly)) ∧
      ly.length = 2 * lx.length := by
    refine exists₅_congr fun b s f lx ly ↦ ?_
    constructor
    · intro ⟨h_dig, h_sq_dig, hf, hs, h_len⟩
      exact ⟨hs, hf, h_dig, h_sq_dig, h_len⟩
    · intro ⟨hs, hf, h_dig, h_sq_dig, h_len⟩
      exact ⟨h_dig, h_sq_dig, hf, hs, h_len⟩
  _ ↔ ∃ (b s : ℕ) (lx ly : List ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      (digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s]) ∧
      (digits 10 (b ^ 2) = ly ++ [s ^ 2] ∧ a ^ 2 = ofDigits 10 (s ^ 2 :: ly)) ∧
      ly.length = 2 * lx.length := by simp

  -- Introduce `k` to denote the number of elements in `lx`.
  _ ↔ ∃ (b s : ℕ) (lx ly : List ℕ) (k : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      (digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s]) ∧
      (digits 10 (b ^ 2) = ly ++ [s ^ 2] ∧ a ^ 2 = ofDigits 10 (s ^ 2 :: ly)) ∧
      lx.length = k ∧ ly.length = 2 * k := by
    simp

  -- Re-order to separate the length conditions for `lx` and `ly`.
  -- Move `s, k` to the front as these will parameterize the solutions.
  _ ↔ ∃ (s k b : ℕ) (lx ly : List ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      (digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s] ∧ lx.length = k) ∧
      digits 10 (b ^ 2) = ly ++ [s ^ 2] ∧ a ^ 2 = ofDigits 10 (s ^ 2 :: ly) ∧
      ly.length = 2 * k := by
    constructor
    · intro ⟨b, s, lx, ly, k, hs, ⟨ha, hb⟩, ⟨hb2, ha2⟩, hx_len, hy_len⟩
      exact ⟨s, k, b, lx, ly, hs, ⟨ha, hb, hx_len⟩, hb2, ha2, hy_len⟩
    · intro ⟨s, k, b, lx, ly, hs, ⟨ha, hb, hx_len⟩, hb2, ha2, hy_len⟩
      exact ⟨b, s, lx, ly, k, hs, ⟨ha, hb⟩, ⟨hb2, ha2⟩, hx_len, hy_len⟩

  -- Replace `lx, ly` with `x, y` to ease mathematical manipulation.
  -- While we know that `x` has `k` digits, it's possible that `y` has less than `2 * k` digits.
  -- To handle this, pad the digits of `y` with zeros to obtain the digits of `b ^ 2`.
  _ ↔ ∃ (s k b x y : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      (digits 10 a = s :: digits 10 x ∧
        digits 10 b = digits 10 x ++ [s] ∧
        (digits 10 x).length = k) ∧
      digits 10 (b ^ 2) = digits 10 y ++ replicate (2 * k - (digits 10 y).length) 0 ++ [s ^ 2] ∧
      digits 10 (a ^ 2) = s ^ 2 :: digits 10 y ∧
      (digits 10 y).length ≤ 2 * k := by
    refine exists₃_congr fun s k b ↦ ?_
    simp only [exists_and_left, exists_and_right, and_congr_right_iff]
    intro hs
    -- Handle the transformation for `x` and `y` independently.
    refine and_congr ?_ ?_
    · -- The reverse direction for `x` is trivial.
      refine ⟨?_, Exists.imp' (digits 10) fun x ↦ id⟩
      intro ⟨lx, ha_dig, hb_dig, hlx_len⟩
      use ofDigits 10 lx
      -- To show the forward direction, replace `digits 10 (ofDigits 10 lx)` with `lx`.
      suffices digits 10 (ofDigits 10 lx) = lx by simpa [this] using ⟨ha_dig, hb_dig, hlx_len⟩
      refine digits_ofDigits 10 (by norm_num) _ ?_ ?_
      · intro i hi
        suffices i ∈ digits 10 a from digits_lt_base' this
        simp [ha_dig, hi]
      · intro h
        simpa [ha_dig, getLast_cons h] using getLast_digit_ne_zero 10 ha
    · -- For `y`, we need the fact that `digits 10 (s ^ 2) = [s ^ 2]`.
      have hs2_dig : digits 10 (s ^ 2) = [s ^ 2] := by
        refine digits_of_lt 10 (s ^ 2) ?_ ?_
        · suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s ^ 2 ≠ 0 from this s hs
          simp
        · suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s ^ 2 < 10 from this s hs
          simp
      constructor
      -- For the forward direction, need to handle padding of `digits 10 y` with zeros.
      · intro ⟨l, hb2_dig, ha2, h_len⟩
        use ofDigits 10 l
        refine ⟨?_, ?_, ?_⟩
        · convert hb2_dig
          rw [← h_len]
          refine digits_ofDigits_append_zeroes_eq_self (by norm_num) l fun i hi ↦ ?_
          suffices i ∈ digits 10 (b ^ 2) from digits_lt_base' this
          simp [hb2_dig, hi]
        · rw [ha2, ofDigits_cons]
          have := digits_append_digits (b := 10) (n := s ^ 2) (m := ofDigits 10 l) (by norm_num)
          simpa [hs2_dig] using this.symm
        · refine le_of_le_of_eq ?_ h_len
          refine digits_ofDigits_len_le_len 10 (by norm_num) l fun i hi ↦ ?_
          suffices i ∈ digits 10 (b ^ 2) from digits_lt_base' this
          simp [hb2_dig, hi]
      -- The reverse direction for `y` is also simpler.
      · intro ⟨y, hb2_dig, ha2_dig, hy_len⟩
        use digits 10 y ++ replicate (2 * k - (digits 10 y).length) 0
        refine ⟨hb2_dig, ?_, ?_⟩
        · convert congrArg (ofDigits 10) ha2_dig using 1
          · simp [ofDigits_digits]
          · simp [ofDigits_cons, ofDigits_append, ofDigits_replicate_zero]
        · simp [hy_len]

  -- Next replace `y` and the length constraints on `a ^ 2, b ^ 2` with the form of `x`.
  -- Since the number of digits in `a ^ 2` and `b ^ 2` is used to eliminate the case where
  -- `k > 0` and `s ∈ {2, 3}`, we split on `k` here.
  _ ↔ ∃ (s k b x : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      digits 10 a = s :: digits 10 x ∧
      digits 10 b = digits 10 x ++ [s] ∧
      (k = 0 ∧ x = 0 ∨ k ≠ 0 ∧ s = 1 ∧ digits 10 x = replicate k (2 * s)) := by
    refine exists₄_congr fun s k b x ↦ ?_
    simp only [and_assoc, exists_and_left, and_congr_right_iff]
    intro hs ha_dig hb_dig
    -- Establish properties of `s` that we will need.
    have hs_zero : s ≠ 0 := by
      suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s ≠ 0 from this s hs
      simp
    have hs_two_mul_lt : 2 * s < 10 := by
      suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → 2 * s < 10 from this s hs
      simp
    have hs_sq_lt : s ^ 2 < 10 := by
      suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s ^ 2 < 10 from this s hs
      simp
    have hs2_dig : digits 10 (s ^ 2) = [s ^ 2] :=
      digits_of_lt 10 (s ^ 2) (by simpa using hs_zero) hs_sq_lt

    -- Split based on whether `a` has one or more digits.
    cases eq_or_ne k 0 with
    | inl hk =>
      rcases hk with rfl
      suffices x = 0 → digits 10 (b ^ 2) = [s ^ 2] ∧ digits 10 (a ^ 2) = [s ^ 2] by
        simpa [digits_eq_nil_iff_eq_zero]
      rintro rfl
      convert And.intro hs2_dig hs2_dig
      · have := congrArg (ofDigits 10) hb_dig
        simpa [ofDigits_digits] using this
      · have := congrArg (ofDigits 10) ha_dig
        simpa [ofDigits_digits] using this

    | inr hk =>
      -- It remains to show that (1) the specified `x` satisfies the equations for `s = 1`, and
      -- (2) that the equations are inconsistent with `s = 2, 3` for `k ≠ 0`.
      -- Simplify the right side.
      refine Iff.trans (b := s = 1 ∧ digits 10 x = replicate k (2 * s)) ?_ (by simp [hk])
      constructor
      -- Show that the equations imply `s = 1`.
      · intro ⟨hx_len, y, hb2_dig, ha2_dig, hy_len⟩
        suffices hx_dig : digits 10 x = replicate k (2 * s) by
          refine ⟨hs.resolve_right ?_, hx_dig⟩
          intro hs
          -- Find contradiction using number of digits in `a ^ 2`.
          -- First use the fact that `a ^ 2` is a digit rotation of `b ^ 2`.
          -- Due to this fact, `a ^ 2` has at most the same number of digits, which is `2 k + 1`.
          have ha2_len : (digits 10 (a ^ 2)).length ≤ 2 * k + 1 := by simp [ha2_dig, hy_len]
          refine ha2_len.not_lt ?_
          -- Now consider the number of digits obtained by squaring `a`.
          -- Since `a` has `k + 1` digits, `a ^ 2` may have either `2 k + 1` or `2 k + 2` digits.
          -- However, the leading digit of `a` is `2 * s` with `s` being 2 or 3.
          -- Since `10 ≤ (2 * s) ^ 2`, `a ^ 2` has `2 k + 2` digits, providing the contradiction.
          -- Replace `k` with `m + 1` for easier simplification.
          obtain ⟨m, rfl⟩ : ∃ m, m + 1 = k := exists_add_one_eq.mpr (zero_lt_of_ne_zero hk)
          suffices (digits 10 (a ^ 2)).length = 2 * (digits 10 a).length by
            simp [this, ha_dig, hx_dig, mul_add]
          refine len_digits_sq_eq_of_le_getLast_sq (b := 10) (by norm_num) a ?_
          suffices 10 ≤ (2 * s) ^ 2 by simpa [ha_dig, hx_dig] using this
          suffices ∀ s, s = 2 ∨ s = 3 → 10 ≤ (2 * s) ^ 2 from this s hs
          simp

        rw [← eq_iff_digits_eq_replicate_two_mul hs_zero hs_two_mul_lt]
        -- We will obtain two equations for `y` by substituting expressions for `a, b` in
        -- the equations for `a ^ 2, b ^ 2`.
        suffices x * (x + 2 * s * 10 ^ k) = x * (2 * s + 10 * x) by
          rw [mul_eq_mul_left_iff] at this
          refine this.resolve_right ?_
          refine mt (fun hx ↦ ?_) hk
          simpa [hx] using hx_len.symm
        -- Obtain `a, b, a ^ 2, b ^ 2` from their digits.
        have ha : a = s + 10 * x := by
          have := congrArg (ofDigits 10) ha_dig
          simpa [ofDigits_digits, ofDigits_cons] using this
        have hb : b = x + 10 ^ k * s := by
          have := congrArg (ofDigits 10) hb_dig
          simpa [ofDigits_digits, ofDigits_append, hx_len] using this
        have ha2 : a ^ 2 = s ^ 2 + 10 * y := by
          have := congrArg (ofDigits 10) ha2_dig
          simpa [ofDigits_digits, ofDigits_cons, hy_len] using this
        have hb2 : b ^ 2 = y + 10 ^ (2 * k) * s ^ 2 := by
          have := congrArg (ofDigits 10) hb2_dig
          simpa [ofDigits_digits, ofDigits_replicate_zero, ofDigits_append, -append_assoc,
            ← pow_add, hy_len] using this
        -- Substitute the definitions for `a, b`.
        rw [ha] at ha2
        rw [hb] at hb2
        -- Eliminate common terms on both sides to obtain two definitions for `y`.
        have ha2 : x * (2 * s + 10 * x) = y := by
          suffices s ^ 2 + 10 * (x * (2 * s + 10 * x)) = s ^ 2 + 10 * y by simpa
          convert ha2 using 1
          ring
        have hb2 : x * (x + 2 * s * 10 ^ k) = y := by
          suffices x * (x + 2 * s * 10 ^ k) + 10 ^ (2 * k) * s ^ 2 = y + 10 ^ (2 * k) * s ^ 2 by
            simpa
          convert hb2 using 1
          ring
        exact hb2.trans ha2.symm

      -- Show that the specified `x` satisfies the constraints.
      · intro ⟨hs, hx_dig⟩
        -- The length constraint is trivial.
        have hx_len : (digits 10 x).length = k := by
          have := congrArg length hx_dig
          simpa using this
        refine ⟨hx_len, ?_⟩
        -- It remains to show that the `y` resulting from `x` gives the digits of `b ^ 2, a ^ 2`
        -- and satsfies the length constraint.
        -- Obtain the two forms of `y` back from the digits form.
        have hx : x + 2 * s * 10 ^ k = 2 * s + 10 * x :=
          (eq_iff_digits_eq_replicate_two_mul hs_zero hs_two_mul_lt x).mpr hx_dig
        let y := x * (2 * s + 10 * x)
        use y
        -- Show that `a ^ 2` and `b ^ 2` can be written using `y`.
        have ha : a = s + 10 * x := by
          have := congrArg (ofDigits 10) ha_dig
          simpa [ofDigits_digits, ofDigits_cons] using this
        have hb : b = x + 10 ^ k * s := by
          have := congrArg (ofDigits 10) hb_dig
          simpa [ofDigits_digits, ofDigits_append, hx_len] using this
        have ha2 : a ^ 2 = s ^ 2 + y * 10 := by
          unfold y
          rw [ha]
          ring
        have hb2 : b ^ 2 = 10 ^ (2 * k) * s ^ 2 + y := by
          unfold y
          rw [← hx, hb]
          ring

        -- Since `a` has `k + 1` digits with leading digit satisfying `(d + 1) ^ 2 < 10`, we know
        -- that `a ^ 2` will have exactly `2 k + 1` digits, the smaller of the two possible cases.
        have ha2_len : (digits 10 (a ^ 2)).length + 1 = 2 * (digits 10 a).length := by
          rw [len_digits_sq_eq_of_getLast_add_one_sq_lt (by norm_num)]
          · simp [ha_dig, mul_add]
          · cases k <;> simp [ha_dig, hx_dig, hs]
        -- Connect the digits of `a ^ 2` to those of `y` to subsequently obtain the length of `y`.
        have ha2_dig : digits 10 (a ^ 2) = s ^ 2 :: digits 10 y := by
          suffices digits 10 (a ^ 2) = digits 10 (s ^ 2) ++ digits 10 y by simpa [hs2_dig]
          convert (digits_append_digits (b := 10) (by norm_num)).symm using 2
          simp only [ha2, hs2_dig, length_singleton]
          ring
        -- In fact, we can show the stronger result that `y` has exactly `2 * k` digits.
        have hy_len : (digits 10 y).length = 2 * k := by
          suffices (digits 10 y).length + 2 = 2 * (k + 1) by simpa [mul_add]
          calc (digits 10 y).length + 2
          _ = (digits 10 (a ^ 2)).length + 1 := by simp [ha2_dig]
          _ = 2 * (digits 10 a).length := by rw [ha2_len]
          _ = 2 * (k + 1) := by simp [ha_dig, hx_len]
        refine ⟨?_, ha2_dig, hy_len.le⟩
        -- The length constraint can finally be applied to obtain the digits of `b ^ 2`.
        suffices digits 10 (b ^ 2) = digits 10 y ++ digits 10 (s ^ 2) by simpa [hy_len, hs2_dig]
        convert (digits_append_digits (b := 10) (by norm_num)).symm using 2
        simp only [hb2, hy_len]
        ring

  -- Eliminate `b` and `x`.
  _ ↔ ∃ (s k : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      (k = 0 ∧ a = s ∨ k ≠ 0 ∧ s = 1 ∧ digits 10 a = s :: replicate k (2 * s)) := by
    refine exists₂_congr fun s k ↦ ?_
    simp only [exists_and_left, and_congr_right_iff]
    intro hs
    constructor
    · intro ⟨b, x, ha_dig, hb_dig, h⟩
      refine h.imp ?_ ?_
      · intro ⟨hk, hx⟩
        refine ⟨hk, ?_⟩
        have := congrArg (ofDigits 10) ha_dig
        simpa [ofDigits_digits, hx] using this
      · intro ⟨hk, hs, hx_dig⟩
        exact ⟨hk, hs, hx_dig ▸ ha_dig⟩
    · intro h
      cases h with
      | inl h =>
        rcases h with ⟨hk, rfl⟩
        suffices digits 10 a = [a] from ⟨a, 0, by simpa [hk] using this⟩
        refine digits_of_lt 10 a ha ?_
        suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s < 10 from this a hs
        simp
      | inr h =>
        rcases h with ⟨hk, rfl, ha_dig⟩
        use (ofDigits 10 (replicate k 2 ++ [1]))
        use (ofDigits 10 (replicate k 2))
        have hx_dig : digits 10 (ofDigits 10 (replicate k 2)) = replicate k 2 := by
          refine digits_ofDigits 10 ?_ _ ?_ ?_ <;> simp
        have hb_dig : digits 10 (ofDigits 10 (replicate k 2 ++ [1])) = replicate k 2 ++ [1] := by
          refine digits_ofDigits 10 ?_ _ ?_ ?_ <;> simp [hk]
        rw [hx_dig, hb_dig]
        exact ⟨ha_dig, rfl, .inr ⟨hk, rfl, rfl⟩⟩

  -- Put in the final form.
  _ ↔ _ := by
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · intro ⟨s, k, ⟨hs, h⟩⟩
      refine h.imp ?_ ?_
      · rintro ⟨rfl, rfl⟩
        exact hs
      · rintro ⟨hk, rfl, ha_dig⟩
        use k - 1
        rw [sub_one_add_one hk]
        have := congrArg (ofDigits 10) ha_dig
        simpa [ofDigits_digits] using this.symm
    · intro h
      cases h with
      | inl h =>
        use a, 0
        simpa using h
      | inr h =>
        rcases h with ⟨k, ha⟩
        use 1, k + 1
        suffices digits 10 a = 1 :: replicate (k + 1) 2 by simpa
        rw [← ha]
        refine digits_ofDigits 10 ?_ _ ?_ ?_ <;> simp
