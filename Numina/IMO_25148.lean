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

-- When we square a number with $n$ digits, we get a number with either $2 n$ or $2 n + 1$ digits.
-- Using the existing lemmas in Mathlib, this is most easily expressed using Nat.log.

lemma le_log_sq {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : 2 * log b n ≤ log b (n ^ 2) := by
  refine le_log_of_pow_le hb ?_
  rw [mul_comm, pow_mul]
  refine Nat.pow_le_pow_left ?_ 2
  exact pow_log_le_self b hn

-- TODO: Might be more elegant to generalize power.
lemma log_sq_le {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b (n ^ 2) ≤ 2 * log b n + 1 := by
  suffices log b (n ^ 2) < 2 * (log b n + 1) from le_of_lt_succ this
  refine Nat.log_lt_of_lt_pow (by simpa) ?_
  rw [mul_comm, pow_mul]
  gcongr
  exact lt_pow_succ_log_self hb n

-- lemma log_sq_mem_Icc {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
--     log b (n ^ 2) ∈ Finset.Icc (2 * log b n) (2 * log b n + 1) :=
--   Finset.mem_Icc.mpr ⟨le_log_sq hb hn, log_sq_le hb hn⟩

-- TODO: Rename to reflect `log`.
lemma log_sq_eq {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b (n ^ 2) = 2 * log b n ∨ log b (n ^ 2) = 2 * log b n + 1 :=
  le_and_le_add_one_iff.mp ⟨le_log_sq hb hn, log_sq_le hb hn⟩

-- Useful lemma for converting between `digits` and `ofDigits`.
lemma digits_eq_iff (b : ℕ) (hb : 1 < b) (n : ℕ) (l : List ℕ) : digits b n = l ↔
    (∀ x ∈ l, x < b) ∧ (∀ h : l ≠ [], l.getLast h ≠ 0) ∧ n = ofDigits b l := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact digits_lt_base hb
    · intro hl
      refine getLast_digit_ne_zero b ?_
      exact digits_ne_nil_iff_ne_zero.mp hl
    · exact (ofDigits_digits b n).symm
  · rintro ⟨h_lt, h_ne, rfl⟩
    exact digits_ofDigits b hb l h_lt h_ne


-- lemma digits_add_base_mul (b : ℕ) (hb : 1 < b) (x y : ℕ) (hx : x < b) (hy : y ≠ 0) :
--     digits b (x + b * y) = x :: digits b y := by
--   convert digits_eq_cons_digits_div hb ?_ using 3
--   · simp [mod_eq_of_lt hx]
--   · rw [add_mul_div_left _ _ (zero_lt_of_lt hb)]
--     simp [hx]
--   · simp [add_ne_zero, hy, not_eq_zero_of_lt hb]

lemma digits_add_base_mul (b : ℕ) (hb : 1 < b) (x y : ℕ) (hx : x < b) (hy : y ≠ 0) :
    digits b (x + b * y) = x :: digits b y := by
  cases x with
  | zero => simpa using digits_base_pow_mul hb (k := 1) (zero_lt_of_ne_zero hy)
  | succ x =>
    simpa [digits_of_lt b _ x.add_one_ne_zero hx] using
      (digits_append_digits (zero_lt_of_lt hb) (n := x + 1) (m := y)).symm

-- lemma digits_add_base_pow_mul (b : ℕ) (hb : 1 < b) (k x y : ℕ) (hx : x < b ^ k) (hy : y ≠ 0) :
--     digits b (x + b ^ k * y) = x :: digits b y := by
--   cases x with
--   | zero => simpa using digits_base_pow_mul hb (k := 1) (zero_lt_of_ne_zero hy)
--   | succ x =>
--     simpa [digits_of_lt b _ x.add_one_ne_zero hx] using
--       (digits_append_digits (zero_lt_of_lt hb) (n := x + 1) (m := y)).symm

lemma digits_ofDigits_len_le_len (b : ℕ) (hb : 1 < b) (l : List ℕ) (hl : ∀ x ∈ l, x < b) :
    (digits b (ofDigits b l)).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons x l IH =>
    have ⟨hx, hl⟩ : x < b ∧ ∀ x ∈ l, x < b := by simpa using hl
    rw [ofDigits_cons, length_cons]
    cases eq_or_ne (ofDigits b l) 0 with
    | inl hl_zero =>
      simp only [hl_zero, mul_zero, add_zero]
      cases x with
      | zero => simp
      | succ x => simp [digits_of_lt b x.succ x.add_one_ne_zero hx]
    | inr hl_zero =>
      rw [digits_add_base_mul b hb _ _ hx hl_zero]
      simpa using IH hl

lemma ofDigits_replicate_zero (b : ℕ) (n : ℕ) : ofDigits b (replicate n 0) = 0 := by
  induction n with
  | zero => simp
  | succ n IH => simp [replicate_succ, ofDigits_cons, IH]


-- When we square an `n`-digit number with leading digit `x`, the result may have `2 * n` or
-- `2 * n + 1` digits. The map of leading digits is monotonic except for this discontinuity.
-- Therefore, we have to consider whether `x ^ 2 < b ≤ (x + 1) ^ 2`.

-- Similar to `Nat.log_eq_iff` except it accounts for the leading digit.

lemma mem_Ico_of_digits_eq_concat {b : ℕ} (hb : 1 < b) (n x : ℕ) (l : List ℕ)
    (hn_digits : digits b n = l ++ [x]) :
    n ∈ Set.Ico (x * b ^ l.length) ((x + 1) * b ^ l.length) := by
  -- have hn_zero : n ≠ 0 := by
  --   suffices digits b n ≠ [] from digits_ne_nil_iff_ne_zero.mp this
  --   simp [hn]
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

lemma digits_square_concat (b : ℕ) (hb : 1 < b) (n : ℕ)
    (lx : List ℕ) (x : ℕ) (ly : List ℕ) (y : ℕ)
    (hx : digits b n = lx ++ [x]) (hy : digits b (n ^ 2) = ly ++ [y]) :
    ly.length = 2 * lx.length ∧ y ∈ Finset.Ico (1 ⊔ x ^ 2) (b ⊓ (x + 1) ^ 2) ∨
    ly.length = 2 * lx.length + 1 ∧ y ∈ Finset.Ico (1 ⊔ x ^ 2 / b) (b ⊓ (x + 1) ^ 2 ⌈/⌉ b) := by
  have hn_zero : n ≠ 0 := by
    suffices digits b n ≠ [] from digits_ne_nil_iff_ne_zero.mp this
    simp [hx]

  have hx_mem := mem_Ico_of_digits_eq_concat hb n x lx hx
  have hy_mem := mem_Ico_of_digits_eq_concat hb (n ^ 2) y ly hy

  -- Split into two cases.
  -- If `n` has `k + 1` digits, then `n ^ 2` has either `2 k + 1` or `2 k + 2` digits.
  -- When it has `2 k + 1`, we know that `x ^ 2 < b` and there was no carry to change this.
  -- TODO: Replace `log` lemma with `length ∘ digits` lemma?
  refine Or.imp (fun h_len ↦ ?_) (fun h_len ↦ ?_) (log_sq_eq hb hn_zero)
  · have h_len : ly.length = 2 * lx.length := by
      suffices (digits b (n ^ 2)).length + 1 = 2 * (digits b n).length by
        simpa [hx, hy, mul_add] using this
      simpa [digits_len b _ hb, hn_zero, mul_add] using h_len

    rw [h_len] at hy_mem
    simp only [← Finset.Ico_inter_Ico, Finset.mem_inter, Finset.mem_Ico]
    refine ⟨h_len, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [one_le_iff_ne_zero]
      convert getLast_digit_ne_zero b (m := n ^ 2) (by simpa using hn_zero)
      simp [hy]
    · suffices y ∈ digits b (n ^ 2) from digits_lt_base hb this
      simp [hy]

    -- We want to show `x ^ 2 ≤ y < (x + 1) ^ 2` when `n` has `k` digits and
    -- `n ^ 2` has `2 * k` digits, with `k = log b n + 1`.

    -- We have `x * b ^ k ≤ n < (x + 1) * b ^ k`
    -- and `y * b ^ (2 * k) ≤ n ^ 2 < (y + 1) * b ^ (2 * k)`.

    -- Does this help us?
    -- What is the principle that we need to apply?

    -- `n = x * b ^ k + r`
    -- Therefore `n ^ 2` is at least `x ^ 2 * b ^ (2 * k)`
    -- But does this help us to bound `y`?
    -- From above, we do have `n ^ 2 < (y + 1) * b ^ (2 * k)`.
    -- Putting these together,
    -- `x ^ 2 * b ^ (2 * k) < (y + 1) * b ^ (2 * k)`
    -- `x ^ 2 < y + 1`
    -- `x ^ 2 ≤ y`
    -- Not sure if this will always work though?

    -- Consider the other side of the bound:
    -- `n = x * b ^ k + r`, and `n < (x + 1) * b ^ k`
    -- `n ^ 2 < (x + 1) ^ 2 * b ^ (2 * k)`
    -- From above, we have `y * b ^ (2 * k) ≤ n ^ 2`
    -- Putting these together,
    -- `y * b ^ (2 * k) < (x + 1) ^ 2 * b ^ (2 * k)`
    -- `y < (x + 1) ^ 2`

    -- Looks good!

    · suffices x ^ 2 < y + 1 from le_of_lt_succ this
      suffices x ^ 2 * b ^ (2 * lx.length) < (y + 1) * b ^ (2 * lx.length) from
        Nat.lt_of_mul_lt_mul_right this
      convert lt_of_le_of_lt (Nat.pow_le_pow_left hx_mem.1 2) hy_mem.2 using 1
      ring
    · suffices y * b ^ (2 * lx.length) < (x + 1) ^ 2 * b ^ (2 * lx.length) from
        Nat.lt_of_mul_lt_mul_right this
      convert lt_of_le_of_lt hy_mem.1 (Nat.pow_lt_pow_left hx_mem.2 two_ne_zero) using 1
      ring

  · have h_len : ly.length = 2 * lx.length + 1 := by
      suffices (digits b (n ^ 2)).length = 2 * (digits b n).length by
        simpa [hx, hy, mul_add] using this
      simpa [digits_len b _ hb, hn_zero, mul_add] using h_len

    rw [h_len] at hy_mem
    simp only [← Finset.Ico_inter_Ico, Finset.mem_inter, Finset.mem_Ico]
    refine ⟨h_len, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [one_le_iff_ne_zero]
      convert getLast_digit_ne_zero b (m := n ^ 2) (by simpa using hn_zero)
      simp [hy]
    · suffices y ∈ digits b (n ^ 2) from digits_lt_base hb this
      simp [hy]

    · suffices x ^ 2 / b < y + 1 from le_of_lt_succ this
      rw [div_lt_iff_lt_mul (zero_lt_of_lt hb)]
      -- suffices x ^ 2 < (y + 1) * b from (div_lt_iff_lt_mul (zero_lt_of_lt hb)).mpr this
      suffices x ^ 2 * b ^ (2 * lx.length) < (y + 1) * b * b ^ (2 * lx.length) from
        Nat.lt_of_mul_lt_mul_right this
      convert lt_of_le_of_lt (Nat.pow_le_pow_left hx_mem.1 2) hy_mem.2 using 1 <;> ring

      -- Where is the bound coming from.
      -- n ^ 2 = y * 10 ^ (2 k + 1) + c = (x * 10 ^ k + r) ^ 2
      -- (x * 10 ^ k) ^ 2 = x ^ 2 * 10 ^ (2 k) ≤ n ^ 2
      -- n ^ 2 < (y + 1) * 10 ^ (2 k + 1) = 10 (y + 1) * 10 ^ (2 k)

      -- Together:
      -- x ^ 2 * 10 ^ (2 k) < 10 (y + 1) 10 ^ (2 k)
      -- x ^ 2 < 10 (y + 1)
      -- x ^ 2 / 10 < y + 1  `Nat.div_lt_iff_lt_mul`
      -- x ^ 2 / 10 ≤ y

    · -- n ^ 2 = y * 10 ^ (2 k + 1) + c = (x * 10 ^ k + r) ^ 2
      -- y * 10 ^ (2 k + 1) ≤ y * 10 ^ (2 k + 1) + c = n ^ 2
      -- n ^ 2 = (x * 10 ^ k + r) ^ 2 < (x + 1) ^ 2 * 10 ^ (2 k)
      -- Together:
      -- 10 y * 10 ^ (2 k) < (x + 1) ^ 2 * 10 ^ (2 k)
      -- 10 y < (x + 1) ^ 2
      -- 10 y < x ^ 2 + 2 x + 1
      -- 10 y ≤ x ^ 2 + 2 x = x (x + 2)
      -- y ≤ x (x + 2) / 10 = (x ^ 2 + 2 * x) / 10

      -- What is the condition on `y` given `10 y < (x + 1) ^ 2`?
      -- y * 10 < ((x + 1) ^ 2 + 10 - 1) - (10 - 1)
      -- y < ((x + 1) ^ 2 + 10 - 1) / 10
      -- y < (x + 1) ^ 2 ⌈/⌉ 10

      rw [ceilDiv_eq_add_pred_div]
      -- TODO: Avoid `tsub` if possible?
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

-- TODO: Extract as lemma. Use log or length digits?
lemma len_digits_eq_of_le_getLast_sq (b : ℕ) (hb : 1 < b) (n : ℕ)
    (hn : digits b n ≠ []) (hx : b ≤ (digits b n).getLast hn ^ 2) :
    (digits b (n ^ 2)).length = 2 * (digits b n).length := by
  sorry

-- TODO: Extract as lemma. Use log (to avoid - 1) or length of digits?
lemma len_digits_eq_of_getLast_add_one_sq_lt (b : ℕ) (hb : 1 < b) (n : ℕ)
    (hn : digits b n ≠ []) (hx : ((digits b n).getLast hn + 1) ^ 2 < b) :
    (digits b (n ^ 2)).length = 2 * (digits b n).length - 1 := by
  sorry


-- TODO: There might be an easier way to prove this using injectivity of addition?
-- Uniqueness of `div_add_mod`? `List.take_append_drop`?
lemma getLast_eq_div_pow (b : ℕ) (hb : 1 < b) (n : ℕ) (hl : digits b n ≠ []) :
    (digits b n).getLast hl = n / b ^ log b n := by
  have hn : n ≠ 0 := digits_ne_nil_iff_ne_zero.mp hl
  calc (digits b n).getLast hl
  _ = ofDigits b [(digits b n).getLast hl] := by simp
  _ = ofDigits b (drop ((digits b n).length - 1) (digits b n)) := by rw [drop_length_sub_one hl]
  _ = ofDigits b (drop (log b n) (digits b n)) := by simp [digits_len b n hb hn]
  _ = n / b ^ log b n := by rw [self_div_pow_eq_ofDigits_drop (log b n) n hb]

lemma exists_digits_eq_concat_iff_exists_lt_pow_log (b : ℕ) (hb : 1 < b) (n d : ℕ) :
    (∃ l, digits b n = l ++ [d]) ↔ n ≠ 0 ∧ ∃ x < b ^ log b n, x + b ^ log b n * d = n := by
  constructor
  · intro ⟨l, hl⟩
    have hn : n ≠ 0 := by
      suffices digits b n ≠ [] from digits_ne_nil_iff_ne_zero.mp this
      simp [hl]
    have hl_len : l.length = log b n := by
      suffices l.length + 1 = log b n + 1 by simpa using this
      convert congrArg length hl.symm
      · simp
      · rw [digits_len b n hb hn]
    refine ⟨hn, ofDigits b l, ?_, ?_⟩
    · refine hl_len ▸ ofDigits_lt_base_pow_length hb fun x hx ↦ ?_
      suffices x ∈ digits b n from digits_lt_base hb this
      exact hl ▸ mem_append_left [d] hx
    · convert congrArg (ofDigits b) hl.symm using 1
      · rw [ofDigits_append, ofDigits_singleton, hl_len]
      · rw [ofDigits_digits]
  · intro ⟨hn, x, hx_lt, hx⟩
    suffices d = (digits b n).getLast (digits_ne_nil_iff_ne_zero.mpr hn) by
      use (digits b n).dropLast
      simp [this, dropLast_append_getLast]
    rw [getLast_eq_div_pow b hb]
    convert congrArg (· / b ^ log b n) hx
    rw [add_mul_div_left _ _ (zero_lt_of_lt hx_lt)]
    simp [hx_lt]

lemma exists_digits_eq_concat_iff_exists_lt_pow_log_of_ne_zero (b : ℕ) (hb : 1 < b)
    (n d : ℕ) (hn : n ≠ 0) :
    (∃ l, digits b n = l ++ [d]) ↔ ∃ x < b ^ log b n, x + b ^ log b n * d = n := by
  simpa [hn] using exists_digits_eq_concat_iff_exists_lt_pow_log b hb n d

lemma exists_digits_eq_concat_iff_exists_getLast_eq (b : ℕ) (hb : 1 < b) (n d : ℕ) :
    (∃ l, digits b n = l ++ [d]) ↔ ∃ h : digits b n ≠ [], (digits b n).getLast h = d := by
  constructor
  · intro ⟨l, hl⟩
    simp [hl]
  · intro ⟨hl, hd⟩
    use (digits b n).dropLast
    rw [← hd]
    simp [dropLast_append_getLast]

lemma exists_digits_eq_concat_iff_exists_getLast_eq_of_ne_nil (b : ℕ) (hb : 1 < b)
    (n d : ℕ) (hl : digits b n ≠ []) :
    (∃ l, digits b n = l ++ [d]) ↔ (digits b n).getLast hl = d := by
  simpa [hl] using exists_digits_eq_concat_iff_exists_getLast_eq b hb n d

-- Let `digits b n = s ++ [x]` and `digits b (n ^ 2) = t ++ [y]`.

-- Hard to use since need to specify `ly`.
-- lemma digits_square_concat_of_asdf (b : ℕ) (hb : 1 < b) (n : ℕ)
--     (lx : List ℕ) (x : ℕ) (hx : digits b n = lx ++ [x])
--     (ly : List ℕ) (y : ℕ) (hy : digits b (n ^ 2) = lx ++ [x])
--     (hy_len : ly.length = 2 * lx.length) :
--     y ∈ Finset.Ico (1 ⊔ x ^ 2) (b ⊓ (x + 1) ^ 2) := by
--   sorry


-- The key constraints are:
-- From `d = a ^ 2`:
-- `(digits 10 d)[0] = (digits 10 (a ^ 2))[0] = (digits 10 a)[0] ^ 2 % 10`
-- From `c = b ^ 2`:
-- `(digits 10 c).getLast _ = (digits 10 (b ^ 2)).getLast _ ∈ ?`
-- From the rotations:
-- `(digits 10 b).getLast = (digits 10 a)[0]`
-- `(digits 10 c).getLast = (digits 10 d)[0]`

-- Let `a = [s] ++ ta` and `c = hc ++ [f]`, then
-- `f = (digits 10 c).getLast _ = (digits 10 d)[0] = s ^ 2 % 10`
-- `f ∈ ?`

lemma rotateRight_concat (l : List ℕ) (x : ℕ) :
    rotateRight (l ++ [x]) = x :: l := by
  unfold rotateRight
  cases l <;> simp

lemma rotateLeft_cons (l : List ℕ) (x : ℕ) :
    rotateLeft (x :: l) = l ++ [x] := by
  unfold rotateLeft
  cases l <;> simp

lemma rotate_cons (l : List ℕ) (x : ℕ) :
    (x :: l).rotate 1 = l ++ [x] := by
  unfold rotate
  cases l <;> simp

-- TODO: Comment
-- Note: It is not necessary to exclude the zero case.
lemma first_and_last (s : ℕ) (hs : s < 10) :
    (s ^ 2 % 10 ∈ Finset.Ico (1 ⊔ s ^ 2) (10 ⊓ (s + 1) ^ 2) ∪
      Finset.Ico (1 ⊔ s ^ 2 / 10) (10 ⊓ (s + 1) ^ 2 ⌈/⌉ 10)) ↔
    s ∈ ({1, 2, 3} : Finset ℕ) := by
  interval_cases s <;> simp

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

lemma ten_pow_sub_one_div_nine (n : ℕ) :
    (10 ^ n - 1) / 9 = ofDigits 10 (replicate n 1) := by
  refine Nat.div_eq_of_eq_mul_right (by norm_num) ?_
  refine Nat.sub_eq_of_eq_add ?_
  exact ten_pow_eq_nine_mul_replicate_add_one n


theorem number_theory_25148 {a : ℕ} (ha : a ≠ 0) :
    d a = a ^ 2 ↔ a ∈ {1, 2, 3} ∪ Set.range (fun n ↦ ofDigits 10 (1 :: replicate (n + 1) 2)) := by
  unfold d

  calc _
  -- a = ...s
  -- b = s...
  -- c = f...
  -- d = ...f = a ^ 2
  _ ↔ ∃ (b c : ℕ) (la lc : List ℕ),
      digits 10 a = la ∧ ofDigits 10 (la.rotate 1) = b ∧ b ^ 2 = c ∧
      digits 10 c = lc ∧ ofDigits 10 lc.rotateRight = a ^ 2 := by simp

  _ ↔ ∃ (b c : ℕ) (s f : ℕ) (lx ly : List ℕ) (la lc : List ℕ),
      digits 10 a = la ∧ ofDigits 10 (la.rotate 1) = b ∧ b ^ 2 = c ∧
      digits 10 c = lc ∧ ofDigits 10 lc.rotateRight = a ^ 2 ∧
      la = s :: lx ∧ lc = ly ++ [f] := by
    simp only [exists_and_left, exists_eq_left', exists_and_right, iff_self_and]
    intro _
    refine ⟨?_, ?_⟩
    · rw [← length_pos_iff_exists_cons]
      refine length_pos.mpr ?_
      exact digits_ne_nil_iff_ne_zero.mpr ha
    · suffices digits 10 (ofDigits 10 ((digits 10 a).rotate 1) ^ 2) ≠ [] by
        -- Is this not available as a lemma?
        generalize digits 10 (ofDigits 10 ((digits 10 a).rotate 1) ^ 2) = l at this ⊢
        use l.getLast this, l.take (l.length - 1)
        simp
      suffices ofDigits 10 ((digits 10 a).rotate 1) ^ 2 ≠ 0 from digits_ne_nil_iff_ne_zero.mpr this
      refine pow_ne_zero 2 ?_
      -- The number composed of rotated digits of `a` cannot be zero since `a` is not zero.
      -- Show this using the largest digit of `a`, which must be non-zero.
      refine mt (fun h ↦ ?_) (getLast_digit_ne_zero 10 ha)
      exact digits_zero_of_eq_zero (by norm_num) h _ (by simp)

  -- -- Re-order and eliminate `la, lc`.
  -- _ ↔ ∃ (b c : ℕ) (s f : ℕ) (lx ly : List ℕ) (la lc : List ℕ),
  --     la = s :: lx ∧ lc = ly ++ [f] ∧
  --     digits 10 a = la ∧ ofDigits 10 (la.rotate 1) = b ∧ b ^ 2 = c ∧
  --     digits 10 c = lc ∧ ofDigits 10 lc.rotateRight = a ^ 2 := by
  --   refine exists₂_congr fun b c ↦ ?_
  --   refine exists₄_congr fun s f lx ly ↦ ?_
  --   refine exists₂_congr fun la lc ↦ ?_
  --   sorry
  -- _ ↔ ∃ (b c : ℕ) (s f : ℕ) (lx ly : List ℕ),
  --     digits 10 a = s :: lx ∧ ofDigits 10 ((s :: lx).rotate 1) = b ∧ b ^ 2 = c ∧
  --     digits 10 c = ly ++ [f] ∧ ofDigits 10 (ly ++ [f]).rotateRight = a ^ 2 := by
  --   simp

  -- Eliminate `la, lc`.
  -- Leave `b` as `b = ofDigits 10 ...` rather than `digits 10 b = ...` since `s` could be zero.
  -- Likewise for `d = a ^ 2`, since `ly` could end in zero.
  -- We do know, however, that `lx` is the valid digits of `a / 10` and `f` is non-zero.
  -- TODO: Eliminate `lx`?
  _ ↔ ∃ (b c : ℕ) (s f : ℕ) (lx ly : List ℕ),
      digits 10 a = s :: lx ∧
      ofDigits 10 (lx ++ [s]) = b ∧
      b ^ 2 = c ∧
      digits 10 c = ly ++ [f] ∧
      ofDigits 10 (f :: ly) = a ^ 2 := by
    refine exists₂_congr fun b c ↦ exists₄_congr fun s f lx ly ↦ ?_
    simp only [exists_and_left, exists_eq_left']
    constructor
    · intro ⟨hb, hc, hd, hla, hlc⟩
      refine ⟨hla, ?_, hc, hlc, ?_⟩
      · simpa [hla, rotate_cons] using hb
      · simpa [hlc, rotateRight_concat] using hd
    · intro ⟨hla, hb, hc, hlc, hd⟩
      refine ⟨?_, hc, ?_, hla, hlc⟩
      · simpa [hla, rotate_cons] using hb
      · simpa [hlc, rotateRight_concat] using hd

  -- Have `s ≠ 0`: otherwise `a` has `lx.length + 1` digits, `b` has at most `lx.length` digits,
  -- `c` has at most `2 * lx.length` digits, `d = a^2` has at least `2 * lx.length + 1` digits.

  _ ↔ ∃ (b c : ℕ) (s f : ℕ) (lx ly : List ℕ),
      digits 10 a = s :: lx ∧
      digits 10 b = lx ++ [s] ∧
      b ^ 2 = c ∧
      digits 10 c = ly ++ [f] ∧
      ofDigits 10 (f :: ly) = a ^ 2 := by
    refine exists₂_congr fun b c ↦ exists₄_congr fun s f lx ly ↦ ?_
    simp only [and_congr_right_iff, and_congr_left_iff, and_imp]
    intro ha_digits hc hc_digits hd
    constructor
    -- For the forward direction, need to prove that `lx` is valid digits.
    · intro hb
      rw [← hb]
      refine digits_ofDigits 10 (by norm_num) _ ?_ ?_
      · intro u hu
        suffices u ∈ digits 10 a from digits_lt_base' this
        simpa [ha_digits, or_comm] using hu
      · suffices s ≠ 0 by simpa using this

        -- Since `a ≠ 0`, we also have `b ≠ 0`.
        have hb_zero : b ≠ 0 := by
          refine mt ?_ ha
          rintro rfl
          -- TODO: Extract as lemma?
          have ofDigits_eq_zero (b : ℕ) (hb : b ≠ 0) (l : List ℕ) :
              ofDigits b l = 0 ↔ ∀ x ∈ l, x = 0 := by
            induction l with
            | nil => simp
            | cons x l IH => simp [ofDigits_cons, hb, IH]
          suffices ofDigits 10 (digits 10 a) = 0 by simpa [ofDigits_digits] using this
          rw [ha_digits]
          simpa [ofDigits_eq_zero 10 (by norm_num), or_comm] using hb

        -- TODO: Move into calc block?
        have hd' : 2 * log 10 a ≤ log 10 (a ^ 2) := le_log_sq (by norm_num) ha
        have hd' : 2 * (log 10 a + 1) ≤ log 10 (a ^ 2) + 1 + 1 := by simpa [mul_add] using hd'
        have hd' : 2 * (digits 10 a).length ≤ (digits 10 (a ^ 2)).length + 1 := by
          simpa [digits_len 10 _ (by norm_num), ha] using hd'
        -- TODO: Write as `suffices (digits 10 (a ^ 2)).length + 2 ≤ 2 * (digits 10 a).length`?
        have hd' : 2 * (digits 10 a).length < (digits 10 (a ^ 2)).length + 2 := lt_add_one_of_le hd'

        contrapose! hd' with hs
        calc _
        _ ≤ (digits 10 c).length + 2 := by
          gcongr
          -- TODO: Extract as lemma?
          -- Follows from ofDigits of length with same length.
          simp [digits_len 10, ha, hb_zero]
          change log 10 (a ^ 2) < (digits 10 c).length
          refine log_lt_of_lt_pow (by simpa using ha) ?_
          rw [← hd, hc_digits]
          convert ofDigits_lt_base_pow_length (b := 10) (by norm_num) ?_ using 2
          · simp
          · suffices ∀ x ∈ ly ++ [f], x < 10 by simpa [or_comm] using this
            rw [← hc_digits]
            intro x
            exact digits_lt_base (by norm_num)

        _ = (digits 10 (b ^ 2)).length + 2 := by rw [← hc]
        _ ≤ 2 * ((digits 10 b).length + 1) := by
          simpa [digits_len 10 _ (by norm_num), hb_zero, mul_add] using
            log_sq_le (by norm_num) hb_zero
        _ ≤ 2 * (digits 10 a).length := by
          gcongr
          -- Follows from `s = 0`.
          rw [ha_digits, ← hb]
          suffices (digits 10 (ofDigits 10 lx)).length ≤ lx.length by
            simpa [hs, ofDigits_append] using this
          -- TODO: Extract as lemma?
          cases eq_or_ne (ofDigits 10 lx) 0 with
          | inl hlx => simp [hlx]
          | inr hlx =>
            rw [digits_len 10 _ (by norm_num) hlx]
            suffices ofDigits 10 lx < 10 ^ lx.length from log_lt_of_lt_pow hlx this
            refine ofDigits_lt_base_pow_length (by norm_num) fun u hu ↦ ?_
            suffices u ∈ digits 10 a from digits_lt_base' this
            exact ha_digits ▸ mem_cons_of_mem s hu

    -- Reverse direction is trivial; digits are guaranteed to satisfy required properties.
    · intro hb_digits
      exact hb_digits ▸ ofDigits_digits 10 b


  -- Introduce additional conditions that must hold.
  -- From `d = (...f) = a ^ 2 = (...s)^2` we know that `s ^ 2 % 10 = f`.
  -- From `c = (f...) = b ^ 2 = (s...)^2` we have constraints outlined above.
  _ ↔ ∃ (b c : ℕ) (s f : ℕ) (lx ly : List ℕ),
      digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s] ∧ b ^ 2 = c ∧
      digits 10 c = ly ++ [f] ∧ ofDigits 10 (f :: ly) = a ^ 2 ∧
      s ^ 2 % 10 = f ∧
      (ly.length = 2 * lx.length ∧ f ∈ Finset.Ico (1 ⊔ s^2) (10 ⊓ (s + 1)^2) ∨
        ly.length = 2 * lx.length + 1 ∧ f ∈ Finset.Ico (1 ⊔ s^2 / 10) (10 ⊓ (s + 1)^2 ⌈/⌉ 10)) := by
    refine exists₂_congr fun b c ↦ exists₄_congr fun s f lx ly ↦ ?_
    simp only [and_congr_right_iff, iff_self_and]
    intro hla hb hc hlc hd
    refine ⟨?_, ?_⟩
    · calc _
      _ = a ^ 2 % 10 := by
        convert congrArg (fun l ↦ ofDigits 10 l ^ 2 % 10) hla.symm using 1
        · simp [ofDigits_cons, pow_mod]
        · simp [ofDigits_digits]
      _ = _ := by
        rw [← hd, ofDigits_cons]
        suffices f < 10 by simpa using this
        suffices f ∈ digits 10 c from digits_lt_base' this
        simp [hlc]
    · exact digits_square_concat 10 (by norm_num) b lx s ly f hb (hc ▸ hlc)

  -- Eliminate the second part of the disjunction.
  _ ↔ ∃ (b c : ℕ) (s f : ℕ) (lx ly : List ℕ),
      digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s] ∧ b ^ 2 = c ∧
      digits 10 c = ly ++ [f] ∧ ofDigits 10 (f :: ly) = a ^ 2 ∧
      s ^ 2 % 10 = f ∧ ly.length = 2 * lx.length ∧ (s = 1 ∨ s = 2 ∨ s = 3) := by
    refine exists₂_congr fun b c ↦ exists₄_congr fun s f lx ly ↦ ?_
    simp only [and_congr_right_iff]
    rintro ha_digits hb_digits hc hc_digits hd rfl
    -- We could also introduce `0 < s` here for `interval_cases`, but it is not necessary.
    have hs_lt : s < 10 := by
      suffices s ∈ digits 10 a from digits_lt_base' this
      simp [ha_digits]
    -- The left side of the disjunction holds for `s = 1, 2, 3` (`f = 1, 4, 9`).
    -- s        =   1    2   3   4   5   6   7   8   9
    -- s^2 % 10 =   1    4   9   6   5   6   9   4   1
    -- f        ∈ 1-3  4-8   9   ∅   ∅   ∅   ∅   ∅   ∅
    have h_left : s ^ 2 % 10 ∈ Finset.Ico (1 ⊔ s ^ 2) (10 ⊓ (s + 1) ^ 2) ↔
        s = 1 ∨ s = 2 ∨ s = 3 := by
      interval_cases s <;> simp
    -- The right side of the disjunction does not hold for any `s`.
    -- s        =  1  2  3    4    5    6    7    8    9
    -- s^2 % 10 =  1  4  9    6    5    6    9    4    1
    -- f        ∈  ∅  ∅  1  1-2  2-3  3-4  4-6  6-8  8-9
    -- We can see that `s^2 % 10` never coincides with feasible values for `f`.
    have h_right : ¬s ^ 2 % 10 ∈ Finset.Ico (1 ⊔ s ^ 2 / 10) (10 ⊓ (s + 1) ^ 2 ⌈/⌉ 10) := by
      interval_cases s <;> simp
    -- Apply these results obtain the required result.
    simp [h_left, h_right]

  -- Since `s < 3` and hence `f = s ^ 2 < 10`, we know that both `c = b ^ 2` and `d` have
  -- exactly `2 k` digits, where `a` has `k` digits. TODO: k + 1?
  -- Let `b = s * 10 ^ k + r` with `r < 10 ^ k`, and therefore `a = 10 * r + s`.
  -- From `c = b ^ 2`, we obtain
  -- `c = (s * 10 ^ k + r) ^ 2 = s ^ 2 * 10 ^ (2 k) + 2 s r * 10 ^ k + r ^ 2`
  -- Shifting the digits gives
  -- `d = 2 s r * 10 ^ (k + 1) + r ^ 2 * 10 + s ^ 2`
  -- Compare this to `d = a ^ 2`:
  -- `d = (10 * r + s) ^ 2 = 10 (r ^ 2 * 10 + 2 r s) + s ^ 2`
  -- Equating these gives
  -- `r (2 s * 10 ^ k + r) = r (r * 10 + 2 s)`
  -- Therefore, either `r = 0`, or `2 s * 10 ^ k + r = r * 10 + 2 s`.
  -- If `r = 0`, then `a = b = s`, `c = d = s ^ 2`, and `d = a ^ 2` is satisfied by `s = 1`.
  -- Otherwise, re-arranging gives
  -- `2 s (10 ^ k - 1) = r (10 - 1)`
  -- `r = (10 ^ k - 1) / 9 * 2 s`
  -- `r = 11...1 * 2 s`
  -- Our three cases are then `a = 22...21`, `a = 44...42`, and `a = 66...63`.
  -- However, the latter two violate the condition that `a ^ 2` has `2 k` digits. (TODO)

  -- Replace `f` with `s ^ 2`.
  -- TODO: Reorder: Make it so that `f` constraint can pop out.
  _ ↔ ∃ (b c : ℕ) (s f : ℕ) (lx ly : List ℕ),
      b ^ 2 = c ∧ (s = 1 ∨ s = 2 ∨ s = 3) ∧ s ^ 2 % 10 = f ∧
      digits 10 a = s :: lx ∧
      digits 10 b = lx ++ [s] ∧
      digits 10 c = ly ++ [f] ∧
      a ^ 2 = ofDigits 10 (f :: ly) ∧
      ly.length = 2 * lx.length := by
    constructor
    · refine fun ⟨b, c, s, f, lx, ly, ha_dig, hb_dig, hc, hc_dig, hd, hf, h_len, hs⟩ ↦ ?_
      exact ⟨b, c, s, f, lx, ly, hc, hs, hf, ha_dig, hb_dig, hc_dig, hd.symm, h_len⟩
    · refine fun ⟨b, c, s, f, lx, ly, hc, hs, hf, ha_dig, hb_dig, hc_dig, hd, h_len⟩ ↦ ?_
      exact ⟨b, c, s, f, lx, ly, ha_dig, hb_dig, hc, hc_dig, hd.symm, hf, h_len, hs⟩

  _ ↔ ∃ (b c : ℕ) (s : ℕ) (lx ly : List ℕ),
      b ^ 2 = c ∧ (s = 1 ∨ s = 2 ∨ s = 3) ∧
      digits 10 a = s :: lx ∧
      digits 10 b = lx ++ [s] ∧
      digits 10 c = ly ++ [s ^ 2] ∧
      a ^ 2 = ofDigits 10 (s ^ 2 :: ly) ∧
      ly.length = 2 * lx.length := by simp

  -- Introduce `k` to denote the number of elements in `lx`.
  -- That is, `a` has `k + 1` digits and `b ^ 2` has `2 k + 1` digits.
  _ ↔ ∃ (b c : ℕ) (s : ℕ) (lx ly : List ℕ) (k : ℕ),
      b ^ 2 = c ∧
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      lx.length = k ∧
      digits 10 a = s :: lx ∧
      digits 10 b = lx ++ [s] ∧
      digits 10 c = ly ++ [s ^ 2] ∧
      a ^ 2 = ofDigits 10 (s ^ 2 :: ly) ∧
      ly.length = 2 * k := by
    refine exists₂_congr fun b c ↦ ?_
    simp

  -- Re-order and eliminate `c`.
  -- TODO: Might not need to re-order here.
  -- TODO: Could eliminate `c` earlier.
  _ ↔ ∃ (s k b : ℕ) (lx ly : List ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      (lx.length = k ∧
        digits 10 a = s :: lx ∧
        digits 10 b = lx ++ [s]) ∧
      (ly.length = 2 * k ∧
        digits 10 (b ^ 2) = ly ++ [s ^ 2] ∧
        -- TODO: Can we have `digits 10 (a ^ 2) = s ^ 2 :: ly` from length of `a ^ 2`?
        -- Do we need it?
        a ^ 2 = ofDigits 10 (s ^ 2 :: ly)) := by
    -- refine exists₃_congr fun s k b ↦ ?_
    constructor
    · rintro ⟨b, _, s, lx, ly, k, rfl, hs, hx_len, ha_dig, hb_dig, hc_dig, hd, hy_len⟩
      exact ⟨s, k, b, lx, ly, hs, ⟨hx_len, ha_dig, hb_dig⟩, hy_len, hc_dig, hd⟩
    · intro ⟨s, k, b, lx, ly, hs, ⟨hx_len, ha_dig, hb_dig⟩, hy_len, hc_dig, hd⟩
      exact ⟨b, _, s, lx, ly, k, rfl, hs, hx_len, ha_dig, hb_dig, hc_dig, hd, hy_len⟩

  -- While we cannot guarantee that `a ^ 2` has `2 k + 1` digits since `ly` could contain
  -- leading zeros, we can guarantee that it has no more digits than `b ^ 2`.
  -- This will later be sufficient, since `a` itself has `k + 1` digits.
  -- Note that we don't *need* it for the `iff condition, but it is easier to derive now.
  -- We could instead write `digits 10 y ≤ 2 * k`.
  -- However, we will soon eliminate `y` anyway.
  _ ↔ ∃ (s k b : ℕ) (x y : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      ((digits 10 x).length = k ∧
        digits 10 a = s :: digits 10 x ∧
        digits 10 b = digits 10 x ++ [s]) ∧
      ((digits 10 (b ^ 2)).length = 2 * k + 1 ∧
        -- (digits 10 (a ^ 2)).length ≤ (digits 10 (b ^ 2)).length ∧
        (digits 10 (a ^ 2)).length ≤ 2 * k + 1 ∧
        y < 10 ^ (2 * k) ∧
        b ^ 2 = y + 10 ^ (2 * k) * s ^ 2 ∧
        a ^ 2 = s ^ 2 + 10 * y) := by
    refine exists₃_congr fun s k b ↦ ?_
    simp only [exists_and_left, exists_and_right, and_congr_right_iff]
    intro hs
    refine and_congr ?_ ?_
    · constructor
      · intro ⟨lx, hlx_len, ha_digits, hb_digits⟩
        use ofDigits 10 lx
        suffices digits 10 (ofDigits 10 lx) = lx by
          simpa [this] using ⟨hlx_len, ha_digits, hb_digits⟩
        refine digits_ofDigits 10 (by norm_num) _ ?_ ?_
        · intro i hi
          suffices i ∈ digits 10 a from digits_lt_base' this
          rw [ha_digits]
          exact mem_cons_of_mem s hi
        · intro h
          simpa [ha_digits, getLast_cons h] using getLast_digit_ne_zero 10 ha

      · intro ⟨x, hx_len, ha_digits, hb_digits⟩
        use digits 10 x

    · constructor
      · intro ⟨ly, hly_len, hb_digits, hd⟩
        refine ⟨?_, ?_, ?_⟩
        · simp [hb_digits, hly_len]
        · rw [hd]
          refine le_trans (digits_ofDigits_len_le_len 10 (by norm_num) _ ?_) ?_
          · simp only [mem_cons, forall_eq_or_imp]
            refine ⟨?_, ?_⟩
            · suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s ^ 2 < 10 from this s hs
              simp
            · intro i hi
              suffices i ∈ digits 10 (b ^ 2) from digits_lt_base' this
              rw [hb_digits]
              exact mem_append_left [s ^ 2] hi
          simp [hly_len]

        use ofDigits 10 ly
        refine ⟨?_, ?_, ?_⟩
        · convert ofDigits_lt_base_pow_length (by norm_num : 1 < 10) ?_ using 2
          · exact hly_len.symm
          · intro i hi
            suffices i ∈ digits 10 (b ^ 2) from digits_lt_base' this
            rw [hb_digits]
            exact mem_append_left [s ^ 2] hi
        · convert congrArg (ofDigits 10) hb_digits
          · simp [ofDigits_digits]
          · simp [ofDigits_append, hly_len]
        · exact hd
      · intro ⟨hc_len, hd_len, y, hy_lt, hc, hd⟩
        have hy_len : (digits 10 y).length ≤ 2 * k := by
          cases eq_or_ne y 0 with
          | inl hy => simp [hy]
          | inr hy =>
            rw [digits_len 10 _ (by norm_num) hy]
            exact log_lt_of_lt_pow hy hy_lt

        use digits 10 y ++ replicate (2 * k - (digits 10 y).length) 0
        -- TODO: Extract as lemma?
        refine ⟨?_, ?_, ?_⟩
        · simp [hy_len]
        · have hs_pos : 0 < s := by
            suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → 0 < s from this s hs
            simp
          have hs_sq_lt : s ^ 2 < 10 := by
            suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s ^ 2 < 10 from this s hs
            simp
          convert (digits_append_zeroes_append_digits (b := 10) (by norm_num) (n := y)
              (m := s ^ 2) (k := (2 * k - (digits 10 y).length)) ?_).symm using 2
          · simp [hc, hy_len]
          · exact (digits_of_lt 10 (s ^ 2) (by simpa using hs_pos.ne') hs_sq_lt).symm
          · exact pos_pow_of_pos 2 hs_pos
        · simpa [ofDigits_cons, ofDigits_append, ofDigits_replicate_zero, ofDigits_digits] using hd


  _ ↔ ∃ (s k b : ℕ) (x y : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      ((digits 10 x).length = k ∧
        digits 10 a = s :: digits 10 x ∧
        digits 10 b = digits 10 x ++ [s]) ∧
      ((digits 10 (b ^ 2)).length = 2 * k + 1 ∧
        -- (digits 10 (a ^ 2)).length ≤ (digits 10 (b ^ 2)).length ∧
        (digits 10 (a ^ 2)).length ≤ 2 * k + 1 ∧
        y < 10 ^ (2 * k) ∧
        b ^ 2 = y + 10 ^ (2 * k) * s ^ 2 ∧
        a ^ 2 = s ^ 2 + 10 * y) := by sorry


  -- Idea: Maybe we should write in terms of `x` and `y` with
  -- `(digits 10 x).length = k` and `(digits 10 y).length ≤ 2 * k`? Then we have...
  -- `digits 10 a = s :: digits 10 x`
  -- `digits 10 b = digits 10 x ++ [s]`
  -- `digits 10 (b ^ 2) = digits 10 y ++ replicate (2 * k - (digits 10 y).length) 0 ++ [s ^ 2]`
  -- `digits 10 (a ^ 2) = s ^ 2 :: digits 10 y`
  -- From this, we easily obtain
  -- `(digits 10 (b ^ 2)).length = 2 * k + 1`
  -- `(digits 10 (a ^ 2)).length ≤ 2 * k + 1`,
  -- as well as
  -- `a = s + 10 * x`
  -- `b = x + 10 ^ k * s`
  -- `b ^ 2 = y + 10 ^ (2 * k) * s ^ 2`
  -- `a ^ 2 = s ^ 2 + 10 * y`
  -- Do we even need to eliminate `b`? Eventually yes...

  -- Still not sure about:
  -- When we obtain `y = x * (x + 2 * s * 10 ^ k) = x * (2 * s + 10 * x)`,
  -- how do we show that this has at most `2 * k` digits, or `y < 10 ^ (2 * k)`?



  -- Eliminate `b` and obtain two equations for `y`.
  -- TODO: Maybe there's no need to eliminate `b`?

  _ ↔ ∃ (s k : ℕ) (x y : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      (digits 10 x).length = k ∧
      digits 10 a = s :: digits 10 x ∧
      (digits 10 ((x + 10 ^ k * s) ^ 2)).length = 2 * k + 1 ∧  -- TODO: Keep `b`? Remove this?
      -- (digits 10 (a ^ 2)).length = 2 * k + 1 ∧
      (digits 10 (a ^ 2)).length ≤ 2 * k + 1 ∧  -- TODO: When to get equality?
      y < 10 ^ (2 * k) ∧  -- TODO: Do we need this? Or need to remove?
      y = x * (x + 2 * s * 10 ^ k) ∧
      y = x * (2 * s + 10 * x) := by
    refine exists₂_congr fun s k ↦ ?_
    rw [exists_comm]
    refine exists_congr fun x ↦ ?_
    rw [exists_comm]
    refine exists_congr fun y ↦ ?_
    simp only [and_assoc, exists_and_left, and_congr_right_iff]
    intro hs hx_len ha_digits

    have ha_eq : a = s + 10 * x := by  -- TODO: Rename `ha`.
      have := congrArg (ofDigits 10) ha_digits
      simpa [ofDigits_digits, ofDigits_cons] using this  -- TODO: why do we need `this`?

    constructor
    · intro ⟨b, hb_digits, hc_len, hd_len, hy_lt, hc, hd⟩
      have hb : b = x + 10 ^ k * s := by
        have := congrArg (ofDigits 10) hb_digits
        simpa [ofDigits_digits, ofDigits_append, hx_len] using this

      refine ⟨hb ▸ hc_len, hd_len, hy_lt, ?_, ?_⟩  -- TODO: avoid re-stating?
      -- ·
      --   suffices log 10 (a ^ 2) = 2 * k by simpa [digits_len 10 _ (by norm_num), ha] using this
      --   have ha_log : log 10 a = k := by
      --     suffices (digits 10 a).length = k + 1 by
      --       simpa [digits_len 10 _ (by norm_num), ha] using this
      --     simpa [ha_digits] using hx_len
      --   rw [← ha_log]
      --   refine le_antisymm ?_ (le_log_sq (by norm_num) ha)

      --   have := ofDigits_lt_base_pow_length (b := 10) (l := (s ^ 2 :: digits 10 y)) (by norm_num)
      --   -- Looks achievable?
      --   sorry

      · rw [hb] at hc
        rw [← add_left_inj (10 ^ (2 * k) * s ^ 2)]
        convert hc.symm using 1
        ring
      · rw [ha_eq] at hd
        rw [← mul_right_inj' (by norm_num : 10 ≠ 0), ← add_right_inj (s ^ 2)]
        convert hd.symm using 1
        ring

    · intro ⟨hc_len, hd_len, hy_lt, hy, hy'⟩
      -- TODO: introduce `b`?
      use ofDigits 10 (digits 10 x ++ [s])  -- Better to simplify here?

      have hs_pos : 0 < s := by
        suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → 0 < s from this s hs
        simp

      refine ⟨?_, ?_⟩
      · refine digits_ofDigits 10 (by norm_num) _ ?_ ?_
        · intro u hu
          suffices u ∈ digits 10 a from digits_lt_base' this
          simpa [ha_digits, or_comm] using hu
        · simpa using hs_pos.ne'
      simp only [ofDigits_append, ofDigits_digits, ofDigits_singleton, hx_len]
      refine ⟨?_, hd_len, hy_lt, ?_, ?_⟩
      · -- Need to keep condition on length of `b ^ 2`?
        -- Maybe we can show it's true?
        -- We know `b` has `s` as leading digit, but `s` could be 3.
        exact hc_len
      · rw [hy]
        ring
      · rw [ha_eq, hy']
        ring


  -- Eliminate `y`.
  _ ↔ ∃ (s k : ℕ) (x : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      (digits 10 x).length = k ∧
      digits 10 a = s :: digits 10 x ∧
      (digits 10 ((x + 10 ^ k * s) ^ 2)).length = 2 * k + 1 ∧  -- TODO: Keep `b`? Remove this?
      -- (digits 10 (a ^ 2)).length = 2 * k + 1 ∧
      (digits 10 (a ^ 2)).length ≤ 2 * k + 1 ∧  -- TODO: When to get equality?
      x * (2 * s + 10 * x) = x * (x + 2 * s * 10 ^ k) := by
    refine exists₃_congr fun s k x ↦ ?_
    simp only [exists_and_left, exists_eq_right_right, and_congr_right_iff, and_iff_right_iff_imp]
    intro hs hx_len ha_dig hc_len hd_len hx
    -- hmm.. not actually sure how we guarantee this? maybe need to keep condition?
    sorry



    -- `c = b ^ 2 = 10 ^ (2 * k) * s ^ 2 + 10 ^ k * 2 * s * x + x ^ 2`
    -- `d = a ^ 2 = 100 * x ^ 2 + 10 * 2 * s * x + s ^ 2`
    -- Now we need the fact that `d` is obtained by rotating `c` to the right.
    -- `c = s ^ 2 * 10 ^ (2 * k) + y`
    -- `c = s ^ 2 * 10 ^ (2 * k) + 10 ^ k * 2 * s * x + x ^ 2`
    --  Therefore `y = 2 * s * x * 10 ^ k + x ^ 2 = x (2 s 10^k + x)`
    -- `d = y * 10 + s ^ 2`
    -- `d = 10 * (x ^ 2 * 10 + 2 * s * x) + s ^ 2`
    -- Therefore `y = x ^ 2 * 10 + 2 * s * x = x (10 x + 2 s)`
    -- Combining these gives
    -- `2 * s * x * 10 ^ k + x ^ 2 = x ^ 2 * 10 + 2 * s * x`
    -- `x * (2 * s * (10 ^ k - 1)) = x * (x * (10 - 1))`
    -- `x = 0` or `2 * s * (10 ^ k - 1) = x * (10 - 1)`

  -- That is, for `k = m + 1`, we have
  -- `digits 10 a = s :: lx = (s :: replicate m (2 * s)) ++ [2 * s]`. Perfect.
  -- When `k = 0`, we have `digits 10 a = [] ++ [s]`.
  -- Therefore, the only condition we need is the number of digits of `a ^ 2`.


  _ ↔ ∃ (s k : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      digits 10 a = s :: replicate k (2 * s) ∧
      -- This is perhaps more messy than keeping `b` or using
      -- `digits _ _ ++ replicate ( - length (digits _ _)) 0`.
      (digits 10 ((ofDigits 10 (replicate k (2 * s)) + 10 ^ k * s) ^ 2)).length = 2 * k + 1 ∧
      (digits 10 (a ^ 2)).length ≤ 2 * k + 1 := by
    refine exists₂_congr fun s k ↦ ?_
    simp only [exists_and_left, and_congr_right_iff]
    intro hs
    -- TODO: Is there a way to obtain this?
    constructor
    · intro ⟨x, hx_len, ha_dig, hc_len, hd_len, hx⟩
      rw [mul_eq_mul_left_iff] at hx
      cases hx with
      -- TODO: Use one result for both branches?
      | inr hx =>
        rcases hx with rfl
        replace hx_len : 0 = k := by simpa using hx_len
        rcases hx_len with rfl
        replace ha_dig : digits 10 a = [s] := by simpa using ha_dig
        have ha : a = s := by
          have := congrArg (ofDigits 10) ha_dig
          simpa [ofDigits_digits] using this
        rcases ha with rfl
        refine ⟨?_, ?_⟩
        · simpa using ha_dig
        · suffices (digits 10 (a ^ 2)).length = 1 by simp [this]
          rw [digits_of_lt]
          · simp
          · simpa using ha
          · suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s ^ 2 < 10 from this a hs
            simp
      | inl hx =>
        have hx : (10 - 1) * x = 2 * s * (10 ^ k - 1) := by
          simp only [tsub_mul, mul_tsub]
          refine tsub_eq_tsub_of_add_eq_add ?_
          convert hx using 1 <;> ring
        -- have hx : x = 2 * s * (10 ^ k - 1) / 9 := Nat.eq_div_of_mul_eq_right (by norm_num) hx
        have hx : x = 2 * s * ((10 ^ k - 1) / 9) := by
          calc _
          _ = 2 * s * (10 ^ k - 1) / 9 := Nat.eq_div_of_mul_eq_right (by norm_num) hx
          _ = _ := Nat.mul_div_assoc _ (Dvd.intro _ (ten_pow_sub_one_eq_nine_mul k).symm)
        rw [ten_pow_sub_one_div_nine] at hx

        refine ⟨?_, ?_, ?_⟩
        · rw [ha_dig, hx, mul_ofDigits]
          simp  -- TODO
          refine digits_ofDigits 10 (by norm_num) _ ?_ ?_
          · suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → 2 * s < 10 by simp [this s hs]
            simp
          · suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s ≠ 0 by simp [this s hs]
            simp
        · simpa [hx, mul_ofDigits] using hc_len
        · -- Could try to convert this to equality using antisymmetry? Not yet necessary?
          exact hd_len

    · intro ⟨ha_dig, hc_len, hd_len⟩

      refine ⟨ofDigits 10 (replicate k (2 * s)), ?_, ?_, ?_, ?_, ?_⟩
      · convert length_replicate k (2 * s) using 2
        refine digits_ofDigits 10 (by norm_num) _ ?_ ?_
        · suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → 2 * s < 10 by simp [this s hs]
          simp
        · suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s ≠ 0 by simp [this s hs]
          simp
      · rw [ha_dig]
        simp  -- TODO
        -- TODO: Feels like we are doing the same thing again.
        refine (digits_ofDigits 10 (by norm_num) _ ?_ ?_).symm
        · suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → 2 * s < 10 by simp [this s hs]
          simp
        · suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s ≠ 0 by simp [this s hs]
          simp

      · -- We need `(digits 10 (b ^ 2)).length = 2 * k + 1` here?
        exact hc_len

      · exact hd_len
      · congr 1
        calc _
        _ = ofDigits 10 (replicate (k + 1) (2 * s)) := by simp [replicate_succ, ofDigits_cons]
        _ = _ := by
          -- TODO: Re-arrange if possible?
          -- simp [replicate_succ', ofDigits_append]
          simp only [replicate_succ', ofDigits_append, length_replicate, ofDigits_singleton]
          ring


  -- _ ↔ ∃ (k s : ℕ) (lx : List ℕ), (digits 10 (a ^ 2)).length = 2 * k + 1 ∧
  --     (s = 1 ∨ s = 2 ∨ s = 3) ∧ replicate k (2 * s) = lx ∧
  --     digits 10 a = s :: lx := by
  --   sorry

  -- Order to extract the length constraint, such that the subsitution
  -- `a = 1 ∨ a = 2 ∨ a = 3` can be obtained via `simp`.
  _ ↔ ∃ k s, (digits 10 (a ^ 2)).length = 2 * k + 1 ∧
      (s = 1 ∨ s = 2 ∨ s = 3) ∧ digits 10 a = s :: replicate k (2 * s) := by
    sorry

  -- _ ↔ ∃ (k s x : ℕ),
  --     (k = 0 ∨ k > 0) ∧
  --     (s = 1 ∨ s = 2 ∨ s = 3) ∧
  --     digits 10 a = s :: replicate k (2 * s) ∧
  --     (digits 10 (a ^ 2)).length = 2 * k + 1 := by
  --   simp only [Nat.eq_zero_or_pos, true_and]

  _ ↔ (a = 1 ∨ a = 2 ∨ a = 3) ∨ (∃ k, digits 10 a = 1 :: replicate (k + 1) 2) := by
    -- Split `k` into `0` and `k + 1`.
    rw [← or_exists_add_one]
    refine or_congr ?_ ?_
    · suffices a = 1 ∨ a = 2 ∨ a = 3 → (digits 10 (a ^ 2)).length = 1 by
        simpa [digits_eq_iff] using this
      -- Verify that `a ^ 2` has one digit in all three cases by substitution.
      clear ha
      revert a
      simp
    · refine exists_congr fun m ↦ ?_
      calc _
      -- TODO: Maybe not necessary?
      _ ↔ (digits 10 (a ^ 2)).length = 2 * (m + 1) + 1 ∧
          (digits 10 a = 1 :: replicate (m + 1) 2 ∨
            digits 10 a = 2 :: replicate (m + 1) 4 ∨
            digits 10 a = 3 :: replicate (m + 1) 6) := by simp
      -- Eliminate the cases `s = 2` and `s = 3`.
      _ ↔ (digits 10 (a ^ 2)).length = 2 * (m + 1) + 1 ∧
          digits 10 a = 1 :: replicate (m + 1) 2 := by
        rw [and_congr_right_iff]
        intro h_len
        refine or_iff_left ?_
        refine not_or_intro ?_ ?_
        · contrapose! h_len with ha_digits
          -- Show that the length property is violated.
          -- Obtain from the fact that the last digit of `a` squared is at least 10.
          rw [len_digits_eq_of_le_getLast_sq] <;> simp [ha_digits, mul_add]
        · contrapose! h_len with ha_digits
          rw [len_digits_eq_of_le_getLast_sq] <;> simp [ha_digits, mul_add]
      -- Drop the constraint on the length since it is satisfied for `s = 1`.
      _ ↔ _ := by
        rw [and_iff_right_iff_imp]
        intro ha_digits
        -- Confirm that the length property holds for `s = 1`.
        rw [len_digits_eq_of_getLast_add_one_sq_lt] <;> simp [ha_digits, mul_add]

  _ ↔ _ := by simp [digits_eq_iff, eq_comm (b := ofDigits _ _)]
