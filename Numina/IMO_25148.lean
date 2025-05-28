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

lemma le_len_digits_sq (b : ℕ) (hb : 1 < b) (n : ℕ) :  -- TODO: Check if `n ≠ 0` required.
    2 * (digits b n).length ≤ (digits b (n ^ 2)).length + 1 := by
  cases n with
  | zero => simp
  | succ n => simpa [digits_len, hb, mul_add] using le_log_sq hb n.add_one_ne_zero

lemma len_digits_sq_le (b : ℕ) (hb : 1 < b) (n : ℕ) :
    (digits b (n ^ 2)).length ≤ 2 * (digits b n).length := by
  cases n with
  | zero => simp
  | succ n => simpa [digits_len, hb, mul_add] using log_sq_le hb n.add_one_ne_zero

lemma len_digits_sq_add_one_eq_or (b : ℕ) (hb : 1 < b) (n : ℕ) :
    (digits b (n ^ 2)).length + 1 = 2 * (digits b n).length ∨
    (digits b (n ^ 2)).length + 1 = 2 * (digits b n).length + 1 := by
  refine le_and_le_add_one_iff.mp ⟨?_, ?_⟩
  · exact le_len_digits_sq b hb n
  · simpa using len_digits_sq_le b hb n

-- lemma log_sq_mem_Icc {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
--     log b (n ^ 2) ∈ Finset.Icc (2 * log b n) (2 * log b n + 1) :=
--   Finset.mem_Icc.mpr ⟨le_log_sq hb hn, log_sq_le hb hn⟩

-- Copied from more recent version of Mathlib.
lemma ofDigits_inj_of_len_eq {b : ℕ} (hb : 1 < b) {L1 L2 : List ℕ}
    (len : L1.length = L2.length) (w1 : ∀ l ∈ L1, l < b) (w2 : ∀ l ∈ L2, l < b)
    (h : ofDigits b L1 = ofDigits b L2) : L1 = L2 := by
  induction' L1 with D L ih generalizing L2
  · simp only [length_nil] at len
    exact (length_eq_zero.mp len.symm).symm
  obtain ⟨d, l, rfl⟩ := exists_cons_of_length_eq_add_one len.symm
  simp only [length_cons, add_left_inj] at len
  simp only [ofDigits_cons] at h
  have eqd : D = d := by
    have H : (D + b * ofDigits b L) % b = (d + b * ofDigits b l) % b := by rw [h]
    simpa [mod_eq_of_lt (w2 d (mem_cons_self _ _)),
      mod_eq_of_lt (w1 D (mem_cons_self _ _))] using H
  simp only [eqd, add_right_inj, mul_left_cancel_iff_of_pos (zero_lt_of_lt hb)] at h
  have := ih len (fun a ha ↦ w1 a <| mem_cons_of_mem D ha)
    (fun a ha ↦ w2 a <| mem_cons_of_mem d ha) h
  rw [eqd, this]


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

lemma mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul {b : ℕ} (hb : 1 < b) {n : ℕ}
    {lx : List ℕ} {x : ℕ} (hx : digits b n = lx ++ [x])
    {ly : List ℕ} {y : ℕ} (hy : digits b (n ^ 2) = ly ++ [y])
    (h_len : ly.length = 2 * lx.length) :
    y ∈ Finset.Ico (x ^ 2) ((x + 1) ^ 2) := by

  have hx_mem := mem_Ico_of_digits_eq_concat hb n x lx hx
  have hy_mem := mem_Ico_of_digits_eq_concat hb (n ^ 2) y ly hy
  rw [h_len] at hy_mem
  simp only [Finset.mem_inter, Finset.mem_Ico]
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

lemma mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul_add_one {b : ℕ} (hb : 1 < b) {n : ℕ}
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


lemma len_eq_or_of_digits_eq_concat {b : ℕ} (hb : 1 < b) {n : ℕ}
    {lx : List ℕ} {x : ℕ} (hx : digits b n = lx ++ [x])
    {ly : List ℕ} {y : ℕ} (hy : digits b (n ^ 2) = ly ++ [y]) :
    ly.length = 2 * lx.length ∨ ly.length = 2 * lx.length + 1 := by
  have hn_zero : n ≠ 0 := by
    suffices digits b n ≠ [] from digits_ne_nil_iff_ne_zero.mp this
    simp [hx]
  suffices log b (n ^ 2) = ly.length ∧ log b n = lx.length by
    rw [← this.1, ← this.2]
    exact log_sq_eq hb hn_zero
  constructor
  · suffices log b (n ^ 2) + 1 = ly.length + 1 by simpa using this
    convert congrArg length hy using 1
    · simp [digits_len, hb, hn_zero]
    · simp
  · suffices log b n + 1 = lx.length + 1 by simpa using this
    convert congrArg length hx using 1
    · simp [digits_len, hb, hn_zero]
    · simp

lemma len_eq_two_mul_of_digits_sq_eq_concat_of_not_mem_Ico {b : ℕ} (hb : 1 < b) {n : ℕ}
    {lx : List ℕ} {x : ℕ} (hn_dig : digits b n = lx ++ [x])
    {ly : List ℕ} {y : ℕ} (hn2_dig : digits b (n ^ 2) = ly ++ [y])
    (hy : y ∉ Finset.Ico (x ^ 2 / b) ((x + 1) ^ 2 ⌈/⌉ b)) :
    ly.length = 2 * lx.length := by
  contrapose! hy with hy_len
  refine mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul_add_one hb hn_dig hn2_dig ?_
  exact (len_eq_or_of_digits_eq_concat hb hn_dig hn2_dig).resolve_left hy_len

lemma len_eq_two_mul_add_one_of_digits_sq_eq_concat_of_not_mem_Ico {b : ℕ} (hb : 1 < b) {n : ℕ}
    {lx : List ℕ} {x : ℕ} (hn_dig : digits b n = lx ++ [x])
    {ly : List ℕ} {y : ℕ} (hn2_dig : digits b (n ^ 2) = ly ++ [y])
    (hy : y ∉ Finset.Ico (x ^ 2) ((x + 1) ^ 2)) :
    ly.length = 2 * lx.length + 1 := by
  contrapose! hy with hy_len
  refine mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul hb hn_dig hn2_dig ?_
  exact (len_eq_or_of_digits_eq_concat hb hn_dig hn2_dig).resolve_right hy_len

lemma digits_square_concat' {b : ℕ} (hb : 1 < b) {n : ℕ}
    {lx : List ℕ} {x : ℕ} (hn_dig : digits b n = lx ++ [x])
    {ly : List ℕ} {y : ℕ} (hn2_dig : digits b (n ^ 2) = ly ++ [y]) :
    ly.length = 2 * lx.length ∧ y ∈ Finset.Ico (x ^ 2) ((x + 1) ^ 2) ∨
    ly.length = 2 * lx.length + 1 ∧ y ∈ Finset.Ico (x ^ 2 / b) ((x + 1) ^ 2 ⌈/⌉ b) := by
  -- TODO: Revise comment.
  -- Split into two cases.
  -- If `n` has `k + 1` digits, then `n ^ 2` has either `2 k + 1` or `2 k + 2` digits.
  -- When it has `2 k + 1`, we know that `x ^ 2 < b` and there was no carry to change this.
  refine (len_eq_or_of_digits_eq_concat hb hn_dig hn2_dig).imp ?_ ?_
  · refine fun hy_len ↦ ⟨hy_len, ?_⟩
    exact mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul hb hn_dig hn2_dig hy_len
  · refine fun hy_len ↦ ⟨hy_len, ?_⟩
    exact mem_Ico_of_digits_sq_eq_concat_of_len_eq_two_mul_add_one hb hn_dig hn2_dig hy_len

-- Build in the digit constraint for easier simplification.
-- TODO: Eliminate?
lemma digits_square_concat (b : ℕ) (hb : 1 < b) (n : ℕ)
    (lx : List ℕ) (x : ℕ) (ly : List ℕ) (y : ℕ)
    (hx : digits b n = lx ++ [x]) (hy : digits b (n ^ 2) = ly ++ [y]) :
    ly.length = 2 * lx.length ∧ y ∈ Finset.Ico (1 ⊔ x ^ 2) (b ⊓ (x + 1) ^ 2) ∨
    ly.length = 2 * lx.length + 1 ∧ y ∈ Finset.Ico (1 ⊔ x ^ 2 / b) (b ⊓ (x + 1) ^ 2 ⌈/⌉ b) := by
  simp only [← Finset.Ico_inter_Ico]
  suffices y ∈ Finset.Ico 1 b by simpa [this] using digits_square_concat' hb hx hy
  rw [Finset.mem_Ico]
  constructor
  · rw [one_le_iff_ne_zero]
    convert getLast_digit_ne_zero b (m := n ^ 2) ?_
    · simp [hy]
    · suffices digits b (n ^ 2) ≠ [] from digits_ne_nil_iff_ne_zero.mp this
      simp [hy]
  · suffices y ∈ digits b (n ^ 2) from digits_lt_base hb this
    simp [hy]


lemma len_digits_eq_of_le_getLast_sq {b : ℕ} (hb : 1 < b) (n : ℕ)
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

lemma len_digits_eq_of_getLast_add_one_sq_lt {b : ℕ} (hb : 1 < b) (n : ℕ)
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

lemma len_digits_add_one_eq_of_getLast_add_one_sq_lt {b : ℕ} (hb : 1 < b) (n : ℕ)
    (hx : ∃ h, ((digits b n).getLast h + 1) ^ 2 < b) :
    (digits b (n ^ 2)).length + 1 = 2 * (digits b n).length := by
  rcases hx with ⟨hn_nil, hx⟩
  suffices (b.digits (n ^ 2)).length = 2 * (b.digits n).length - 1 by
    refine (eq_tsub_iff_add_eq_of_le ?_).mp this
    simpa [one_le_iff_ne_zero] using hn_nil
  exact len_digits_eq_of_getLast_add_one_sq_lt hb n (fun _ ↦ hx)

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

-- TODO: rename
lemma combined_result {s k : ℕ} (hs_ne : s ≠ 0) (hs_lt : 2 * s < 10) (x : ℕ) :
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
      digits 10 a = la ∧
      b = ofDigits 10 (la.rotate 1) ∧
      digits 10 (b ^ 2) = lc ∧
      a ^ 2 = ofDigits 10 lc.rotateRight := by
    simp only [eq_comm (a := a ^ 2)]
    simp

  -- Separate the digit being moved from the rest of the list.
  _ ↔ ∃ (b : ℕ) (la lc : List ℕ) (s f : ℕ) (lx ly : List ℕ),
      digits 10 a = la ∧
      b = ofDigits 10 (la.rotate 1) ∧
      digits 10 (b ^ 2) = lc ∧
      a ^ 2 = ofDigits 10 lc.rotateRight ∧
      la = s :: lx ∧
      lc = ly ++ [f] := by
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
      simpa [ha_dig, mul_add] using le_len_digits_sq 10 (by norm_num) a
    -- ...with the maximum number of digits obtained by rotating `b ^ 2`.
    calc (digits 10 (a ^ 2)).length
    _ ≤ (f :: ly).length := by
      rw [ha2]
      refine digits_ofDigits_len_le_len 10 (by norm_num) (f :: ly) ?_
      intro i hi
      suffices i ∈ digits 10 (b ^ 2) from digits_lt_base' this
      simpa [hb2, or_comm] using hi
    _ = (digits 10 (b ^ 2)).length := by simp [hb2]
    _ ≤ 2 * (digits 10 b).length := len_digits_sq_le 10 (by norm_num) b
    _ ≤ _ := by
      gcongr
      convert digits_ofDigits_len_le_len 10 (by norm_num) lx ?_
      · simpa [hs, ofDigits_append] using hb
      · intro i hi
        suffices i ∈ digits 10 a from digits_lt_base' this
        simp [ha_dig, hi]

  _ ↔ ∃ (b c : ℕ) (s f : ℕ) (lx ly : List ℕ),
      digits 10 a = s :: lx ∧
      digits 10 b = lx ++ [s] ∧
      b ^ 2 = c ∧
      digits 10 c = ly ++ [f] ∧
      ofDigits 10 (f :: ly) = a ^ 2 := by
    sorry

  -- Identify the `(s, f)` which are feasible.
  -- From `d = (...f) = a ^ 2 = (...s) ^ 2` we know that `s ^ 2 % 10 = f`.
  -- From `c = (f...) = b ^ 2 = (s...) ^ 2` we have constraints outlined above.

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

  _ ↔ ∃ (s k b x y : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      ((digits 10 x).length = k ∧
        digits 10 a = s :: digits 10 x ∧
        digits 10 b = digits 10 x ++ [s]) ∧
      ((digits 10 y).length ≤ 2 * k ∧
        digits 10 (b ^ 2) = digits 10 y ++ replicate (2 * k - (digits 10 y).length) 0 ++ [s ^ 2] ∧
        digits 10 (a ^ 2) = s ^ 2 :: digits 10 y) := by
    refine exists₃_congr fun s k b ↦ ?_
    simp only [exists_and_left, exists_and_right, and_congr_right_iff]
    intro hs
    -- Group into separate statements for `x` and `y`, treat each separately.
    refine and_congr ?_ ?_
    · -- The reverse direction for `x` is trivial.
      refine ⟨?_, Exists.imp' (digits 10) fun x ↦ id⟩
      intro ⟨lx, hlx_len, ha_digits, hb_digits⟩
      use ofDigits 10 lx
      -- To show the forward direction, replace `digits 10 (ofDigits 10 lx)` with `lx`.
      suffices digits 10 (ofDigits 10 lx) = lx by
        simpa [this] using ⟨hlx_len, ha_digits, hb_digits⟩
      refine digits_ofDigits 10 (by norm_num) _ ?_ ?_
      · intro i hi
        suffices i ∈ digits 10 a from digits_lt_base' this
        simpa [ha_digits] using mem_cons_of_mem s hi
      · intro h
        simpa [ha_digits, getLast_cons h] using getLast_digit_ne_zero 10 ha

    · have hs_pos : 0 < s := by
        suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → 0 < s from this s hs
        simp
      have hs2_digits : digits 10 (s ^ 2) = [s ^ 2] := by
        refine digits_of_lt 10 (s ^ 2) ?_ ?_
        · exact pow_ne_zero 2 hs_pos.ne'
        · suffices ∀ s, s = 1 ∨ s = 2 ∨ s = 3 → s ^ 2 < 10 from this s hs
          simp

      constructor
      · intro ⟨ly, hly_len, hc_dig, hd⟩
        use ofDigits 10 ly
        refine ⟨?_, ?_, ?_⟩
        · refine le_of_le_of_eq ?_ hly_len
          refine digits_ofDigits_len_le_len 10 (by norm_num) ly fun i hi ↦ ?_
          exact digits_lt_base' (hc_dig ▸ mem_append_left [s ^ 2] hi)
        · convert hc_dig
          rw [← hly_len]
          refine ofDigits_inj_of_len_eq (b := 10) (by norm_num) ?_ ?_ ?_ ?_
          · simp only [length_append, length_replicate]
            rw [add_tsub_cancel_of_le]
            refine digits_ofDigits_len_le_len 10 ((by norm_num)) ly ?_
            -- Note: Repeated below.
            exact fun i hi ↦ digits_lt_base' (hc_dig ▸ mem_append_left [s ^ 2] hi)
          · simp only [mem_append, mem_replicate]
            intro i hi
            exact hi.elim digits_lt_base' fun ⟨_, hi⟩ ↦ by simp [hi]
          · exact fun i hi ↦ digits_lt_base' (hc_dig ▸ mem_append_left [s ^ 2] hi)
          simp [ofDigits_append, ofDigits_replicate_zero, ofDigits_digits]

        · -- refine ofDigits_inj_of_len_eq (b := 10) (by norm_num) ?_ ?_ ?_ ?_
          -- · rw [hd]
          --   simp [ofDigits_cons]
          --   -- Maybe it's not so useful... Still need to prove length equal.
          --   sorry
          -- · sorry
          -- · sorry
          -- sorry

          rw [hd, ofDigits_cons]
          -- TODO: Could extract as lemma (like digits_append_digits).
          have := digits_append_digits (b := 10) (n := s ^ 2) (m := ofDigits 10 ly) (by norm_num)
          simpa [hs2_digits] using this.symm  -- TODO: Need to instantiate first?

      · intro ⟨y, hy_len, hc_dig, hd_dig⟩
        use digits 10 y ++ replicate (2 * k - (digits 10 y).length) 0
        refine ⟨?_, hc_dig, ?_⟩
        · simp [hy_len]
        · convert congrArg (ofDigits 10) hd_dig using 1
          · simp [ofDigits_digits]
          · simp [ofDigits_cons, ofDigits_append, ofDigits_replicate_zero, ofDigits_digits]

  -- Re-order.
  _ ↔ ∃ (s k b x y : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      digits 10 a = s :: digits 10 x ∧
      digits 10 b = digits 10 x ++ [s] ∧
      (digits 10 x).length = k ∧
      (digits 10 y).length ≤ 2 * k ∧
      digits 10 (b ^ 2) = digits 10 y ++ replicate (2 * k - (digits 10 y).length) 0 ++ [s ^ 2] ∧
      digits 10 (a ^ 2) = s ^ 2 :: digits 10 y := by
    refine exists₅_congr fun s k b x y ↦ ?_
    simp only [and_congr_right_iff]
    intro hs
    simp only [← and_assoc, and_congr_left_iff]
    intro ha2_dig hb2_dig hy_len
    simp only [and_assoc]
    constructor
    · exact fun ⟨hx_len, ha_dig, hb_dig⟩ ↦ ⟨ha_dig, hb_dig, hx_len⟩
    · exact fun ⟨ha_dig, hb_dig, hx_len⟩ ↦ ⟨hx_len, ha_dig, hb_dig⟩

  -- Eliminate constraint on length of `a ^ 2, b ^ 2`.
  -- Since this is used to eliminate `s = 2, 3` when `k ≠ 0`, must split cases here.
  _ ↔ ∃ (s k b x : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      digits 10 a = s :: digits 10 x ∧
      digits 10 b = digits 10 x ++ [s] ∧
      (k = 0 ∧ x = 0 ∨ k ≠ 0 ∧ s = 1 ∧ digits 10 x = replicate k (2 * s)) := by
    refine exists₄_congr fun s k b x ↦ ?_
    simp only [exists_and_left, and_congr_right_iff]
    intro hs ha_dig hb_dig

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

    cases eq_or_ne k 0 with
    | inl hk =>
      rcases hk with rfl
      suffices x = 0 → digits 10 (b ^ 2) = [s ^ 2] ∧ digits 10 (a ^ 2) = [s ^ 2] by
        simpa [digits_eq_nil_iff_eq_zero]
      rintro rfl
      convert And.intro hs2_dig hs2_dig
      · have := congrArg (ofDigits 10) hb_dig
        simpa [ofDigits_digits] using this  -- TODO: why??
      · have := congrArg (ofDigits 10) ha_dig
        simpa [ofDigits_digits] using this

    | inr hk =>
      simp only [hk, false_and, ne_eq, not_false_eq_true, true_and, false_or]

      have ha : a = s + 10 * x := by
        have := congrArg (ofDigits 10) ha_dig
        simpa [ofDigits_digits, ofDigits_cons] using this  -- TODO: why??

      -- Not sure how to get nice condition from here.
      constructor
      · intro ⟨hx_len, y, hy_len, hb2_dig, ha2_dig⟩

        have hb : b = x + 10 ^ k * s := by
          have := congrArg (ofDigits 10) hb_dig
          simpa [ofDigits_digits, ofDigits_append, hx_len] using this

        -- TODO: long?
        have hx : x + 2 * s * 10 ^ k = 2 * s + 10 * x := by
          have ha2 : a ^ 2 = s ^ 2 + 10 * y := by
            have := congrArg (ofDigits 10) ha2_dig
            simpa [ofDigits_digits, ofDigits_cons, hy_len] using this
          have hb2 : b ^ 2 = y + 10 ^ (2 * k) * s ^ 2 := by
            have := congrArg (ofDigits 10) hb2_dig
            simpa [ofDigits_digits, ofDigits_replicate_zero, ofDigits_append, -append_assoc,
              ← pow_add, hy_len] using this

          rw [ha] at ha2
          rw [hb] at hb2

          have hx_zero : x ≠ 0 := by
            refine mt (fun h ↦ ?_) hk
            simp [← hx_len, h]

          have ha2 : y = x * (2 * s + 10 * x) := by
            suffices s ^ 2 + 10 * y = s ^ 2 + 10 * (x * (2 * s + 10 * x)) by
              simpa [hx_zero] using this
            rw [← ha2]
            ring
          have hb2 : y = x * (x + 2 * s * 10 ^ k) := by
            suffices y + 10 ^ (2 * k) * s ^ 2 = x * (x + 2 * s * 10 ^ k) + 10 ^ (2 * k) * s ^ 2 by
              simpa using this
            rw [← hb2]
            ring

          have hy := hb2.symm.trans ha2
          simpa [hx_zero] using hy

        have hx_dig : digits 10 x = replicate k (2 * s) :=
          (combined_result hs_zero hs_two_mul_lt x).mp hx

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
        refine len_digits_eq_of_le_getLast_sq (b := 10) (by norm_num) a ?_
        suffices 10 ≤ (2 * s) ^ 2 by simpa [ha_dig, hx_dig] using this
        suffices ∀ s, s = 2 ∨ s = 3 → 10 ≤ (2 * s) ^ 2 from this s hs
        simp

      · intro ⟨hs, hx_dig⟩

        let y := x * (2 * s + 10 * x)
        -- TODO: Need to use `combined_result` twice?
        have hx : x + 2 * s * 10 ^ k = 2 * s + 10 * x :=
          (combined_result hs_zero hs_two_mul_lt x).mpr hx_dig

        have hx_len : (digits 10 x).length = k := by
          have := congrArg length hx_dig
          simpa using this
        refine ⟨hx_len, ?_⟩

        -- TODO: avoid doing this twice?
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

        -- Rewrite `k` as `m + 1` for simplification.
        obtain ⟨m, hm⟩ : ∃ m, m + 1 = k := exists_add_one_eq.mpr (zero_lt_of_ne_zero hk)

        have ha_nil : digits 10 a ≠ [] := by simp [ha_dig]
        -- TOD: Might be nicer to use `_.length = _ - 1` here?
        have ha2_len : (digits 10 (a ^ 2)).length + 1 = 2 * (digits 10 a).length :=
          len_digits_add_one_eq_of_getLast_add_one_sq_lt (b := 10) (by norm_num) a
            ⟨ha_nil, by simp [ha_dig, hx_dig, hs, ← hm]⟩

        have ha2_dig : digits 10 (a ^ 2) = s ^ 2 :: digits 10 y := by
          calc _
          _ = digits 10 (s ^ 2) ++ digits 10 y := by
            rw [digits_append_digits (b := 10) (by norm_num)]
            simp only [hs2_dig, length_singleton]
            congr 1
            convert ha2 using 1
            ring
          _ = s ^ 2 :: digits 10 y := by simp [hs2_dig]

        -- TODO: Could strengthen assumption? Here we can prove stronger. Could even remove zeros?
        have hy_len : (digits 10 y).length = 2 * k := by
          suffices (digits 10 y).length + 2 = 2 * (k + 1) by simpa [mul_add]
          calc (digits 10 y).length + 2
          _ = (digits 10 (a ^ 2)).length + 1 := by simp [ha2_dig]
          _ = 2 * (digits 10 a).length := by rw [ha2_len]
          _ = 2 * (k + 1) := by simp [ha_dig, hx_len]

        use y
        refine ⟨?_, ?_, ?_⟩
        · exact hy_len.le
        · -- TODO: cleanup
          rw [hy_len]
          simp
          rw [← hs2_dig]
          rw [digits_append_digits (b := 10) (by norm_num)]
          rw [hb2]
          congr 1
          rw [hy_len]
          ring
        · exact ha2_dig

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
        rcases h with ⟨hk, hs, ha_dig⟩
        have hx_dig : digits 10 (ofDigits 10 (replicate k (2 * s))) = replicate k (2 * s) := by
          refine digits_ofDigits 10 (by norm_num) _ ?_ ?_
          · simp [hs]
          · simp [hs]
        have hb_dig :
            digits 10 (ofDigits 10 (replicate k (2 * s) ++ [s])) = replicate k (2 * s) ++ [s] := by
          refine digits_ofDigits 10 (by norm_num) _ ?_ ?_
          · simp [hk, hs]
          · simp [hs]
        use (ofDigits 10 (replicate k (2 * s) ++ [s]))
        use (ofDigits 10 (replicate k (2 * s)))
        rw [hx_dig, hb_dig]
        exact ⟨ha_dig, rfl, .inr ⟨hk, hs, rfl⟩⟩

  _ ↔ (a = 1 ∨ a = 2 ∨ a = 3) ∨ (∃ k, digits 10 a = 1 :: replicate (k + 1) 2) := by
    constructor
    · intro ⟨s, k, hs, h⟩
      refine h.imp ?_ ?_
      · rintro ⟨hk, rfl⟩
        exact hs
      · rintro ⟨hk, rfl, ha_dig⟩
        use k - 1  -- TODO
        convert ha_dig
        exact succ_pred_eq_of_ne_zero hk

    · intro h
      cases h with
      | inl ha =>
        use a, 0
        simpa using ha
      | inr h =>
        rcases h with ⟨k, ha_dig⟩
        use 1, k + 1
        simpa using ha_dig

  _ ↔ _ := by simp [digits_eq_iff, eq_comm (b := ofDigits _ _)]
