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

lemma le_length_digits_sq {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) : 2 * log b n ≤ log b (n ^ 2) := by
  refine le_log_of_pow_le hb ?_
  rw [mul_comm, pow_mul]
  refine Nat.pow_le_pow_left ?_ 2
  exact pow_log_le_self b hn

-- TODO: Might be more elegant to generalize power.
lemma length_digits_sq_le {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b (n ^ 2) ≤ 2 * log b n + 1 := by
  suffices log b (n ^ 2) < 2 * (log b n + 1) from le_of_lt_succ this
  refine Nat.log_lt_of_lt_pow (by simpa) ?_
  rw [mul_comm, pow_mul]
  gcongr
  exact lt_pow_succ_log_self hb n

-- lemma length_digits_sq_mem_Icc {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
--     log b (n ^ 2) ∈ Finset.Icc (2 * log b n) (2 * log b n + 1) :=
--   Finset.mem_Icc.mpr ⟨le_length_digits_sq hb hn, length_digits_sq_le hb hn⟩

-- TODO: Rename to reflect `log`.
lemma length_digits_sq {b n : ℕ} (hb : 1 < b) (hn : n ≠ 0) :
    log b (n ^ 2) = 2 * log b n ∨ log b (n ^ 2) = 2 * log b n + 1 :=
  le_and_le_add_one_iff.mp ⟨le_length_digits_sq hb hn, length_digits_sq_le hb hn⟩

-- When we square an `n`-digit number with leading digit `x`, the result may have `2 * n` or
-- `2 * n + 1` digits. The map of leading digits is monotonic except for this discontinuity.
-- Therefore, we have to consider whether `x ^ 2 < b ≤ (x + 1) ^ 2`.

lemma square_mem_Ico (n x b k : ℕ) (hn : n ∈ Set.Ico (x * b ^ k) ((x + 1) * b ^ k)) :
    n ^ 2 ∈ Set.Ico (x ^ 2 * b ^ (2 * k)) ((x + 1) ^ 2 * b ^ (2 * k)) := by
  rw [Set.mem_Ico] at hn
  refine ⟨?_, ?_⟩
  · convert Nat.pow_le_pow_left hn.1 2 using 1
    ring
  · convert Nat.pow_lt_pow_left hn.2 two_ne_zero using 1
    ring

-- Similar to `Nat.log_eq_iff` except it accounts for the leading digit.
lemma mem_Ico_of_digits_eq_append_singleton {b : ℕ} (hb : 1 < b) (n x : ℕ) (l : List ℕ)
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

lemma digits_square_append_singleton (b : ℕ) (hb : 1 < b) (n x y : ℕ) (lx ly : List ℕ)
    (hx : digits b n = lx ++ [x]) (hy : digits b (n ^ 2) = ly ++ [y]) :
    ly.length = 2 * lx.length ∧ y ∈ Finset.Ico (1 ⊔ x ^ 2) (b ⊓ (x + 1) ^ 2) ∨
    ly.length = 2 * lx.length + 1 ∧ y ∈ Finset.Ico (1 ⊔ x ^ 2 / b) (b ⊓ (x + 1) ^ 2 ⌈/⌉ b) := by
  have hn_zero : n ≠ 0 := by
    suffices digits b n ≠ [] from digits_ne_nil_iff_ne_zero.mp this
    simp [hx]

  have hx_mem := mem_Ico_of_digits_eq_append_singleton hb n x lx hx
  have hy_mem := mem_Ico_of_digits_eq_append_singleton hb (n ^ 2) y ly hy

  -- Split into two cases.
  -- If `n` has `k + 1` digits, then `n ^ 2` has either `2 k + 1` or `2 k + 2` digits.
  -- When it has `2 k + 1`, we know that `x ^ 2 < b` and there was no carry to change this.
  -- TODO: Replace `log` lemma with `length ∘ digits` lemma?
  refine Or.imp (fun h_len ↦ ?_) (fun h_len ↦ ?_) (length_digits_sq hb hn_zero)
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

lemma rotateRight_append_singleton (l : List ℕ) (x : ℕ) :
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

lemma ten_pow_sub_one_div_nine (n : ℕ) :
    (10 ^ n - 1) / 9 = ofDigits 10 (replicate n 1) := by
  refine Nat.div_eq_of_eq_mul_right (by norm_num) ?_
  refine Nat.sub_eq_of_eq_add ?_
  exact ten_pow_eq_nine_mul_replicate_add_one n


theorem number_theory_25148 {a : ℕ} (ha : a ≠ 0) :
    d a = a ^ 2 ↔ a ∈ Set.range (fun n ↦ ofDigits 10 (1 :: replicate n 2)) ∪ {2, 3} := by
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
      · simpa [hlc, rotateRight_append_singleton] using hd
    · intro ⟨hla, hb, hc, hlc, hd⟩
      refine ⟨?_, hc, ?_, hla, hlc⟩
      · simpa [hla, rotate_cons] using hb
      · simpa [hlc, rotateRight_append_singleton] using hd

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
        have hd' : 2 * log 10 a ≤ log 10 (a ^ 2) := le_length_digits_sq (by norm_num) ha
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
            length_digits_sq_le (by norm_num) hb_zero
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
    · exact digits_square_append_singleton 10 (by norm_num) b s f lx ly hb (hc ▸ hlc)

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
      digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s] ∧
      digits 10 c = ly ++ [f] ∧ ofDigits 10 (f :: ly) = a ^ 2 ∧
      ly.length = 2 * lx.length := by
    -- TODO
    sorry
  _ ↔ ∃ (b c : ℕ) (s : ℕ) (lx ly : List ℕ),
      b ^ 2 = c ∧ (s = 1 ∨ s = 2 ∨ s = 3) ∧
      digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s] ∧
      digits 10 c = ly ++ [s ^ 2] ∧ ofDigits 10 (s ^ 2 :: ly) = a ^ 2 ∧
      ly.length = 2 * lx.length := by simp

  -- Goal: Introduce constraint `x * (2 * s * 10 ^ k + x) = x * (x * 10 + 2 * s)`
  -- where `x = ofDigits 10 lx`, with `x < 10 ^ k`.
  -- First step: Introduce `k` and `x`.

  _ ↔ ∃ (b c : ℕ) (s : ℕ) (lx ly : List ℕ) (k : ℕ),
      b ^ 2 = c ∧
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      lx.length = k ∧
      digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s] ∧
      digits 10 c = ly ++ [s ^ 2] ∧ ofDigits 10 (s ^ 2 :: ly) = a ^ 2 ∧
      ly.length = 2 * k := by
    -- simp? [-exists_eq_or_imp]
    refine exists₂_congr fun b c ↦ ?_
    simp
    -- simp only [exists_and_left, exists_eq_left', exists_eq_left]

  -- Introduce `x` without eliminating `lx`.
  -- This is because it's easier to require e.g. `digits 10 a = s :: lx` than
  -- require that `lx` is a valid digit list.


  _ ↔ ∃ (lx ly : List ℕ) (s : ℕ) (c b k : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      lx.length = k ∧
      b ^ 2 = c ∧
      digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s] ∧
      digits 10 c = ly ++ [s ^ 2] ∧ ofDigits 10 (s ^ 2 :: ly) = a ^ 2 ∧
      ly.length = 2 * k := by
    sorry
  -- Re-order such that `b` is substituted with `x + 10 ^ k * s`.
  -- TODO: Might not be needed since we use `exists_congr` anyway?
  _ ↔ ∃ (lx ly : List ℕ) (s : ℕ) (c b k x : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      lx.length = k ∧
      ofDigits 10 lx = x ∧
      x + 10 ^ k * s = b ∧
      b ^ 2 = c ∧
      digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s] ∧
      digits 10 c = ly ++ [s ^ 2] ∧ ofDigits 10 (s ^ 2 :: ly) = a ^ 2 ∧
      ly.length = 2 * k := by
    refine exists₃_congr fun lx ly s ↦ ?_
    refine exists₃_congr fun c b k ↦ ?_
    simp only [exists_and_left, exists_eq_left', and_congr_right_iff, iff_and_self, and_imp]
    intro hs hx_len hc ha_digits hb_digits hc_digits hd hy_len
    convert congrArg (ofDigits 10) hb_digits.symm using 1
    · simp [ofDigits_append, hx_len]
    · simp [ofDigits_digits]

  -- From here, we can eliminate `lx` and `ly`.

  _ ↔ ∃ (s : ℕ) (b k x : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      (digits 10 x).length = k ∧
      -- x < 10 ^ k ∧
      (digits 10 a).length = k + 1 ∧
      x + 10 ^ k * s = b ∧
      -- b ^ 2 = c ∧
      s + 10 * x = a ∧
      (digits 10 (b ^ 2)).length = 2 * k + 1 ∧
      -- s ^ 2 + 10 * y = a ^ 2 ∧
      (digits 10 (a ^ 2)).length = 2 * k + 1 := by
    sorry

  -- See whether this is enough to obtain the condition.
  _ ↔ ∃ (s k x b : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      x + 10 ^ k * s = b ∧
      s + 10 * x = a ∧
      (digits 10 x).length = k ∧
      (digits 10 a).length = k + 1 ∧  -- for convenience
      (digits 10 (b ^ 2)).length = 2 * k + 1 ∧
      (digits 10 (a ^ 2)).length = 2 * k + 1 := by
    -- simp [-exists_eq_or_imp]
    sorry

  _ ↔ ∃ (s k x b : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      x + 10 ^ k * s = b ∧
      s + 10 * x = a ∧
      (digits 10 x).length = k ∧
      (digits 10 a).length = k + 1 ∧  -- for convenience
      (digits 10 (b ^ 2)).length = 2 * k + 1 ∧
      (digits 10 (a ^ 2)).length = 2 * k + 1 ∧
      x * (2 * s * 10 ^ k + x) = x * (x * 10 + 2 * s) := by
    refine exists₄_congr fun s k x b ↦ ?_
    simp only [and_congr_right_iff, iff_self_and]
    intro hs hb ha hx_len ha_len hc_len hd_len
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
    sorry


  -- How to most easily check that the numbers starting with 4 and 6 violate the length?
  -- Any number greater than 33..3?
  -- Can we use our existing condition for the digits of the square?

  -- That is, for `k = m + 1`, we have
  -- `digits 10 a = s :: lx = (s :: replicate m (2 * s)) ++ [2 * s]`. Perfect.
  -- When `k = 0`, we have `digits 10 a = [] ++ [s]`.
  -- Therefore, the only condition we need is the number of digits of `a ^ 2`.
  _ ↔ ∃ (k s : ℕ),
      (s = 1 ∨ s = 2 ∨ s = 3) ∧
      digits 10 a = s :: replicate k (2 * s) ∧
      (digits 10 (a ^ 2)).length = 2 * k + 1 := by
    sorry

  -- _ ↔ ∃ (k s x : ℕ),
  --     (k = 0 ∨ k > 0) ∧
  --     (s = 1 ∨ s = 2 ∨ s = 3) ∧
  --     digits 10 a = s :: replicate k (2 * s) ∧
  --     (digits 10 (a ^ 2)).length = 2 * k + 1 := by
  --   simp only [Nat.eq_zero_or_pos, true_and]

  _ ↔ (a = 1 ∨ a = 2 ∨ a = 3) ∨ (∃ k, digits 10 a = 1 :: replicate (k + 1) 2) := by
    rw [← or_exists_add_one]
    refine or_congr ?_ ?_
    · simp
      -- Need to rewrite `digits 10 a = [s]` as `a = s`?
      sorry
    · refine exists_congr fun k ↦ ?_
      simp [replicate_succ']
      simp only [← cons_append]
      -- Hmm... Need to have `v` and `lv` to use our definition...
      -- Just use `getLast` and `take`?
      have h (s v lv) := digits_square_append_singleton 10 (by norm_num) a (2 * s) v
        (s :: replicate k (2 * s)) lv
      -- A number starting with 2 has square starting with 4-9.
      have h₁ := h 1
      simp [ceilDiv_eq_add_pred_div] at h₁
      -- A number starting with 4 has square starting with 1-2 and an extra digit.
      have h₂ := h 2
      simp [ceilDiv_eq_add_pred_div] at h₂
      -- A number starting with 6 has square starting with 3-4 and an extra digit.
      have h₃ := h 3
      simp [ceilDiv_eq_add_pred_div] at h₃
      sorry

    -- simp only [exists_and_left]
    -- simp only [exists_const]  -- TODO: move condition?
    -- rw [exists_eq_or_imp]
    -- refine or_congr ?_ ?_
    -- · sorry
    -- · refine exists_congr fun k ↦ ?_
    --   simp only [and_congr_right_iff]
    --   intro hk
    --   simp
    --   -- Prefer to take `cases k` to have `k + 1`.
    --   have (s m : ℕ) : s :: replicate (m + 1) (2 * s) = (s :: replicate m (2 * s)) ++ [2 * s] := by
    --     simp [replicate_succ']

    --   sorry


  -- -- Re-order.
  -- _ ↔ ∃ (s : ℕ) (k : ℕ) (lx ly : List ℕ) (b c : ℕ),
  --     (s = 1 ∨ s = 2 ∨ s = 3) ∧
  --     b ^ 2 = c ∧
  --     lx.length = k ∧
  --     digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s] ∧
  --     digits 10 c = ly ++ [s ^ 2] ∧ ofDigits 10 (s ^ 2 :: ly) = a ^ 2 ∧
  --     ly.length = 2 * k := by
  --   sorry

  -- _ ↔ ∃ (s : ℕ) (x k : ℕ) (lx ly : List ℕ) (b c : ℕ),
  --     (s = 1 ∨ s = 2 ∨ s = 3) ∧
  --     b ^ 2 = c ∧
  --     b = x + s * 10 ^ k ∧
  --     x = ofDigits 10 lx ∧
  --     lx.length = k ∧
  --     digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s] ∧
  --     digits 10 c = ly ++ [s ^ 2] ∧ ofDigits 10 (s ^ 2 :: ly) = a ^ 2 ∧
  --     ly.length = 2 * k := by
  --   -- refine exists₃_congr fun b c s ↦ ?_
  --   -- simp only [exists_and_left, exists_eq_left', exists_eq_left]
  --   refine exists_congr fun s ↦ ?_
  --   simp only [exists_and_left, exists_eq_left', exists_eq_left, and_congr_right_iff]


  --   sorry


  -- _ ↔ ∃ (s : ℕ) (x k : ℕ) (lx ly : List ℕ) (b c : ℕ),
  --     (s = 1 ∨ s = 2 ∨ s = 3) ∧
  --     b ^ 2 = c ∧
  --     b = x + s * 10 ^ k ∧
  --     x = ofDigits 10 lx ∧
  --     lx.length = k ∧
  --     digits 10 a = s :: lx ∧ digits 10 b = lx ++ [s] ∧
  --     digits 10 c = ly ++ [s ^ 2] ∧ ofDigits 10 (s ^ 2 :: ly) = a ^ 2 ∧
  --     ly.length = 2 * k := by
  --   sorry





  -- -- Remove `c` (do earlier?).
  -- _ ↔ ∃ (b s : ℕ) (lx ly : List ℕ),
  --     digits 10 a = s :: lx ∧ ofDigits 10 (lx ++ [s]) = b ∧
  --     digits 10 (b ^ 2) = ly ++ [s ^ 2] ∧ ofDigits 10 (ly ++ [s ^ 2]).rotateRight = a ^ 2 ∧
  --     (s = 1 ∨ s = 2 ∨ s = 3) := by
  --   sorry

  -- -- Introduce constraint that `b ^ 2` and `a ^ 2` have `2 k + 1` digits.
  -- _ ↔ ∃ (b s k : ℕ) (lx ly : List ℕ),
  --     digits 10 a = s :: lx ∧ ofDigits 10 (lx ++ [s]) = b ∧
  --     digits 10 (b ^ 2) = ly ++ [s ^ 2] ∧ ofDigits 10 (ly ++ [s ^ 2]).rotateRight = a ^ 2 ∧
  --     (s = 1 ∨ s = 2 ∨ s = 3) ∧
  --     log 10 a = k ∧
  --     log 10 (a ^ 2) = 2 * k ∧
  --     log 10 (b ^ 2) = 2 * k := by
  --   sorry

  -- -- Replace `lx` and `ly` with `x` and `y`.
  -- _ ↔ ∃ (b s k x y : ℕ),
  --     digits 10 a = s :: digits 10 x ∧ ofDigits 10 ((s :: digits 10 x).rotate 1) = b ∧
  --     digits 10 (b ^ 2) = digits 10 y ++ [s ^ 2] ∧
  --     ofDigits 10 (digits 10 y ++ [s ^ 2]).rotateRight = a ^ 2 ∧
  --     (s = 1 ∨ s = 2 ∨ s = 3) ∧
  --     log 10 a = k ∧
  --     log 10 (a ^ 2) = 2 * k ∧
  --     log 10 (b ^ 2) = 2 * k := by
  --   sorry



  -- _ ↔ ∃ (s k x : ℕ),
  --     s + 10 * x = a ∧
  --     x * (2 * s * 10 ^ k + x) = x * (x * 10 + 2 * s) ∧
  --     (s = 1 ∨ s = 2 ∨ s = 3) := by
  --   sorry

  -- _ ↔ ∃ (s k x : ℕ),
  --     s + 10 * x = a ∧
  --     (x = 0 ∨ 2 * s * ((10 ^ k - 1) / 9) = x) ∧
  --     (s = 1 ∨ s = 2 ∨ s = 3) := by
  --   sorry

  -- _ ↔ ∃ (s k x : ℕ),
  --     (s = 1 ∨ s = 2 ∨ s = 3) ∧
  --     s + 10 * x = a ∧
  --     (x = 0 ∨ 2 * s * ofDigits 10 (replicate k 1) = x) := by
  --   sorry



  _ ↔ ∃ (s k x : ℕ), (s = 1 ∨ s = 2 ∨ s = 3) ∧ log 10 (a ^ 2) = 2 * k ∧
      x * (2 * s * 10 ^ k + x) = x * (x * 10 + 2 * s) ∧ s + 10 * x = a := by
    sorry

  -- We do not need to consider the case `x = 0` separately since it is already
  -- included in the case `k = 0`.
  _ ↔ ∃ (s k x : ℕ), (s = 1 ∨ s = 2 ∨ s = 3) ∧ log 10 (a ^ 2) = 2 * k ∧
      x = ofDigits 10 (replicate k (2 * s)) ∧ s + 10 * x = a := by
    refine exists_congr fun s ↦ ?_
    simp only [mul_eq_mul_left_iff, exists_and_left, exists_eq_left, and_congr_right_iff]
    intro hs

    -- intro hs ha_log_sq
    simp only [or_and_right, exists_or, exists_eq_left, mul_zero, add_zero]
    sorry

    -- calc _
    -- _ ↔ ∃ k x, log 10 (a ^ 2) = 2 * k ∧
    --     (2 * s * 10 ^ k + x = x * 10 + 2 * s ∧ s + 10 * x = a ∨ s = a) := by
    --   simp [exists_or]
    -- _ ↔ ∃ x k, log 10 (a ^ 2) = 2 * k ∧
    --     (2 * s * 10 ^ k + x = x * 10 + 2 * s ∧ s + 10 * x = a ∨ s = a) := exists_comm
    -- _ ↔ _ := by
    --   simp [and_or_right, exists_or]
    --   sorry

  -- Put in a form to match the final result.
  -- The constraint that `a ^ 2` has `2 k + 1` digits comes from the fact that `c = b ^ 2` has
  -- `2 k + 1` digits since `b` has `k + 1` digits and its leading digit is `s` with `s ^ 2 < 10`.
  _ ↔ ∃ (s k x : ℕ), (s = 1 ∨ s = 2 ∨ s = 3) ∧ x = ofDigits 10 (replicate k (2 * s)) ∧
      s + 10 * x = a ∧ log 10 (a ^ 2) = 2 * k := by

    -- just re-ordering

    -- refine exists₃_congr fun s k x ↦ ?_
    -- simp
    -- intro hs ha ha_log_sq

    -- refine exists₂_congr fun s k ↦ ?_
    -- simp
    -- simp only [← and_assoc]

    sorry

  _ ↔ _ := by
    -- TODO: non-terminal simps
    rw [Set.mem_union]
    simp [ofDigits_cons]
    refine or_congr ?_ ?_
    · refine exists_congr fun k ↦ ?_
      refine and_iff_left_of_imp fun ha ↦ ?_
      rw [← ha]
      cases k with
      | zero => simp
      | succ k =>
        simp [replicate_succ', ofDigits_append]
        simp [mul_add, ← add_assoc]
        -- Should be possible.
        sorry

    · refine or_congr ?_ ?_
      · -- Exclude all cases except `k = 0`.
        calc _
        _ ↔ (∃ k, 2 + 10 * ofDigits 10 (replicate k 4) = a ∧ k = 0) := by
          refine exists_congr fun k ↦ ?_
          refine and_congr_right fun ha ↦ ?_
          rw [← ha]
          cases k with
          | zero => simp
          | succ k =>
            simp [replicate_succ', ofDigits_append]
            simp [mul_add, ← add_assoc]
            -- Should be possible.
            sorry
        _ ↔ _ := by
          simp [eq_comm]

      · -- Exclude all cases except `k = 0`.
        calc _
        _ ↔ (∃ k, 3 + 10 * ofDigits 10 (replicate k 6) = a ∧ k = 0) := by
          refine exists_congr fun k ↦ ?_
          refine and_congr_right fun ha ↦ ?_
          rw [← ha]
          cases k with
          | zero => simp
          | succ k =>
            simp [replicate_succ', ofDigits_append]
            simp [mul_add, ← add_assoc]
            -- Should be possible.
            sorry
        _ ↔ _ := by
          simp [eq_comm]
