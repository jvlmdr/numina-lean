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
  ofDigits 10 <| rotateRight <| digits 10 <| (· ^ 2) <| ofDigits 10 <| rotateLeft <| digits 10 a

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
lemma mem_Ico_of_digits_eq_append {b : ℕ} (hb : 1 < b) (n x : ℕ) (l : List ℕ)
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

lemma last_digit' (b : ℕ) (hb : 1 < b) (n x y : ℕ)
    (hx : ∃ l, digits b n = l ++ [x]) (hy : ∃ l, digits b (n ^ 2) = l ++ [y]) :
    y ∈ Finset.Ico (x ^ 2) ((x + 1) ^ 2) ∪ Finset.Ico (x ^ 2 / b) ((x + 1) ^ 2 ⌈/⌉ b) := by
  simp only [Finset.mem_union, Finset.mem_Ico]
  rcases hx with ⟨lx, hx⟩
  rcases hy with ⟨ly, hy⟩
  have hn_zero : n ≠ 0 := by
    suffices digits b n ≠ [] from digits_ne_nil_iff_ne_zero.mp this
    simp [hx]

  have hx_mem := mem_Ico_of_digits_eq_append hb n x lx hx
  have hy_mem := mem_Ico_of_digits_eq_append hb (n ^ 2) y ly hy

  refine Or.imp (fun h_sq ↦ ?_) (fun h_sq ↦ ?_) (length_digits_sq hb hn_zero)
  · have hk : ly.length = 2 * lx.length := by
      -- TODO: clean up
      have hx := congrArg length hx
      rw [digits_len b n hb hn_zero] at hx
      have hy := congrArg length hy
      rw [digits_len b _ hb (by simpa using hn_zero)] at hy
      rw [h_sq] at hy
      simp at hx hy
      rw [← hy, ← hx]

    rw [hk] at hy_mem

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

  · have hk : ly.length = 2 * lx.length + 1 := by
      -- TODO: clean up AND avoid duplication
      have hx := congrArg length hx
      rw [digits_len b n hb hn_zero] at hx
      have hy := congrArg length hy
      rw [digits_len b _ hb (by simpa using hn_zero)] at hy
      rw [h_sq] at hy
      simp at hx hy
      rw [← hy, ← hx]

    rw [hk] at hy_mem

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

lemma last_digit (b : ℕ) (hb : 1 < b) (n x y : ℕ)
    (hx : ∃ l, digits b n = l ++ [x]) (hy : ∃ l, digits b (n ^ 2) = l ++ [y]) :
    y ∈ Finset.Ico (1 ⊔ x ^ 2) (b ⊓ (x + 1) ^ 2) ∪
      Finset.Ico (1 ⊔ x ^ 2 / b) (b ⊓ (x + 1) ^ 2 ⌈/⌉ b) := by
  rcases hx with ⟨lx, hx⟩
  rcases hy with ⟨ly, hy⟩
  have hn_zero : n ≠ 0 := by
    suffices digits b n ≠ [] from digits_ne_nil_iff_ne_zero.mp this
    simp [hx]

  suffices y ∈ Finset.Ico 1 b ∩
      (Finset.Ico (x ^ 2) ((x + 1) ^ 2) ∪ Finset.Ico (x ^ 2 / b) ((x + 1) ^ 2 ⌈/⌉ b)) by
    convert this using 1
    simp [Finset.inter_union_distrib_left, Finset.Ico_inter_Ico]

  rw [Finset.mem_inter]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_Ico]
    refine ⟨?_, ?_⟩
    · suffices y ≠ 0 from one_le_iff_ne_zero.mpr this
      convert getLast_digit_ne_zero b (m := n ^ 2) (by simpa using hn_zero)
      simp [hy]
    · suffices y ∈ digits b (n ^ 2) from digits_lt_base hb this
      simp [hy]
  · exact last_digit' b hb n x y ⟨lx, hx⟩ ⟨ly, hy⟩

def f : ℕ → ℕ → Finset ℕ :=
  fun b x ↦
    Finset.Ico (1 ⊔ x ^ 2) (b ⊓ (x + 1) ^ 2) ∪
      Finset.Ico (1 ⊔ x ^ 2 / b) (b ⊓ (x + 1) ^ 2 ⌈/⌉ b)

#eval f 10 1
#eval f 10 2
#eval f 10 3
#eval f 10 4
#eval f 10 5
#eval f 10 6
#eval f 10 7
#eval f 10 8
#eval f 10 9

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

theorem number_theory_25148 {a : ℕ} (ha : 0 < a) :
    d a = a ^ 2 ↔ a ∈ Set.range (fun n ↦ ofDigits 10 ([1] ++ List.replicate n 2)) ∪ {2, 3} := by
  unfold d
  simp only

  sorry
