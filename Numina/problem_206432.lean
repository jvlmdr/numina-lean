-- https://cloud.kili-technology.com/label/projects/label/cmcbovi8d00u1ueaxct6nn82y

import Mathlib

/- Reduce each of the first billion natural numbers (billion $=10^{9}$) to a single digit by
taking its digit sum repeatedly. Do we get more 1s than 2s ? -/

-- For `n ≥ b` the sum of the digits in base `b` is strictly less than `n`.
-- This will be required to prove that the repeated digit sum is well-defined.
lemma sum_digits_lt {b n : ℕ} (hb : 1 < b) (hn : b ≤ n) : (Nat.digits b n).sum < n := by
  induction n using Nat.strongRecOn with
  | ind n IH =>
    have hm_ne : n / b ≠ 0 := by
      rw [Nat.div_ne_zero_iff]
      exact ⟨Nat.not_eq_zero_of_lt hb, hn⟩
    have hm_pos : 0 < n / b := Nat.zero_lt_of_ne_zero hm_ne
    suffices (b.digits (n % b + b * (n / b))).sum < n % b + b * (n / b) by
      simpa [Nat.mod_add_div]

    rw [Nat.digits_add b hb _ _]
    rotate_left
    · exact Nat.mod_lt n (Nat.zero_lt_of_lt hb)
    · exact .inr hm_ne
    rw [List.sum_cons, add_lt_add_iff_left]
    cases lt_or_le (n / b) b with
    | inl hm =>
      calc _
      _ = n / b := by simp [Nat.digits_of_lt _ _ hm_ne hm]
      _ < b * (n / b) := (Nat.lt_mul_iff_one_lt_left hm_pos).mpr hb
    | inr hm =>
      calc _
      _ < n / b := IH (n / b) (Nat.div_lt_self (by linarith) hb) hm
      _ ≤ _ := Nat.le_mul_of_pos_left (n / b) (by linarith)

-- Take the sum of the digits until there is one digit left.
def repeatedDigitSum (b : ℕ) (hb : 1 < b) (n : ℕ) : ℕ :=
  if h : n < b then n else repeatedDigitSum b hb (Nat.digits b n).sum
  termination_by n
  decreasing_by exact sum_digits_lt hb (le_of_not_lt h)

-- Apply `Nat.modEq_digits_sum` to the repeated digit sum.
lemma modEq_repeatedDigitSum (b b' : ℕ) (hb' : 1 < b') (h : b' % b = 1) (n : ℕ) :
    n ≡ repeatedDigitSum b' hb' n [MOD b] := by
  induction n using Nat.strongRecOn with
  | ind n IH =>
    unfold repeatedDigitSum
    cases lt_or_le n b' with
    | inl hn => simpa [hn] using Nat.ModEq.rfl
    | inr hn =>
      refine .trans (Nat.modEq_digits_sum b b' h n) ?_
      simpa [hn.not_lt] using IH _ (sum_digits_lt hb' hn)

-- The result of the repeated digit sum is a single digit.
lemma repeatedDigitSum_lt (b : ℕ) (hb : 1 < b) (n : ℕ) :
    repeatedDigitSum b hb n < b := by
  induction n using Nat.strongRecOn with
  | ind n IH =>
    unfold repeatedDigitSum
    cases lt_or_le n b with
    | inl hn => simp [hn]
    | inr hn => simpa [hn.not_lt] using IH _ (sum_digits_lt hb hn)

theorem number_theory_206432 :
    Nat.count (repeatedDigitSum 10 (Nat.one_lt_succ_succ _) · = 1) (10 ^ 9 + 1) >
    Nat.count (repeatedDigitSum 10 (Nat.one_lt_succ_succ _) · = 2) (10 ^ 9 + 1) := by
  -- Replace `repeatedDigitSum 10 ⋯ n = r` with `n ≡ r [MOD 10]`.
  suffices ∀ (b : ℕ) (hb : 0 < b) (n r : ℕ), r ≠ 0 → r < b →
      (repeatedDigitSum (b + 1) (lt_add_of_pos_left 1 hb) n = r ↔ n ≡ r [MOD b]) by
    simp [this, Nat.count_modEq_card]
  intro b hb n r hr hrb
  have hb' := lt_add_of_pos_left 1 hb
  calc _
  -- We can take `· % b` of both sides without effect.
  -- This is because `x < b + 1` implies `x < b` given that `x % b ≠ 0`.
  _ ↔ repeatedDigitSum (b + 1) hb' n ≡ r [MOD b] := by
    unfold Nat.ModEq
    constructor
    · exact congrArg (· % b)
    · intro h
      rw [Nat.mod_eq_of_lt hrb] at h
      rcases h with rfl
      suffices repeatedDigitSum (b + 1) hb' n < b by simp [Nat.mod_eq_of_lt this]
      suffices repeatedDigitSum (b + 1) hb' n ≠ b from
        Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (repeatedDigitSum_lt (b + 1) hb' n)) this
      contrapose! hr
      simp [hr]
  _ ↔ _ := by
    -- Use the property that the digit sum of `n` using base `b + 1` is congruent to `n` modulo `b`.
    -- First, eliminate the case where `b = 1` (everything is equal modulo 1).
    change 1 ≤ b at hb
    cases eq_or_gt_of_le hb with
    | inl hb => simp [hb, Nat.modEq_one]
    | inr hb =>
      suffices n ≡ repeatedDigitSum (b + 1) hb' n [MOD b] from Eq.congr_left this.symm
      refine modEq_repeatedDigitSum b (b + 1) hb' ?_ n
      simp [Nat.mod_eq_of_lt hb]
