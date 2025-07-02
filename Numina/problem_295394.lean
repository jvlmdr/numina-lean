-- https://cloud.kili-technology.com/label/projects/label/cmcbouv7300moueaxaag69l3n

import Mathlib

/- Find all positive integers $N$, such that it equals the sum of the digits of $N^{3}$. -/

-- TODO: used?
lemma clog_le_log_add_one (b n : ℕ) : b.clog n ≤ b.log n + 1 := by
  rw [← Int.ofNat_le]
  simpa [Real.ceil_logb_natCast, Real.floor_logb_natCast] using
    Int.ceil_le_floor_add_one (Real.logb b n)

lemma log_pow_add_one_le_mul_log_add_one (b n k : ℕ) (hb : 1 < b) (hk : k ≠ 0) :
    Nat.log b (n ^ k) + 1 ≤ k * (Nat.log b n + 1) := by
  -- We don't need to assume `n ≠ 0` as the equation holds.
  -- It does not hold for `k = 0`.
  cases n.eq_zero_or_pos with
  | inl hn => simp [hn, Nat.pos_iff_ne_zero, Nat.one_le_iff_ne_zero, hk]
  | inr hn =>
    sorry

-- lemma log_pow_lt_mul_log_add_one (b n k : ℕ) (hb : 1 < b) (hk : k ≠ 0) :
--     Nat.log b (n ^ k) < k * (Nat.log b n + 1) :=
--   log_pow_add_one_le_mul_log_add_one b n k hb hk

theorem number_theory_295394 (n : ℕ) :
    n ≠ 0 ∧ n = (Nat.digits 10 (n^3)).sum ↔
    n = 1 ∨ n = 8 ∨ n = 17 ∨ n = 18 ∨ n = 26 ∨ n = 27 := by
  -- First confirm that each solution is valid.
  constructor
  swap
  · revert n
    simp

  intro ⟨hn, hn_eq⟩

  -- let k := Nat.log 10 n + 1
  generalize hk : Nat.log 10 n + 1 = k
  have hn_len : (Nat.digits 10 n).length = k := by
    simpa [hk] using Nat.digits_len 10 n (by norm_num) hn

  -- have hn3_len := Nat.digits_len 10 (n ^ 3) (by norm_num) (by simpa using hn)
  have hn3_len : (Nat.digits 10 (n ^ 3)).length ≤ 3 * k := by
    rw [← hn_len]
    rw [Nat.digits_len 10 n (by norm_num) (by simpa)]
    rw [Nat.digits_len 10 (n ^ 3) (by norm_num) (by simpa)]
    exact log_pow_add_one_le_mul_log_add_one 10 n 3 (by norm_num) three_ne_zero

  have hn3_sum : (Nat.digits 10 (n ^ 3)).sum ≤ 27 * k := by
    calc _
    _ ≤ (Nat.digits 10 (n ^ 3)).length * 9 := by
      refine List.sum_le_card_nsmul _ _ fun x hx ↦ ?_
      exact Nat.le_of_lt_succ (Nat.digits_lt_base' hx)
    _ ≤ 3 * k * 9 := Nat.mul_le_mul_right 9 hn3_len
    _ = _ := by ring

  cases lt_or_le k 3 with
  | inr hk =>
    exfalso
    suffices 27 * k < n from hn3_sum.not_lt (hn_eq ▸ this)
    calc
    _ < 10 * 9 * (k - 2) := by
      rw [mul_tsub]
      refine lt_tsub_of_add_lt_left ?_
      linarith
    _ < 10 * 10 ^ (k - 2) := by
      simp only [mul_assoc]
      gcongr
      -- Put in the form to match `one_add_mul_sub_le_pow`.
      rw [mul_comm 9, ← Nat.one_add_le_iff]
      rw [← Int.ofNat_le]
      simpa using one_add_mul_sub_le_pow (a := (10 : ℤ)) (by simp) (k - 2)
    _ = 10 ^ (k - 2 + 1) := by rw [Nat.pow_succ']
    _ = 10 ^ (k - 1) := by
      congr
      rw [← Nat.sub_add_comm (by linarith)]
      simp
    _ ≤ _ := by
      suffices 10 * 10 ^ (k - 1) ≤ 10 * n from le_of_mul_le_mul_left this (by norm_num)
      calc _
      _ = 10 ^ (k - 1 + 1) := by ring
      _ = 10 ^ k := by rw [Nat.sub_add_cancel (by linarith)]
      _ = 10 ^ (Nat.digits 10 n).length := by rw [hn_len]
      _ ≤ _ := Nat.base_pow_length_digits_le' _ n hn

  | inl hk =>

    sorry
