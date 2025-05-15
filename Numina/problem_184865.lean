-- https://cloud.kili-technology.com/label/projects/label/cma3ygp4o00omahay7ooupdf2

import Mathlib

/- Natural numbers $a < b < c$ are such that $b+a$ is divisible by $b−a$, and $c+b$ is
divisible by $c−b$. The number $a$ is written with 2011 digits, and the number $b−2012$ is
written with 2012 digits. How many digits does the number $c$ have? -/

-- From `b - a ∣ b + a`, we can see that `b - a ∣ (b + a) - (b - a) = 2 * a`.
-- This implies `b ≤ 3 * a`.
lemma le_three_mul_of_sub_dvd_add {a b : ℕ} (ha : a ≠ 0) (hab : a < b)
    (h_dvd : b - a ∣ b + a) : b ≤ 3 * a := by
  replace ha : 0 < a := Nat.pos_of_ne_zero ha
  suffices b - a ≤ 2 * a by
    convert Nat.sub_le_iff_le_add.mp this using 1
    ring
  calc _
  _ ≤ (b + a) - (b - a) := by
    have : b - a ∣ (b + a) - (b - a) := Nat.dvd_sub' h_dvd (Nat.dvd_refl (b - a))
    refine Nat.le_of_dvd ?_ this
    refine Nat.sub_pos_iff_lt.mpr ?_
    refine Nat.lt_add_right a ?_
    exact Nat.sub_lt_self ha hab.le
  _ = _ := by rw [two_mul, Nat.add_sub_sub_cancel hab.le]

theorem number_theory_184865 (a b c : ℕ) (hab : a < b) (hbc : b < c)
    (hab_dvd : b - a ∣ b + a) (hbc_dvd : c - b ∣ c + b)
    (ha_digits : (Nat.digits 10 a).length = 2011)
    (hb_digits : (Nat.digits 10 (b - 2012)).length = 2012) :
    (Nat.digits 10 c).length = 2012 := by
  -- This is the specific case of `k = 2011`, but we can prove more generally for `k ≠ 0`.
  revert ha_digits hb_digits
  suffices ∀ k ≠ 0, (Nat.digits 10 a).length = k → (Nat.digits 10 (b - (k + 1))).length = k + 1 →
      (Nat.digits 10 c).length = k + 1 from this 2011 (by norm_num)
  intro k hk ha_digits hb_digits

  -- We cannot have `a = 0` since `a` has a non-zero number of digits `k`.
  have ha : a ≠ 0 := by
    refine mt (fun ha ↦ ?_) hk
    simpa [ha] using ha_digits.symm
  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
  have hb_pos : 0 < b := ha_pos.trans hab
  have hc_pos : 0 < c := hb_pos.trans hbc

  -- Replace the length of digits with the logarithm.
  rw [Nat.digits_len 10 _ (by norm_num) (Nat.not_eq_zero_of_lt hbc), Nat.add_left_inj]
  rw [Nat.log_eq_iff (.inl hk)]

  refine ⟨?_, ?_⟩
  -- For the lower bound `10 ^ k ≤ c`, use that `b ≤ c` and `b - (k + 1)` has `k + 1` digits.
  · suffices k ≤ Nat.log 10 b from le_trans (Nat.pow_le_of_le_log hb_pos.ne' this) hbc.le
    -- We now need to take consider the digits of `b - (k + 1)`. There is an implicit
    -- assumption that it is positive since it is a natural number with at least one digit.
    have hb' : b - (k + 1) ≠ 0 := fun hb ↦ by simp [hb] at hb_digits
    rw [Nat.digits_len 10 _ (by norm_num) hb', add_left_inj] at hb_digits
    rw [← hb_digits]
    refine Nat.log_monotone ?_
    simp

  -- For the upper bound `c < 10 ^ (k + 1)`, we need to show that `c` is less than `10 * a`.
  · rw [Nat.digits_len 10 _ (by norm_num) ha_pos.ne'] at ha_digits
    calc _
    -- Chain the inequalities `c ≤ 3 * b` and `b ≤ 3 * a`.
    _ ≤ 3 * b := le_three_mul_of_sub_dvd_add hb_pos.ne' hbc hbc_dvd
    _ ≤ 3 * (3 * a) := by
      gcongr
      exact le_three_mul_of_sub_dvd_add ha_pos.ne' hab hab_dvd
    _ = 9 * a := by ring
    _ < 10 * a := by
      gcongr
      norm_num
    -- Use the constraint on the number of digits of `a`.
    _ < 10 * 10 ^ k := by
      suffices a < 10 ^ k by gcongr
      exact Nat.lt_pow_of_log_lt (by norm_num) ha_digits.le
    _ = 10 ^ (k + 1) := by ring
