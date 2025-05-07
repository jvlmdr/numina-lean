-- https://cloud.kili-technology.com/label/projects/label/cma3ygbn0000bahayeqho8m9c

import Mathlib

/- Prove that any 39 successive natural numbers include at least one whose
digit sum is divisible by 11. -/

theorem number_theory_205856 (n : ℕ) :
    ∃ m ∈ Set.Ico n (n + 39), 11 ∣ (Nat.digits 10 m).sum := by

  -- Eliminate the trivial case where `n = 0`.
  cases Nat.eq_zero_or_pos n with
  | inl hn =>
    use 0
    simpa using hn
  | inr hn =>
    -- First find a multiple of 10 whose digit sum is not congruent to 1 mod 11.
    -- Let `10 * a` by the first multiple of 10 after `n`.
    -- Consider `10 * a`, `10 * (a + 1)`, `10 * (a + 2)`.
    -- At least one of these must have digit sum not congruent to 1 mod 11.
    -- The number `10 * a` could be anywhere from `n` to `n + 29` inclusive.
    obtain ⟨k, hk_mem, hk_sum⟩ :
        ∃ k, 10 * k ∈ Set.Ico n (n + 30) ∧ (Nat.digits 10 k).sum % 11 ≠ 1 := by
      let a := n ⌈/⌉ 10
      -- Establish upper and lower bound on `10 * a` for `linarith`.
      have ha_ge : n ≤ 10 * a := le_smul_ceilDiv (by norm_num : 0 < 10)
      have ha_le : 10 * a ≤ n + 9 := Nat.mul_div_le (n + 9) 10
      cases eq_or_ne ((Nat.digits 10 a).sum % 11) 1 with
      | inr ha => refine ⟨a, ⟨?_, ?_⟩, ha⟩ <;> linarith
      | inl ha =>
        cases eq_or_ne ((Nat.digits 10 (a + 1)).sum % 11) 1 with
        | inr hb => refine ⟨a + 1, ⟨?_, ?_⟩, hb⟩ <;> linarith
        | inl hb =>
          cases eq_or_ne ((Nat.digits 10 (a + 2)).sum % 11) 1 with
          | inr hc => refine ⟨a + 2, ⟨?_, ?_⟩, hc⟩ <;> linarith
          | inl hc =>
            exfalso
            -- Find contradiction.
            -- If `a % 10 = 9`, then adding 1 to `a` may change multiple digits.
            -- If this occurs, add 1 more.
            -- Adding 1 to a number increases its digit sum by 1 unless there was a carry.
            have (x : ℕ) : ¬10 ∣ x + 1 →
                (Nat.digits 10 (x + 1)).sum = (Nat.digits 10 x).sum + 1 := by
              intro h
              cases eq_or_ne x 0 with
              | inl hx => simp [hx]
              | inr hx =>
                rw [Nat.digits_of_two_le_of_pos (by norm_num) (by simp), List.sum_cons]
                have h_div := Nat.succ_div_of_not_dvd h
                have h_mod : (x + 1) % 10 = x % 10 + 1 := by
                  simp only [Nat.mod_eq_sub, h_div]
                  refine Nat.sub_add_comm ?_
                  exact Nat.mul_div_le x 10
                rw [h_div, h_mod, ← add_rotate]
                congr
                calc (Nat.digits 10 (x / 10)).sum + x % 10
                _ = (x % 10 :: Nat.digits 10 (x / 10)).sum := by simp [add_comm]
                _ = (Nat.digits 10 x).sum := by
                  congr
                  exact (Nat.digits_eq_cons_digits_div (by norm_num) hx).symm

            have (x : ℕ) : (Nat.digits 10 (x + 1)).sum ≠ (Nat.digits 10 x).sum + 1 →
                10 ∣ x + 1 := by
              simpa using fun h ↦ mt (this x) h

            have hb' : (Nat.digits 10 (a + 1)).sum ≠ (Nat.digits 10 a).sum + 1 := by
              contrapose! hb
              rw [hb, Nat.add_mod, ha]
              norm_num
            have hc' : (Nat.digits 10 (a + 2)).sum ≠ (Nat.digits 10 (a + 1)).sum + 1 := by
              contrapose! hc
              rw [hc, Nat.add_mod, hb]
              norm_num

            have hb' := this a hb'
            have hc' := this (a + 1) hc'
            simp [Nat.dvd_add_right hb'] at hc'  -- Contradiction since ¬10 ∣ 1.

    have hk_pos : 0 < k := by simpa using hn.trans_le hk_mem.1

    generalize hc : (Nat.digits 10 k).sum = c at hk_sum

    -- Set the final digit to obtain a number whose digit sum is congruent to 0 mod 11.
    use Int.natMod (-c) 11 + 10 * k

    have hc_mod : Int.natMod (-c) 11 < 10 := by
      have h_lt : Int.natMod (-c) 11 < 11 := Int.natMod_lt (by norm_num)
      suffices Int.natMod (-c) 11 ≠ 10 from Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h_lt) this
      suffices (-c % 11 : ℤ) ≠ 10 by
        refine mt (fun this ↦ ?_) this
        convert congrArg Int.ofNat this
        refine (Int.toNat_of_nonneg ?_).symm
        exact Int.emod_nonneg _ (by norm_num)
      -- TODO: switch to `Int.modEq`?
      suffices (c % 11 : ℤ) ≠ 1 by
        have h := Int.neg_modEq_neg (n := 11) (a := c) (b := 1)
        simp [Int.ModEq] at h  -- TODO
        simpa [h] using this
      have h := Int.natCast_modEq_iff (a := c) (b := 1) (n := 11)
      simp [Int.ModEq, Nat.ModEq] at h  -- TODO
      simpa [h] using hk_sum

    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact le_add_of_le_right hk_mem.1
      · rw [add_comm]  -- TODO: move add_comm?
        simpa using add_lt_add_of_lt_of_le hk_mem.2 (Nat.le_of_lt_succ hc_mod)
    · rw [Nat.digits_add 10 (by norm_num) _ _ hc_mod (.inr hk_pos.ne')]
      rw [List.sum_cons, add_comm, hc]  -- TODO: move add_comm?
      change 11 ∣ c + (-c % 11 : ℤ).toNat
      refine Int.ofNat_dvd.mp ?_
      rw [Nat.cast_add, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
      simp [Int.dvd_iff_emod_eq_zero]
