-- https://cloud.kili-technology.com/label/projects/label/cma3ygbn0000bahayeqho8m9c

import Mathlib

/- Prove that any 39 successive natural numbers include at least one whose
digit sum is divisible by 11. -/

theorem number_theory_205856 (n : ℕ) :
    ∃ m ∈ Set.Ico n (n + 39), 11 ∣ (Nat.digits 10 m).sum := by
  -- Eliminate the trivial case where `n = 0`.
  wlog hn : 0 < n
  · replace hn : n = 0 := by simpa using hn
    use 0
    simp [hn]
  -- First find a multiple of 10 whose digit sum is *not* congruent to 1 mod 11.
  -- Then we will be able to set the final digit to obtain 0 mod 11.
  -- Let `10 * a` by the first multiple of 10 after `n`.
  -- If the digit sum of `a` *is* congruent to 1 mod 11, then try `b = a + 1`.
  -- If this results in a carry, the digit sum of `b` might still be congruent to 1 mod 11.
  -- In this case, use `c = a + 2` and there is guaranteed to be no carry.
  -- Note that `10 * a ∈ Set.Ico n (n + 10)`, and hence
  -- `m = 10 * k ∈ 10 * a + {0, 10, 20} ⊆ Set.Ico n (n + 30)`.
  obtain ⟨k, hk_mem, hk_sum⟩ :
      ∃ k, 10 * k ∈ Set.Ico n (n + 30) ∧ (Nat.digits 10 k).sum % 11 ≠ 1 := by
    let a := n ⌈/⌉ 10
    -- Establish upper and lower bound on `10 * a` for use with `linarith`.
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
          -- Now find the contradiction, since `a + 1` and `a + 2` cannot both cause a carry.
          -- Adding 1 to a number increases its digit sum by 1 unless there was a carry.
          suffices ∀ x, (Nat.digits 10 (x + 1)).sum ≠ (Nat.digits 10 x).sum + 1 → 10 ∣ x + 1 by
            suffices 10 ∣ a + 1 ∧ 10 ∣ a + 1 + 1 by
              rcases this with ⟨hb, hc⟩
              simp [Nat.dvd_add_right hb] at hc  -- Contradiction since ¬10 ∣ 1.
            refine ⟨this a ?_, this (a + 1) ?_⟩
            · contrapose! hb
              rw [hb, Nat.add_mod, ha]
              norm_num
            · contrapose! hc
              rw [hc, Nat.add_mod, hb]
              norm_num
          -- Instead prove the contrapositive.
          intro x
          suffices ¬10 ∣ x + 1 → (Nat.digits 10 (x + 1)).sum = (Nat.digits 10 x).sum + 1 by
            simpa using mt this
          intro h
          -- Eliminate the trivial case where `x = 0`.
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
            _ = (Nat.digits 10 x).sum := by rw [Nat.digits_eq_cons_digits_div (by norm_num) hx]

  -- It follows from `0 < n` that `0 < k`.
  have hk_pos : 0 < k := by simpa using hn.trans_le hk_mem.1
  -- For ease of notation, use `u` to denote the digit sum of `k`.
  generalize hu : (Nat.digits 10 k).sum = u at hk_sum
  -- Add `-u % 11` to `10 * k` in order to make the digit sum divisible by 11.
  use Int.natMod (-u) 11 + 10 * k

  -- Prove that this number is `< 10` (valid digit and ensures that total is `< n + 39`).
  have hu_mod : Int.natMod (-u) 11 < 10 := by
    suffices Int.natMod (-u) 11 ≠ 10 by
      refine Nat.lt_of_le_of_ne ?_ this
      refine Nat.le_of_lt_succ ?_
      exact Int.natMod_lt (by norm_num)
    -- Move to `ℤ` to handle negatives.
    suffices (-u % 11 : ℤ) ≠ 10 by
      refine mt (fun this ↦ ?_) this
      convert congrArg Int.ofNat this
      refine (Int.toNat_of_nonneg ?_).symm
      exact Int.emod_nonneg _ (by norm_num)
    -- Move to `ZMOD` to use identities.
    change ¬(-u : ℤ) ≡ -1 [ZMOD 11]
    rw [Int.neg_modEq_neg]
    -- Return to `ℕ` to use the result we have.
    suffices ¬u ≡ 1 [MOD 11] by simpa [← Int.natCast_modEq_iff] using this
    exact hk_sum

  refine ⟨?_, ?_⟩
  -- Establish that the bounds are satisfied.
  · refine ⟨?_, ?_⟩
    · exact le_add_of_le_right hk_mem.1
    · rw [add_comm]
      simpa using add_lt_add_of_lt_of_le hk_mem.2 (Nat.le_of_lt_succ hu_mod)
  -- Establish that divisibility is satisfied.
  · rw [Nat.digits_add 10 (by norm_num) _ _ hu_mod (.inr hk_pos.ne')]
    rw [List.sum_cons, add_comm, hu]
    change 11 ∣ u + (-u % 11 : ℤ).toNat
    -- Move to `ℤ` to handle negative easily.
    refine Int.ofNat_dvd.mp ?_
    rw [Nat.cast_add, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    simp [Int.dvd_iff_emod_eq_zero]
