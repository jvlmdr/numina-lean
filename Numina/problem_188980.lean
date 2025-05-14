-- https://cloud.kili-technology.com/label/projects/label/cmaktgyj8006ky1v5yb7qm9pv

import Mathlib

/- Kolya Vasin wrote down an example of multiplication, and then replaced all the digits with
letters: the same digits with the same letters, and different digits with different letters.
The resulting equation is $\overline{a b} \cdot \overline{c d} = \overline{e f f e}$.
Did Kolya make a mistake? -/

theorem number_theory_188980 (a b c d e f : ℕ) (h_nodup : [a, b, c, d, e, f].Nodup) :
    ¬∃ x y z : ℕ, Nat.digits 10 x = [b, a] ∧ Nat.digits 10 y = [d, c] ∧
      Nat.digits 10 z = [e, f, f, e] ∧ x * y = z := by
  simp only [exists_and_left, not_exists, not_and]
  intro x hx y hy z hz
  -- We observe that `effe` is a palindrome with even number of digits, hence divisible by 11.
  -- Therefore, it will suffice to show that neither two-digit number is divisible by 11.
  suffices (¬11 ∣ x ∧ ¬11 ∣ y) ∧ 11 ∣ z by
    rcases this with ⟨⟨hx, hy⟩, hz⟩
    rintro rfl
    exact Nat.Prime.not_dvd_mul (by norm_num) hx hy hz

  refine ⟨?_, ?_⟩
  -- Two-digit numbers are divisible by 11 only if their digits are equal.
  · suffices ∀ {a b x}, Nat.digits 10 x = [b, a] → a ≠ b → ¬11 ∣ x by
      -- Apply this to `ab` and `cd`.
      refine ⟨?_, ?_⟩
      · refine this hx ?_
        suffices [a, b].Nodup by simpa using this
        refine .sublist ?_ h_nodup
        simp
      · refine this hy ?_
        suffices [c, d].Nodup by simpa using this
        refine .sublist ?_ h_nodup
        simp
    intro a b x hx hab
    suffices ¬11 ∣ (b - a : ℤ) by simpa [Nat.eleven_dvd_iff, hx] using this
    -- We cannot have `b - a` divisible by 11 since `a ≠ b` and `|b - a| < 11`.
    -- Prove the contrapositive: if `11 ∣ b - a` then we must have `a = b`.
    refine mt (fun h_dvd ↦ ?_) hab
    suffices (a : ℤ) = (b : ℤ) by simpa using this
    refine Int.eq_of_mod_eq_of_natAbs_sub_lt_natAbs (b := 11) ?_ ?_
    · calc _
      _ = (b : ℤ) % 11 := Int.modEq_iff_dvd.mpr h_dvd
      _ = (b : ℤ) := by
        refine Int.emod_eq_of_lt (Int.ofNat_zero_le b) ?_
        refine Int.lt_toNat.mp ?_
        calc _
        _ < 10 := by
          suffices b ∈ Nat.digits 10 x from Nat.digits_lt_base' this
          simp [hx]
        _ < 11 := Nat.lt_add_one 10
    · suffices (a - b : ℤ).natAbs < 10 from lt_trans this (by norm_num)
      refine Int.natAbs_coe_sub_coe_lt_of_lt ?_ ?_
      · suffices a ∈ Nat.digits 10 x from Nat.digits_lt_base' this
        simp [hx]
      · suffices b ∈ Nat.digits 10 x from Nat.digits_lt_base' this
        simp [hx]

  -- We have a simple proof for the divisibility of `effe` by 11.
  · refine Nat.eleven_dvd_of_palindrome ?_ ?_
    · simp [hz, List.Palindrome.iff_reverse_eq]
    · simp [hz, Nat.even_iff]
