-- https://cloud.kili-technology.com/label/projects/label/cmac65080000294ay2bab2ir3

import Mathlib

/- Solve the Diophantine equation $6(x^{2} + y^{2}) = z^{2} + t^{2}$. -/

theorem number_theory_107999 (x y z t : ℕ) (h : 6 * (x ^ 2 + y ^ 2) = z ^ 2 + t ^ 2) :
    (x, y, z, t) = 0 := by
  -- Rewrite as a proposition about `ℕ × ℕ × ℕ × ℕ` to use `WellFounded.fix`.
  revert x y z t
  suffices ∀ (m : ℕ × ℕ × ℕ × ℕ), match m with
      | (x, y, z, t) => 6 * (x ^ 2 + y ^ 2) = z ^ 2 + t ^ 2 → (x, y, z, t) = 0 by simpa

  refine WellFounded.fix wellFounded_lt ?_
  intro (x, y, z, t) IH h

  -- TODO: Can this be done later?
  cases eq_or_ne (x, y, z, t) (0, 0, 0, 0) with
  | inl h_zero => exact h_zero
  | inr h_zero =>

    -- Since squares are either 0 or 1 mod 3, both must be 0 for their sum to be 0.
    have h_three_dvd_sq (a b : ℕ) (h : 3 ∣ a ^ 2 + b ^ 2) : 3 ∣ a ∧ 3 ∣ b := by
      suffices 3 ∣ a ^ 2 ∧ 3 ∣ b ^ 2 from
        this.imp Nat.prime_three.dvd_of_dvd_pow Nat.prime_three.dvd_of_dvd_pow
      suffices a ^ 2 ≡ 0 [MOD 3] ∧ b ^ 2 ≡ 0 [MOD 3] from
        this.imp Nat.dvd_of_mod_eq_zero Nat.dvd_of_mod_eq_zero
      suffices ∀ n, n ^ 2 ≡ 0 [MOD 3] ∨ n ^ 2 ≡ 1 [MOD 3] by
        cases this a with
        | inl ha =>
          cases this b with
          | inl hb => exact ⟨ha, hb⟩
          | inr hb =>
            exfalso
            suffices (a ^ 2 + b ^ 2) % 3 ≠ 0 from this (Nat.dvd_iff_mod_eq_zero.mp h)
            have : (a ^ 2 + b ^ 2) % 3 = 1 := ha.add hb
            simp [this]
        | inr ha =>
          exfalso
          suffices (a ^ 2 + b ^ 2) % 3 ≠ 0 from this (Nat.dvd_iff_mod_eq_zero.mp h)
          cases this b with
          | inl hb =>
            have : (a ^ 2 + b ^ 2) % 3 = 1 := ha.add hb
            simp [this]
          | inr hb =>
            have : (a ^ 2 + b ^ 2) % 3 = 2 := ha.add hb
            simp [this]

      intro n
      suffices (n ^ 2) % 3 ∈ ({0, 1} : Finset ℕ) by simpa using this
      rw [Nat.pow_mod]
      have : Finset.image (fun x ↦ x ^ 2 % 3) (Finset.range 3) = {0, 1} := rfl
      rw [← this]
      refine Finset.mem_image_of_mem _ ?_
      rw [Finset.mem_range]
      exact Nat.mod_lt n (by norm_num)

    have h_three_zt : 3 ∣ z ∧ 3 ∣ t := by
      refine h_three_dvd_sq z t ?_
      refine Dvd.intro (2 * (x ^ 2 + y ^ 2)) ?_
      convert h using 1
      ring
    rcases h_three_zt with ⟨⟨z', rfl⟩, ⟨t', rfl⟩⟩

    replace h : 2 * (x ^ 2 + y ^ 2) = 3 * (z' ^ 2 + t' ^ 2) := by
      refine (Nat.mul_left_inj (by norm_num : 3 ≠ 0)).mp ?_
      convert h using 1 <;> ring

    have h_three_xy : 3 ∣ x ∧ 3 ∣ y := by
      refine h_three_dvd_sq x y ?_
      suffices 3 ∣ 2 * (x ^ 2 + y ^ 2) from Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this
      exact Dvd.intro _ h.symm

    rcases h_three_xy with ⟨⟨x', rfl⟩, ⟨y', rfl⟩⟩
    replace h : 6 * (x' ^ 2 + y' ^ 2) = z' ^ 2 + t' ^ 2 := by
      refine (Nat.mul_left_inj (by norm_num : 3 ≠ 0)).mp ?_
      convert h using 1 <;> ring

    suffices (x', y', z', t') = 0 by simpa using this
    simp only [Prod.mk.eta] at IH
    refine IH _ ?_ h
    replace h_zero : (x', y', z', t') ≠ 0 := by simpa using h_zero

    -- Now we need to deal with the four possible cases `x' ≠ 0`, `y' ≠ 0`, `z' ≠ 0`, `t' ≠ 0`.
    have h3 (w : ℕ) : w ≤ 3 * w := Nat.le_mul_of_pos_left w (by norm_num)
    cases Nat.eq_zero_or_pos x' with
    | inr hx' =>
      refine Prod.mk_lt_mk_of_lt_of_le ?_ ?_
      · exact lt_mul_of_one_lt_left hx' (by norm_num)
      · simp [h3]
    | inl hx' =>
      refine Prod.mk_lt_mk_of_le_of_lt (Nat.le_mul_of_pos_left x' (by norm_num)) ?_
      -- If `x' = 0`, then one of `y', z', t'` must be non-zero.
      cases Nat.eq_zero_or_pos y' with
      | inr hy' =>
        refine Prod.mk_lt_mk_of_lt_of_le ?_ ?_
        · exact lt_mul_of_one_lt_left hy' (by norm_num)
        · simp [h3]
      | inl hy' =>
        refine Prod.mk_lt_mk_of_le_of_lt (Nat.le_mul_of_pos_left y' (by norm_num)) ?_
        -- If `x' = y' = 0`, then one of `z', t'` must be non-zero.
        cases Nat.eq_zero_or_pos z' with
        | inr hz' =>
          refine Prod.mk_lt_mk_of_lt_of_le ?_ ?_
          · exact lt_mul_of_one_lt_left hz' (by norm_num)
          · simp [h3]
        | inl hz' =>
          refine Prod.mk_lt_mk_of_le_of_lt (Nat.le_mul_of_pos_left z' (by norm_num)) ?_
          -- If `x' = y' = z' = 0`, `t'` must be non-zero.
          refine lt_mul_of_one_lt_left ?_ (by norm_num)
          refine Nat.zero_lt_of_ne_zero ?_
          refine mt (fun ht' ↦ ?_) h_zero
          simpa using ⟨hx', hy', hz', ht'⟩
