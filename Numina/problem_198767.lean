-- https://cloud.kili-technology.com/label/projects/label/cma1au8wi00nvthv57dp8nyq5

import Mathlib

/- Determine all pairs $(a, b)$ of prime numbers for which the following holds:
$$
3 a^{2} + a = b^{2} + b
$$
-/

theorem number_theory_198767 (a b : ℕ) (ha : a.Prime) (hb : b.Prime) (h : 3 * a^2 + a = b^2 + b) :
    a = 3 ∧ b = 5 := by

  -- Re-arrange to `2 a^2 = b^2 + b - (a^2 + a) = (b - a) (b + a + 1)`.
  have h : a ^ 2 + a + 2 * a ^ 2 = b ^ 2 + b := .trans (by ring) h
  have h : 2 * a ^ 2 = b ^ 2 + b - (a ^ 2 + a) := Nat.eq_sub_of_add_eq' h
  -- First prove `a < b` for subtraction to be valid.
  -- TODO: Prove `a ≤ b` then `a < b`?
  have hab : a < b := by
    suffices a ^ 2 + a < b ^ 2 + b by
      refine (StrictMono.lt_iff_lt ?_ (f := fun x ↦ x ^ 2 + x)).mp this
      exact .add (strictMono_id.nat_pow two_ne_zero) strictMono_id
    suffices 0 < 2 * a ^ 2 from Nat.lt_of_sub_pos (h ▸ this)
    refine Nat.pos_of_ne_zero ?_
    simpa using ha.ne_zero

  have h : 2 * a ^ 2 = (b - a) * (b + a + 1) := by
    symm
    calc _
    _ = (b + a) * (b - a) + (b - a) := by ring
    _ = b ^ 2 - a ^ 2 + (b - a) := by rw [Nat.sq_sub_sq]
    _ = b ^ 2 + b - (a ^ 2 + a) := tsub_add_tsub_comm (Nat.pow_le_pow_left hab.le _) hab.le
    _ = _ := h.symm

  -- Now show that `a` cannot divide `b - a` since that would imply `b = k a`.
  -- This is only prime if `a = b`.
  have h_not_dvd : ¬a ∣ b - a := by
    rintro ⟨m, hm⟩
    have hb' : b = a * m + a := Nat.eq_add_of_sub_eq hab.le hm
    replace hb' : b = a * (m + 1) := .trans hb' (by ring)
    suffices m ≠ 0 by
      rcases hb' with rfl
      revert hb
      simpa [Nat.prime_mul_iff, ha, ha.ne_one]
    rintro rfl
    revert hab
    simpa using hb'.le

  have hab_two : b - a ≤ 2 := by
    have := Prime.pow_dvd_of_dvd_mul_left (Nat.prime_iff.mp ha) 2 h_not_dvd (Dvd.intro_left 2 h)
    rcases this with ⟨k, hk⟩
    rw [hk] at h
    have h : 2 * a ^ 2 = (b - a) * k * a ^ 2 := by
      convert h using 1
      ring
    have h : 2 = (b - a) * k := by
      refine (Nat.mul_left_inj ?_).mp h
      simpa using ha.ne_zero
    calc _
    _ ≤ (b - a) * k := by
      refine Nat.le_mul_of_pos_right (b - a) ?_
      suffices k ≠ 0 from Nat.zero_lt_of_ne_zero this
      rintro rfl
      simp at hk  -- Contradiction in `b + a + 1 = 0`.
    _ = 2 := h.symm

  have hb' : b - a = 1 ∨ b - a = 2 := by
    suffices b - a ∈ ({1, 2} : Finset ℕ) by simpa using this
    change b - a ∈ Finset.Icc 1 2
    rw [Finset.mem_Icc]
    exact ⟨Nat.le_sub_of_add_le' hab, hab_two⟩

  simp only [Nat.sub_eq_iff_eq_add' hab.le] at hb'

  cases hb' with
  | inl hb' =>
    -- If we have two primes with `b - a = 1`, then `a = 2` and `b = 3`.
    -- This does not satisfy the original equation; eliminate this case.
    exfalso
    suffices a = 2 ∧ b = 3 by
      rcases this with ⟨rfl, rfl⟩
      simp at h

    -- have hb' : b = a + 1 := (Nat.sub_eq_iff_eq_add' hab.le).mp hab'  -- TODO?
    cases a.even_or_odd with
    | inl ha_even =>
      -- If `a` is even, then `a = 2` and hence `b = a + 1 = 3`.
      rcases (Nat.Prime.even_iff ha).mp ha_even with rfl
      exact ⟨rfl, hb'⟩
    | inr ha_odd =>
      exfalso
      -- Cannot have `a < b` prime with `Odd a` and `Even b`.
      have hb_even : Even b := hb' ▸ ha_odd.add_one
      -- Substitute `b = 2`, hence `a = 1`, which is not prime.
      rcases (Nat.Prime.even_iff hb).mp hb_even with rfl
      refine ha.ne_one ?_
      linarith

  | inr hb' =>
    rcases hb' with rfl
    suffices a = 3 by simpa using this
    have h : a ^ 2 = a + 2 + a + 1 := by simpa using h
    suffices (a : ℤ) = 3 from Int.ofNat_inj.mp this
    suffices (a - 1 : ℤ) = 2 from sub_eq_iff_eq_add.mp this
    suffices |(a - 1 : ℤ)| = 2 by
      rw [abs_eq two_pos.le] at this
      cases this with
      | inl h => exact h
      | inr h => simpa using sub_eq_iff_eq_add.mp h
    suffices (a - 1 : ℤ) ^ 2 = 2 ^ 2 by simpa using (sq_eq_sq_iff_abs_eq_abs _ _).mp this
    rw [sub_sq, ← Nat.cast_pow, h]
    simp only [Nat.cast_add]
    ring
