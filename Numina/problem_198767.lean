-- https://cloud.kili-technology.com/label/projects/label/cmac65080000194ayn9mp2jp2

import Mathlib

/- Determine all pairs $(a, b)$ of prime numbers for which the following holds:
$$
3 a^{2} + a = b^{2} + b
$$
-/

theorem number_theory_198767 (a b : ℕ) (ha : a.Prime) (hb : b.Prime) (h : 3 * a^2 + a = b^2 + b) :
    a = 3 ∧ b = 5 := by
  -- Re-arrange the equation to obtain `2 a^2 = b^2 + b - (a^2 + a) = (b - a) (b + a + 1)`.
  replace h : a ^ 2 + a + 2 * a ^ 2 = b ^ 2 + b := .trans (by ring) h
  replace h : 2 * a ^ 2 = b ^ 2 + b - (a ^ 2 + a) := Nat.eq_sub_of_add_eq' h
  -- Pause to prove `a < b` for subtraction to be valid.
  -- Use strict monotonicity of `fun x ↦ x ^ 2 + x`.
  have hab : a < b := by
    suffices a ^ 2 + a < b ^ 2 + b by
      refine (StrictMono.lt_iff_lt ?_ (f := fun x ↦ x ^ 2 + x)).mp this
      exact .add (strictMono_id.nat_pow two_ne_zero) strictMono_id
    suffices 0 < 2 * a ^ 2 from Nat.lt_of_sub_pos (h ▸ this)
    refine Nat.pos_of_ne_zero ?_
    simpa using ha.ne_zero
  -- Obtain the factorization.
  replace h : 2 * a ^ 2 = (b - a) * (b + a + 1) := by
    calc _
    _ = b ^ 2 + b - (a ^ 2 + a) := h
    _ = b ^ 2 - a ^ 2 + (b - a) := (tsub_add_tsub_comm (Nat.pow_le_pow_left hab.le _) hab.le).symm
    _ = (b + a) * (b - a) + (b - a) := by rw [Nat.sq_sub_sq]
    _ = _ := by ring

  -- Now show that `a` cannot divide `b - a`. This would imply `b - a = m a` and hence
  -- `b = (m + 1) a`, which can only be prime if `a = b`, contradicting `a < b`.
  have h_not_dvd : ¬a ∣ b - a := by
    refine mt (fun ⟨m, hm⟩ ↦ ?_) hab.not_le
    have hb' : b = a * (m + 1) :=
      calc _
      _ = a * m + a := Nat.eq_add_of_sub_eq hab.le hm
      _ = a * (m + 1) := by ring
    have hm : m = 0 := by simpa [hb', Nat.prime_mul_iff, ha, ha.ne_one] using hb
    simp [hb', hm]

  -- Since `a` (prime) does not divide `b - a` and `2 a^2 = (b - a) (b + a + 1)`,
  -- `b - a` must be either 1 or 2.
  have hab' : b - a ≤ 2 := by
    -- First show that `(b - a) * k = 2` for `k` such that `b + a + 1 = k (a ^ 2)`.
    obtain ⟨k, hk⟩ : a ^ 2 ∣ b + a + 1 :=
      (Nat.prime_iff.mp ha).pow_dvd_of_dvd_mul_left 2 h_not_dvd (Dvd.intro_left 2 h)
    suffices (b - a) * k = 2 by
      refine le_of_le_of_eq ?_ this
      refine Nat.le_mul_of_pos_right (b - a) ?_
      suffices k ≠ 0 from Nat.zero_lt_of_ne_zero this
      rintro rfl
      simp at hk  -- Contradiction in `b + a + 1 = 0`.
    symm
    -- Multiply by `a ^ 2` on both sides.
    suffices 2 * a ^ 2 = (b - a) * k * a ^ 2 by
      refine (Nat.mul_left_inj ?_).mp this
      simpa using ha.ne_zero
    convert h using 1
    rw [hk]
    ring
  have hab' : b - a = 1 ∨ b - a = 2 := by
    suffices b - a ∈ ({1, 2} : Finset ℕ) by simpa using this
    change b - a ∈ Finset.Icc 1 2
    rw [Finset.mem_Icc]
    exact ⟨Nat.le_sub_of_add_le' hab, hab'⟩

  -- Re-arrange as either `b = a + 1` or `b = a + 2`.
  simp only [Nat.sub_eq_iff_eq_add' hab.le] at hab'
  cases hab' with
  | inl hb' =>
    -- If we have two primes `a, b` with `b = a + 1`, then the primes are `2, 3`.
    -- This does not satisfy the original equation; eliminate this case.
    suffices a = 2 ∧ b = 3 by
      rcases this with ⟨rfl, rfl⟩
      simp at h  -- Contradiction in original equation.
    cases a.even_or_odd with
    | inl ha_even =>
      -- If `a` is even, then `a = 2` and hence `b = a + 1 = 3`.
      rcases (Nat.Prime.even_iff ha).mp ha_even with rfl
      exact ⟨rfl, hb'⟩
    | inr ha_odd =>
      -- Cannot have `a < b` prime with `Odd a` and `Even b`.
      exfalso
      have hb_even : Even b := hb' ▸ ha_odd.add_one
      -- Substitute `b = 2`, hence `a = 1`, which is not prime.
      rcases (Nat.Prime.even_iff hb).mp hb_even with rfl
      refine ha.ne_one ?_
      linarith

  | inr hb' =>
    -- Substitute `b = a + 2`. This gives a quadratic equation with at most 2 solutions.
    rcases hb' with rfl
    -- The quadratic equation is `a^2 - 2 a - 3 = 0 ↔ (a - 1)^2 = 4 ↔ a = 1 ± 2`.
    -- Show that only one solution is valid.
    suffices a = 3 by simpa using this
    -- Switch to `ℤ` to consider both solutions.
    suffices (a : ℤ) = 3 from Int.ofNat_inj.mp this
    suffices (a - 1 : ℤ) = 2 from sub_eq_iff_eq_add.mp this
    suffices |(a - 1 : ℤ)| = 2 by
      rw [abs_eq two_pos.le] at this
      cases this with
      | inl h => exact h
      | inr h => simpa using sub_eq_iff_eq_add.mp h
    suffices (a - 1 : ℤ) ^ 2 = 2 ^ 2 by simpa using (sq_eq_sq_iff_abs_eq_abs _ _).mp this
    -- Substitute in the equation for `a ^ 2` and use casts and `ring` to resolve.
    have h : a ^ 2 = a + 2 + a + 1 := by simpa using h
    rw [sub_sq, ← Nat.cast_pow, h]
    simp only [Nat.cast_add]
    ring
