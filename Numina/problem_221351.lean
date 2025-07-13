-- https://cloud.kili-technology.com/label/projects/label/cmcboth12006bueaxcg0nw74p

import Mathlib

/- Given a natural number $x = 9^{n} - 1$, where $n$ is a natural number. It is known that
$x$ has exactly three distinct prime divisors, one of which is 13. Find $x$. -/

-- The remainders of the powers of 9 when divided by 13 are 9, 3, 1 repeating cyclically.
lemma periodic_nine_pow_mod_thirteen : Function.Periodic (fun n ↦ 9 ^ n % 13) 3 := by
  simp [pow_add, Nat.mul_mod]

lemma nine_pow_mod_thirteen_eq_one_iff (n : ℕ) :
    9 ^ n % 13 = 1 ↔ n % 3 = 0 := by
  rw [← periodic_nine_pow_mod_thirteen.map_mod_nat]
  -- Test the three possible values of `n % 3`.
  suffices ∀ k < 3, 9 ^ k % 13 = 1 ↔ k = 0 from this (n % 3) (Nat.mod_lt n three_pos)
  intro k hk
  interval_cases k <;> simp

lemma minFac_mem_primeFactors {n : ℕ} (hn : 1 < n) : n.minFac ∈ n.primeFactors := by
  rw [Nat.mem_primeFactors]
  split_ands
  · exact Nat.minFac_prime hn.ne'
  · exact Nat.minFac_dvd n
  · linarith

theorem number_theory_221351 (n : ℕ) (x : ℕ) (hx : x = 9 ^ n - 1)
    (h_card : x.primeFactors.card = 3) (h13 : 13 ∣ x) :
    x = 728 := by
  -- Replace `x` with `9 ^ n - 1` everywhere.
  rcases hx with rfl

  have hx_zero : 9 ^ n - 1 ≠ 0 := by
    contrapose! h_card with hx
    simp [hx]

  -- Clearly `x` is even, hence one of the other prime factors is 2.
  have hx2 : 2 ∣ 9 ^ n - 1 := by
    rw [← even_iff_two_dvd]
    refine Odd.tsub_odd (.pow ?_) odd_one
    simp [Nat.odd_iff]

  -- Since `13 ∣ 9 ^ n - 1`, we must have `n % 3 = 0` by the periodicity of `9 ^ n % 13`.
  have hn3 : 3 ∣ n := by
    rw [Nat.dvd_iff_mod_eq_zero]
    rw [← nine_pow_mod_thirteen_eq_one_iff]
    -- TODO
    suffices 9 ^ n % 13 = 1 % 13 by simpa
    change 9 ^ n ≡ 1 [MOD 13]
    -- TODO
    rw [← Int.ofNat_dvd, Nat.cast_sub (by simp [Nat.one_le_pow]), ← Nat.modEq_iff_dvd] at h13
    exact h13.symm
  -- Obtain `n = 3 * m`.
  rcases hn3 with ⟨m, hmn⟩

  -- Use the cyclotomic polynomial to factor `(9 ^ m) ^ 3 - 1`.
  let a : ℕ := 9 ^ m - 1
  let b : ℕ := 9 ^ (2 * m) + 9 ^ m + 1
  have hab : 9 ^ n - 1 = a * b := by
    -- Prove using `ring` in `ℤ`.
    suffices (9 ^ n - 1 : ℤ) = (9 ^ m - 1) * (9 ^ (2 * m) + 9 ^ m + 1) by
      simpa [a, b, ← @Nat.cast_inj ℤ]
    rw [hmn]
    ring

  cases le_or_lt m 1 with
  | inl hm =>
    -- Replace `n` with `3 * m` everywhere.
    rcases hmn with rfl
    interval_cases m
    · -- Contradiction: Cannot have `n = 0`.
      simp at h_card
    · -- This is the solution: `9 ^ 3 - 1 = 728 = 2^3 * 7 * 13`.
      norm_num

  | inr hm =>
    -- It remains to show that `1 < m` leads to a contradiction.

    have h_coprime : a.Coprime b := by
      sorry

    -- It suffices to show that `x` has four distinct prime factors.
    exfalso
    suffices ∃ s : Finset ℕ, s.card = 4 ∧ s ⊆ (9 ^ n - 1).primeFactors by
      refine h_card.not_gt ?_
      rcases this with ⟨s, hs_card, hs_subset⟩
      simpa [hs_card] using Finset.card_le_card hs_subset

    have h13 : 13 ∣ a ∨ 13 ∣ b := (Nat.Prime.dvd_mul (by norm_num)).mp (hab ▸ h13)
    cases h13 with
    | inl ha13 =>
      -- We just need one more prime factor of `a`.
      suffices ∃ p, p.Prime ∧ p ∣ a ∧ p ≠ 2 ∧ p ≠ 13 by
        rcases this with ⟨p, hp_prime, hp_dvd, hp2, hp13⟩
        use {b.minFac, p, 13, 2}
        refine ⟨?_, ?_⟩
        -- Show that all four numbers are distinct.
        · suffices Multiset.Nodup {b.minFac, p, 13, 2} by
            simpa using Multiset.toFinset_card_of_nodup this
          suffices b.minFac ∉ ({p, 13} : Finset ℕ) ∧ b.minFac ≠ 2 ∧ p ≠ 13 ∧ p ≠ 2 by
            simpa [and_assoc]
          refine ⟨?_, ?_, hp13, hp2⟩
          · -- TODO: clean up
            have hb_fac : b.minFac ∈ b.primeFactors := minFac_mem_primeFactors (by simp [b])
            have h_disj := h_coprime.disjoint_primeFactors
            have ha_fac : {p, 13} ⊆ a.primeFactors := by
              have ha_zero : a ≠ 0 := by simpa [hab] using hx_zero
              suffices (Nat.Prime p ∧ p ∣ a) ∧ Nat.Prime 13 ∧ 13 ∣ a by
                simpa [Finset.subset_iff, Nat.mem_primeFactors_of_ne_zero ha_zero]
              refine ⟨?_, ?_⟩
              · exact ⟨hp_prime, hp_dvd⟩
              · exact ⟨by norm_num, ha13⟩
            rw [Finset.disjoint_right] at h_disj
            exact mt (fun h ↦ ha_fac h) (h_disj hb_fac)
          · suffices ¬2 ∣ b by simpa
            suffices Odd b from this.not_two_dvd_nat
            refine Even.add_one ?_
            refine Odd.add_odd ?_ ?_
            · exact .pow (by simp [Nat.odd_iff])
            · exact .pow (by simp [Nat.odd_iff])

        -- Show that all four numbers are prime divisors.
        · simp only [Finset.subset_iff, Finset.mem_insert, Finset.mem_singleton,
            forall_eq_or_imp, forall_eq, Nat.mem_primeFactors_of_ne_zero hx_zero]
          refine ⟨?_, ?_, ?_, ?_⟩
          · refine ⟨?_, ?_⟩
            · exact Nat.minFac_prime (by simp [b])
            · refine .trans b.minFac_dvd ?_
              exact hab ▸ Nat.dvd_mul_left b a
          · refine ⟨hp_prime, ?_⟩
            refine .trans hp_dvd ?_
            exact hab ▸ Nat.dvd_mul_right a b
          · refine ⟨by norm_num, ?_⟩
            refine .trans ha13 ?_
            exact hab ▸ Nat.dvd_mul_right a b
          · exact ⟨Nat.prime_two, hx2⟩

      have hq13 : ¬13 ∣ b := by
        contrapose! h_coprime with hq
        exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) ha13 hq

      -- Apply the same logic to obtain `3 ∣ m`, and therefore
      -- `p = 9 ^ k - 1` can be factored into two coprime numbers.
      have hm3 : 3 ∣ m := by sorry
      rcases hm3 with ⟨k, hmk⟩

      let u := 9 ^ k - 1
      let v := 9 ^ (2 * k) + 9 ^ k + 1
      have huv : a = u * v := by
        suffices (9 ^ m - 1 : ℤ) = (9 ^ k - 1) * (9 ^ (2 * k) + 9 ^ k + 1) by
          simpa [a, u, v, ← @Nat.cast_inj ℤ]
        rw [hmk]
        ring

      have hk : 1 ≤ k := by linarith
      cases hk.eq_or_lt with
      | inl hk =>
        -- If `k = 1`, then `v = 9^2 + 9 + 1 = 91 = 7 * 13`.
        rcases hk with rfl
        suffices 7 ∣ a by refine ⟨7, ?_, this, ?_, ?_⟩ <;> norm_num
        rw [huv]
        suffices 7 ∣ v from this.mul_left u
        norm_num

      | inr hk =>

        sorry

    | inr hb =>
      have ha : ¬13 ∣ a := by
        contrapose! h_coprime with ha
        exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) ha hb

      sorry
