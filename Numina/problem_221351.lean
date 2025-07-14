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

lemma lemma_1 {n : ℕ} (hn : n ≠ 0) : Nat.Coprime (9 ^ n - 1) (9 ^ (2 * n) + 9 ^ n + 1) := by
  sorry

-- Based on `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt`.
lemma exist_odd_prime_and_dvd_mul_add_two {n : ℕ} (hn : 2 < n) :
    ∃ p, Nat.Prime p ∧ p ∣ n * (n + 2) ∧ Odd p := by
  -- It suffices to find a number that divides `n * (n + 2)` and is *not* divisible by 4.
  -- This number can then be used to obtain an odd prime.
  suffices ∃ r, r ∣ n * (n + 2) ∧ 2 < r ∧ ¬4 ∣ r by
    obtain ⟨r, hrn, hr2, hr4⟩ := this
    have := Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hr2
    refine (this.resolve_left hr4).imp ?_
    exact fun p ⟨hp_prime, hpr, hp_odd⟩ ↦ ⟨hp_prime, hpr.trans hrn, hp_odd⟩

  cases n.even_or_odd with
  | inr h_odd =>
    -- For `n` odd, neither `n` nor `n + 2` are divisible by 4; we can use either.
    use n
    refine ⟨Nat.dvd_mul_right _ _, hn, ?_⟩
    refine mt ?_ h_odd.not_two_dvd_nat
    intro h
    exact .trans (by norm_num) h
  | inl h_even =>
    -- For `n` even, only one of the two consecutive even numbers can be divisible by 4.
    -- Use the other one to obtain an odd prime factor.
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := h_even.exists_two_nsmul n
    cases m.even_or_odd with
    | inl h_even =>
      use 2 * m + 2
      refine ⟨Nat.dvd_mul_left _ _, by linarith, ?_⟩
      suffices ¬2 * 2 ∣ 2 * (m + 1) by simpa [mul_add]
      rw [mul_dvd_mul_iff_left two_ne_zero]
      refine Odd.not_two_dvd_nat ?_
      exact Even.add_one h_even
    | inr h_odd =>
      use 2 * m
      refine ⟨Nat.dvd_mul_right _ _, by linarith, ?_⟩
      suffices ¬2 * 2 ∣ 2 * m by simpa
      rw [mul_dvd_mul_iff_left two_ne_zero]
      exact Odd.not_two_dvd_nat h_odd

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
    have hab_coprime : Nat.Coprime a b := lemma_1 (Nat.not_eq_zero_of_lt hm)

    -- It suffices to show that `x` has four distinct prime factors.
    exfalso
    -- suffices ∃ s : Finset ℕ, s.card = 4 ∧ s ⊆ (9 ^ n - 1).primeFactors by
    --   refine h_card.not_gt ?_
    --   rcases this with ⟨s, hs_card, hs_subset⟩
    --   simpa [hs_card] using Finset.card_le_card hs_subset

    suffices ∃ s : Multiset ℕ, 3 < s.card ∧ s.Nodup ∧ s.toFinset ⊆ (9 ^ n - 1).primeFactors by
      refine h_card.not_gt ?_
      rcases this with ⟨s, hs_card, hs_nodup, hs_subset⟩
      calc _
      _ < s.card := hs_card
      _ = s.toFinset.card := (Multiset.toFinset_card_of_nodup hs_nodup).symm
      _ ≤ _ := Finset.card_le_card hs_subset

    have h13 : 13 ∣ a ∨ 13 ∣ b := (Nat.Prime.dvd_mul (by norm_num)).mp (hab ▸ h13)
    cases h13 with
    | inl ha13 =>

      -- -- We just need one more prime factor of `a`.
      -- suffices ∃ p, p.Prime ∧ p ∣ a ∧ p ≠ 2 ∧ p ≠ 13 by
      --   rcases this with ⟨p, hp_prime, hp_dvd, hp2, hp13⟩
      --   use {b.minFac, p, 13, 2}
      --   refine ⟨?_, ?_⟩
      --   -- Show that all four numbers are distinct.
      --   · suffices Multiset.Nodup {b.minFac, p, 13, 2} by
      --       simpa using Multiset.toFinset_card_of_nodup this
      --     suffices b.minFac ∉ ({p, 13} : Finset ℕ) ∧ b.minFac ≠ 2 ∧ p ≠ 13 ∧ p ≠ 2 by
      --       simpa [and_assoc]
      --     refine ⟨?_, ?_, hp13, hp2⟩
      --     · -- TODO: clean up
      --       have hb_fac : b.minFac ∈ b.primeFactors := minFac_mem_primeFactors (by simp [b])
      --       have h_disj := hab_coprime.disjoint_primeFactors
      --       have ha_fac : {p, 13} ⊆ a.primeFactors := by
      --         have ha_zero : a ≠ 0 := by simpa [hab] using hx_zero
      --         suffices (Nat.Prime p ∧ p ∣ a) ∧ Nat.Prime 13 ∧ 13 ∣ a by
      --           simpa [Finset.subset_iff, Nat.mem_primeFactors_of_ne_zero ha_zero]
      --         refine ⟨?_, ?_⟩
      --         · exact ⟨hp_prime, hp_dvd⟩
      --         · exact ⟨by norm_num, ha13⟩
      --       rw [Finset.disjoint_right] at h_disj
      --       exact mt (fun h ↦ ha_fac h) (h_disj hb_fac)
      --     · suffices ¬2 ∣ b by simpa
      --       suffices Odd b from this.not_two_dvd_nat
      --       refine Even.add_one ?_
      --       refine Odd.add_odd ?_ ?_
      --       · exact .pow (by simp [Nat.odd_iff])
      --       · exact .pow (by simp [Nat.odd_iff])

      --   -- Show that all four numbers are prime divisors.
      --   · simp only [Finset.subset_iff, Finset.mem_insert, Finset.mem_singleton,
      --       forall_eq_or_imp, forall_eq, Nat.mem_primeFactors_of_ne_zero hx_zero]
      --     refine ⟨?_, ?_, ?_, ?_⟩
      --     · refine ⟨?_, ?_⟩
      --       · exact Nat.minFac_prime (by simp [b])
      --       · refine .trans b.minFac_dvd ?_
      --         exact hab ▸ Nat.dvd_mul_left b a
      --     · refine ⟨hp_prime, ?_⟩
      --       refine .trans hp_dvd ?_
      --       exact hab ▸ Nat.dvd_mul_right a b
      --     · refine ⟨by norm_num, ?_⟩
      --       refine .trans ha13 ?_
      --       exact hab ▸ Nat.dvd_mul_right a b
      --     · exact ⟨Nat.prime_two, hx2⟩

      -- have hq13 : ¬13 ∣ b := by
      --   contrapose! hab_coprime with hq
      --   exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) ha13 hq

      -- Apply the same logic to obtain `3 ∣ m`, and therefore
      -- `p = 9 ^ k - 1` can be factored into two coprime numbers.
      have hm3 : 3 ∣ m := by sorry
      rcases hm3 with ⟨k, hmk⟩

      let c := 9 ^ k - 1
      let d := 9 ^ (2 * k) + 9 ^ k + 1
      have hcd : a = c * d := by
        suffices (9 ^ m - 1 : ℤ) = (9 ^ k - 1) * (9 ^ (2 * k) + 9 ^ k + 1) by
          simpa [a, c, d, ← @Nat.cast_inj ℤ]
        rw [hmk]
        ring


      -- Since `1 < m = 3 * k`, we have `0 < k`.
      have hk : 1 ≤ k := by linarith
      have hk_zero : k ≠ 0 := Nat.not_eq_zero_of_lt hk  -- TODO?

      have hcd_coprime : Nat.Coprime c d := lemma_1 (Nat.not_eq_zero_of_lt hk)
      cases hk.eq_or_lt with
      | inl hk =>
        -- If `k = 1`, then `d = 9^2 + 9 + 1 = 91 = 7 * 13`, hence `7 ∣ d ∣ a`.
        use {7, 13, b.minFac, 2}
        -- TODO: avoid repeition! do we take two odd factors from p in both cases?
        refine ⟨by simp, ?_, ?_⟩
        · suffices 7 ≠ b.minFac ∧ 13 ≠ b.minFac ∧ ¬2 ∣ b by simpa
          sorry
        · simp [Finset.subset_iff, Nat.mem_primeFactors_of_ne_zero hx_zero]  -- TODO
          sorry

      | inr hk =>

        obtain ⟨p, hp_prime, hpc, hp2⟩ : ∃ p, p.Prime ∧ p ∣ c ∧ Odd p := by
          -- As before, we can factorize `c = 9 ^ k - 1 = (3^k + 1) (3^k - 1)`.
          -- Since these are consecutive even numbers, one of them is not divisible by 4,
          -- hence their product is not a power of 2 (has at least one odd prime factor).
          have hc : c = (3 ^ k - 1) * (3 ^ k - 1 + 2) := by
            calc _
            _ = (3 ^ 2) ^ k - 1 := by simp
            _ = (3 ^ k) ^ 2 - 1 ^ 2 := by simp [Nat.pow_right_comm 3 k 2]
            _ = (3 ^ k + 1) * (3 ^ k - 1) := Nat.sq_sub_sq (3 ^ k) 1
            _ = (3 ^ k - 1) * (3 ^ k + 1) := by ring
            _ = _ := by simp [Nat.sub_add_comm, Nat.one_le_pow]
          simp only [hc]
          refine exist_odd_prime_and_dvd_mul_add_two ?_
          refine Nat.lt_sub_of_add_lt ?_
          exact lt_self_pow₀ (by norm_num) hk

        obtain ⟨q, hq_prime, hqd, hq2⟩ : ∃ p, p.Prime ∧ p ∣ d ∧ Odd p := by
          refine (Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt ?_).resolve_left ?_
          · unfold d
            calc _
            _ < 1 + 1 + 1 := by norm_num
            _ ≤ _ := by gcongr <;> simp [Nat.one_le_pow']
          · -- It is trivial to show `¬4 ∣ d` since `d` is odd.
            suffices ¬2 ∣ d by
              refine mt (.trans ?_) this
              norm_num
            suffices Odd d from this.not_two_dvd_nat
            refine Even.add_one (Odd.add_odd ?_ ?_) <;> simp [Odd.pow, Nat.odd_iff]

        use {p, q, b.minFac, 2}
        refine ⟨by simp, ?_, ?_⟩
        · suffices p ≠ q ∧ p ≠ b.minFac ∧ p ≠ 2 ∧ q ≠ b.minFac ∧ q ≠ 2 ∧ ¬2 ∣ b by
            simpa [and_assoc]
          split_ands
          · -- Follows from `p ∣ c`, `q ∣ d`, and `c` and `d` are coprime.
            contrapose! hcd_coprime with hpq
            rw [Nat.Prime.not_coprime_iff_dvd]
            exact ⟨p, hp_prime, hpc, hpq ▸ hqd⟩
          · contrapose! hab_coprime with hp
            rw [Nat.Prime.not_coprime_iff_dvd]
            refine ⟨p, hp_prime, ?_, ?_⟩
            · refine hpc.trans ?_
              exact hcd ▸ Nat.dvd_mul_right c d
            · exact hp ▸ Nat.minFac_dvd b
          · refine mt hp_prime.even_iff.mpr ?_
            simpa
          · contrapose! hab_coprime with hq
            rw [Nat.Prime.not_coprime_iff_dvd]
            refine ⟨q, hq_prime, ?_, ?_⟩
            · refine hqd.trans ?_
              exact hcd ▸ Nat.dvd_mul_left d c
            · exact hq ▸ Nat.minFac_dvd b
          · refine mt hq_prime.even_iff.mpr ?_
            simpa
          · -- TODO: avoid repeitition for b and d?
            suffices Odd b from this.not_two_dvd_nat
            refine Even.add_one (Odd.add_odd ?_ ?_) <;> simp [Odd.pow, Nat.odd_iff]

        · simp [Finset.subset_iff, Nat.mem_primeFactors_of_ne_zero hx_zero]
          -- TODO: add `c * d ∣ x` as assumption? group by factor?
          refine ⟨?_, ?_, ?_, ?_⟩
          · refine ⟨hp_prime, ?_⟩
            calc _
            _ ∣ c := hpc
            _ ∣ c * d := Nat.dvd_mul_right c d
            _ = a := by rw [hcd]
            _ ∣ a * b := Nat.dvd_mul_right a b
            _ = _ := by rw [hab]
          · refine ⟨hq_prime, ?_⟩
            calc _
            _ ∣ d := hqd
            _ ∣ c * d := Nat.dvd_mul_left d c
            _ = a := by rw [hcd]
            _ ∣ a * b := Nat.dvd_mul_right a b
            _ = _ := by rw [hab]
          · refine ⟨Nat.minFac_prime <| by simp [b], ?_⟩
            calc _
            _ ∣ b := Nat.minFac_dvd b
            _ ∣ a * b := Nat.dvd_mul_left b a
            _ = _ := by rw [hab]
          · exact ⟨Nat.prime_two, hx2⟩

    | inr hb =>
      have ha : ¬13 ∣ a := by
        contrapose! hab_coprime with ha
        exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) ha hb

      sorry
