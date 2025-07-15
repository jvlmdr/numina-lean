-- https://cloud.kili-technology.com/label/projects/label/cmcboth12006bueaxcg0nw74p

import Mathlib

/- Given a natural number $x = 9^{n} - 1$, where $n$ is a natural number. It is known that
$x$ has exactly three distinct prime divisors, one of which is 13. Find $x$. -/

-- If `b ^ c ≡ 1 [MOD n]`, then `
lemma pow_mod_periodic {b n c : ℕ} (hc : b ^ c % n = 1) : (b ^ · % n).Periodic c := by
  simp [pow_add, Nat.mul_mod, hc]

-- The remainders of the powers of 9 when divided by 13 are 1, 9, 3 repeating cyclically.
lemma nine_pow_mod_thirteen_periodic : (9 ^ · % 13).Periodic 3 := pow_mod_periodic rfl

lemma nine_pow_mod_thirteen_eq_one_iff (n : ℕ) :
    9 ^ n % 13 = 1 ↔ n % 3 = 0 := by
  rw [← nine_pow_mod_thirteen_periodic.map_mod_nat]
  -- Test the three possible values of `n % 3`.
  suffices ∀ k < 3, 9 ^ k % 13 = 1 ↔ k = 0 from this (n % 3) (Nat.mod_lt n three_pos)
  intro k hk
  interval_cases k <;> simp

-- The remainders of the powers of 13 when divided by 8 are 1, 5 repeating cyclically.
lemma thirteen_pow_mod_eight_periodic : (13 ^ · % 8).Periodic 2 := pow_mod_periodic rfl

lemma thirteen_pow_mod_eight_eq (n : ℕ) : 13 ^ n % 8 = 1 ∨ 13 ^ n % 8 = 5 := by
  rw [← thirteen_pow_mod_eight_periodic.map_mod_nat]
  -- Test the two possible values of `n % 2`.
  suffices ∀ k < 2, 13 ^ k % 8 ∈ ({1, 5} : Set ℕ) from this (n % 2) (Nat.mod_lt n two_pos)
  intro k hk
  interval_cases k <;> simp

-- TODO: need this?
lemma minFac_mem_primeFactors {n : ℕ} (hn : 1 < n) : n.minFac ∈ n.primeFactors := by
  rw [Nat.mem_primeFactors]
  split_ands
  · exact Nat.minFac_prime hn.ne'
  · exact Nat.minFac_dvd n
  · linarith

-- TODO: need this?
lemma ne_of_odd_of_even {a b : ℕ} (ha : Odd a) (hb : Even b) : a ≠ b := by
  contrapose! hb
  simpa using hb ▸ ha

lemma ne_of_even_of_odd {a b : ℕ} (ha : Even a) (hb : Odd b) : a ≠ b := by
  contrapose! hb
  simpa using hb ▸ ha

lemma ne_two_of_odd {n : ℕ} (hn : Odd n) : n ≠ 2 := ne_of_odd_of_even hn even_two

-- The numbers `9 ^ m - 1` and `9 ^ (2 * m) + 9 ^ m + 1` are coprime for `m` positive.
lemma lemma_1 {m : ℕ} (hm : m ≠ 0) : Nat.Coprime (9 ^ m - 1) (9 ^ (2 * m) + 9 ^ m + 1) := by
  let p := 9 ^ m - 1
  let q := 9 ^ (2 * m) + 9 ^ m + 1
  refine Nat.coprime_of_dvd fun k hk_prime hp hq ↦ ?_
  -- Observe that `q - (9 ^ (2 * m) - 1) - (9 ^ m - 1) = q - p * (9 ^ m + 2) = 3`.
  -- Therefore, if `k` divides both `p` and `q`, it must be equal to 3.
  -- However, `p = 9 ^ m - 1` is not divisible by 3.
  suffices k ∣ 3 by
    rw [Nat.prime_dvd_prime_iff_eq hk_prime Nat.prime_three] at this
    rcases this with rfl
    replace hp : 1 ≡ (3 ^ 2) ^ m [MOD 3] := by
      simpa [Nat.modEq_iff_dvd', Nat.one_le_pow] using hp
    suffices 1 ≠ (3 ^ 2) ^ m % 3 from this hp
    simp [Nat.pow_mod, hm]

  calc _
  _ ∣ q - p * (9 ^ m + 2) := Nat.dvd_sub' hq (hp.mul_right _)
  _ = q - ((9 ^ (2 * m) - 1) + (9 ^ m - 1)) := by
    congr
    unfold p
    -- Easy to prove using `ring` in `ℤ`.
    have : (9 ^ m - 1 : ℤ) * (9 ^ m + 2) = 9 ^ (2 * m) - 1 + (9 ^ m - 1) := by ring
    simpa [← @Nat.cast_inj ℤ]
  _ = 3 := by
    unfold q
    -- Easy to prove using `ring` in `ℤ`.
    have : 9 ^ (2 * m) + 9 ^ m + 1 - (9 ^ (2 * m) - 1 + (9 ^ m - 1)) = (3 : ℤ) := by ring
    -- Prove that subtraction does not lead to truncation for `Nat.cast_sub`.
    have hq : 9 ^ (2 * m) - 1 + (9 ^ m - 1) ≤ 9 ^ (2 * m) + 9 ^ m + 1 := by
      calc _
      _ ≤ 9 ^ (2 * m) + 9 ^ m := by refine add_le_add ?_ ?_ <;> simp
      _ ≤ _ := by simp
    simpa [← @Nat.cast_inj ℤ, hq]

-- The product `n * (n + 2)` is not a power of 2 (i.e. has an odd prime factor) for `n > 2`.
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
  -- For `n` odd, neither `n` nor `n + 2` are divisible by 4; we can use either.
  -- For `n` even, *only one* of two consecutive even numbers can be divisible by 4.
  -- Use the other one to obtain an odd prime factor.
  cases n.even_or_odd with
  | inr h_odd =>
    use n
    refine ⟨Nat.dvd_mul_right _ _, hn, ?_⟩
    refine mt ?_ h_odd.not_two_dvd_nat
    intro h
    exact .trans (by norm_num) h
  | inl h_even =>
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

theorem number_theory_221351 (x : ℕ) (n : ℕ) (hx : x = 9 ^ n - 1)
    (h_card : x.primeFactors.card = 3) (h13 : 13 ∣ x) :
    x = 728 := by
  -- Replace `x` with `9 ^ n - 1` everywhere.
  rcases hx with rfl
  -- Clearly `x` is even, therefore the prime factors include {2, 13}.
  have hx2 : 2 ∣ 9 ^ n - 1 := by
    rw [← even_iff_two_dvd]
    refine Odd.tsub_odd (.pow ?_) odd_one
    simp [Nat.odd_iff]

  -- Since `13 ∣ x = 9 ^ n - 1`, we must have `n ≡ 0 [MOD 3]` by the periodicity of `9 ^ n % 13`.
  have hn3 : 3 ∣ n := by
    rw [Nat.dvd_iff_mod_eq_zero, ← nine_pow_mod_thirteen_eq_one_iff]
    suffices 1 ≡ 9 ^ n [MOD 13] from this.symm
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow' n _)).mpr h13
  -- Obtain `n = 3 * m`.
  rcases hn3 with ⟨m, hmn⟩
  -- Use the factorization `a^3 - b^3 = (a - b) (a^2 + ab + b^2)` to factor `9 ^ (3 m) - 1`.
  let a : ℕ := 9 ^ m - 1
  let b : ℕ := 9 ^ (2 * m) + 9 ^ m + 1
  have hx_ab : 9 ^ n - 1 = a * b := by
    -- Easy to prove using `ring` in `ℤ`.
    have : (9 ^ (3 * m) - 1 : ℤ) = (9 ^ m - 1 : ℤ) * (9 ^ (2 * m) + 9 ^ m + 1) := by ring
    simpa [← @Nat.cast_inj ℤ, hmn, a, b]

  -- Consider the cases `m = 0`, `m = 1`, `m > 1`.
  cases le_or_lt m 1 with
  | inl hm =>
    -- Replace `n` with `3 * m` everywhere.
    rcases hmn with rfl
    interval_cases m
    · -- Contradiction: `9 ^ 0 - 1 = 0` does not have 3 prime factors.
      simp at h_card
    · -- This is the valid solution! `9 ^ 3 - 1 = 728 = 2^3 * 7 * 13`
      norm_num

  | inr hm =>
    -- It remains to show that `1 < m` leads to a contradiction.
    exfalso
    -- Use the lemma above to obtain that the two factors are coprime.
    have hab_coprime : Nat.Coprime a b := lemma_1 (by linarith)
    -- It is trivial to show that `b = _ + 1` is non-zero.
    -- It will be useful to have the same fact for `a`.
    have hx_zero : 9 ^ n - 1 ≠ 0 := by
      refine ne_of_gt ?_
      suffices 1 < 9 ^ n by simpa
      exact Nat.one_lt_pow (by linarith) (by norm_num)
    have ha_zero : a ≠ 0 := by
      refine ne_of_gt ?_
      suffices 1 < 9 ^ m by simpa [a]
      exact Nat.one_lt_pow (by linarith) (by norm_num)

    -- We know that `x = a * b` (coprime product) is divisible by 2 and 13.
    -- Further, since `b = 9 ^ (2 * m) + 9 ^ m + 1` is odd, we must have `2 ∣ a`.
    -- Split based on whether 13 divides `a` or `b`.
    have h13 : 13 ∣ a ∨ 13 ∣ b := (Nat.Prime.dvd_mul (by norm_num)).mp (hx_ab ▸ h13)
    cases h13 with
    | inl h13 =>
      -- Since `13 ∣ a = 9 ^ m - 1`, we can apply the same logic to obtain `m = 3 k` with `k > 0`
      -- and factor `a = 9 ^ (3 k) - 1 = c * d` into two coprime factors.
      have hm3 : 3 ∣ m := by
        rw [Nat.dvd_iff_mod_eq_zero, ← nine_pow_mod_thirteen_eq_one_iff]
        suffices 1 ≡ 9 ^ m [MOD 13] from this.symm
        exact (Nat.modEq_iff_dvd' (Nat.one_le_pow' m _)).mpr h13
      rcases hm3 with ⟨k, hkm⟩
      let c := 9 ^ k - 1
      let d := 9 ^ (2 * k) + 9 ^ k + 1
      have hcd : a = c * d := by
        have : (9 ^ (3 * k) - 1 : ℤ) = (9 ^ k - 1) * (9 ^ (2 * k) + 9 ^ k + 1) := by ring
        simpa [← @Nat.cast_inj ℤ, hkm, a, c, d]
      have hk : 1 ≤ k := by linarith
      have hcd_coprime : Nat.Coprime c d := lemma_1 (Nat.not_eq_zero_of_lt hk)

      -- Next we split based on whether `k = 1` or `k > 1`.
      -- We know that `x` is even and therefore has 2 as a prime factor.
      -- Since `b` is at least 3, it has at least one odd prime factor.
      -- Therefore it will suffice to find 2 odd prime factors of `a`.

      suffices ∃ s : Finset ℕ, 2 ≤ s.card ∧ s ⊆ a.primeFactors.erase 2 by
        rcases this with ⟨s, hs_card, hs_mem⟩

        -- refine h_card.not_gt ?_
        -- have := Finset.insert_erase (s := Nat.primeFactors (9 ^ n - 1)) (a := 2) sorry

        sorry
        -- calc _
        -- _ = 2 + 1 := by sorry
        -- _ <

        -- suffices 2 < (9 ^ n - 1).primeFactors.card - 1 from Nat.add_lt_of_lt_sub this
        -- calc _
        -- _ < ((9 ^ n - 1).primeFactors.erase 2).card := by sorry
        -- _ = _ := by sorry

        -- suffices 2 < ((9 ^ n - 1).primeFactors.erase 2).card by
        --   rw [Finset.card_erase_of_mem] at this
        --   swap
        --   · rw [Nat.mem_primeFactors_of_ne_zero hx_zero]
        --     exact ⟨Nat.prime_two, hx2⟩

        -- calc _
        -- _ < 4 := by simp

        -- -- _ ≤ s.card + 1 := by simpa using hs_card
        -- -- _ ≤ a.primeFactors.card + b.primeFactors.card := by
        -- --   refine add_le_add ?_ ?_
        -- --   · exact Finset.card_le_card hs_mem
        -- --   · simp [b]
        -- -- _ ≤ (a * b).primeFactors.card := by
        -- --   rw [hab_coprime.primeFactors_mul]
        -- --   rw [Finset.card_union_of_disjoint hab_coprime.disjoint_primeFactors]

        -- _ = ((a * b).primeFactors.erase 2).card := by sorry

        -- _ = _ := by
        --   rw [hx_ab]

      -- To make this easier to specify, use a `Multiset`.
      suffices ∃ s : Multiset ℕ, s.Nodup ∧ 3 ≤ s.card ∧ s.toFinset ⊆ a.primeFactors by
        rcases this with ⟨s, hs_nodup, hs_card, hs_mem⟩
        refine ⟨s.toFinset, ?_, hs_mem⟩
        rw [Multiset.toFinset_card_of_nodup hs_nodup]
        exact hs_card

      -- -- It will suffice to find two odd prime factors of `a`.
      -- suffices ∃ p q, (p.Prime ∧ p ∣ a ∧ p ≠ 2) ∧ (q.Prime ∧ q ∣ a ∧ q ≠ 2) ∧ p ≠ q by
      --   rcases this with ⟨p, q, ⟨hp_prime, hpa, hp2⟩, ⟨hq_prime, hqa, hq2⟩, hpq⟩
      --   refine h_card.not_gt ?_
      --   calc _
      --   _ < Multiset.card {p, q, 2} + Multiset.card {b.minFac} := by simp
      --   _ = (Multiset.toFinset {p, q, 2}).card + (Multiset.toFinset {b.minFac}).card := by
      --     congr 1
      --     suffices Multiset.Nodup {p, q, 2} from (Multiset.toFinset_card_of_nodup this).symm
      --     suffices p ≠ q ∧ p ≠ 2 ∧ q ≠ 2 by simpa [and_assoc]
      --     exact ⟨hpq, hp2, hq2⟩
      --   _ = Finset.card {p, q, 2} + Finset.card {b.minFac} := by simp
      --   _ ≤ a.primeFactors.card + b.primeFactors.card := by
      --     refine add_le_add ?_ ?_
      --     · refine Finset.card_le_card ?_
      --       suffices (p.Prime ∧ p ∣ a) ∧ (q.Prime ∧ q ∣ a) ∧ Nat.Prime 2 ∧ 2 ∣ a by
      --         simpa [Finset.subset_iff, ha_zero]
      --       refine ⟨⟨hp_prime, hpa⟩, ⟨hq_prime, hqa⟩, Nat.prime_two, ?_⟩
      --       suffices Nat.Coprime 2 b by
      --         rw [hx_ab] at hx2
      --         exact this.dvd_of_dvd_mul_right hx2
      --       refine Odd.coprime_two_left ?_
      --       refine Even.add_one (Odd.add_odd ?_ ?_) <;> simp [Odd.pow, Nat.odd_iff]
      --     · refine Finset.card_le_card ?_
      --       suffices b.minFac.Prime ∧ b.minFac ∣ b by simpa [Finset.subset_iff]
      --       refine ⟨Nat.minFac_prime ?_, Nat.minFac_dvd b⟩
      --       exact ne_of_gt (by simp [b])
      --   _ = (a * b).primeFactors.card := by
      --     rw [hab_coprime.primeFactors_mul]
      --     rw [Finset.card_union_of_disjoint hab_coprime.disjoint_primeFactors]
      --   _ = _ := by rw [hx_ab]

      cases hk.eq_or_lt with
      | inl hk =>
        -- If `k = 1`, then `d = 9^2 + 9 + 1 = 91 = 7 * 13`, hence `7 ∣ d ∣ a`.
        use {2, 7, 13}
        split_ands
        · simp
        · simp
        · suffices (Nat.Prime 2 ∧ 2 ∣ a) ∧ (Nat.Prime 7 ∧ 7 ∣ a) ∧ Nat.Prime 13 ∧ 13 ∣ a by
            simpa [Finset.subset_iff, ha_zero]
          refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
          · sorry
          ·
            sorry
          · sorry


        suffices 7 ∣ a by refine ⟨7, ?_, this, ?_, 13, ?_, h13, ?_, ?_⟩ <;> norm_num
        rcases hk with rfl
        exact .trans (by norm_num) (Dvd.intro_left c hcd.symm)

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

        refine ⟨p, hp_prime, ?_, ne_two_of_odd hp2, q, hq_prime, ?_, ne_two_of_odd hq2, ?_⟩
        · exact hpc.trans (Dvd.intro d hcd.symm)
        · exact hqd.trans (Dvd.intro_left c hcd.symm)
        · contrapose! hcd_coprime with hpq
          rw [Nat.Prime.not_coprime_iff_dvd]
          exact ⟨p, hp_prime, hpc, hpq ▸ hqd⟩

    | inr h13 =>
      -- We know that `x = a * b` is divisible by 2 and 13.
      -- Since `a` is the product of two consecutive even numbers > 2, it is not a power of 2.
      -- Therefore, `a` has another odd prime factor `p`.
      -- Note that `p ≠ 13` since `13 ∣ b` and `a` is coprimme to `b`.
      obtain ⟨p, hp_prime, hpa, hp_odd⟩ : ∃ p, p.Prime ∧ p ∣ a ∧ Odd p := by
        -- As before, we can factorize `a = 9 ^ m - 1 = (3^m + 1) (3^m - 1)`.
        -- Since these are consecutive even numbers, one of them is not divisible by 4,
        -- hence their product is not a power of 2 (has at least one odd prime factor).
        have ha : a = (3 ^ m - 1) * (3 ^ m - 1 + 2) := by
          calc _
          _ = (3 ^ 2) ^ m - 1 := by simp
          _ = (3 ^ m) ^ 2 - 1 ^ 2 := by simp [Nat.pow_right_comm 3 m 2]
          _ = (3 ^ m + 1) * (3 ^ m - 1) := Nat.sq_sub_sq (3 ^ m) 1
          _ = (3 ^ m - 1) * (3 ^ m + 1) := by ring
          _ = _ := by simp [Nat.sub_add_comm, Nat.one_le_pow]
        simp only [ha]
        refine exist_odd_prime_and_dvd_mul_add_two ?_
        refine Nat.lt_sub_of_add_lt ?_
        exact lt_self_pow₀ (by norm_num) hm

      -- Therefore, `x = a * b` cannot have any other prime factors besides 2, 13, `p`.
      -- However, `p` is a factor of `a`, and 2 cannot divide `b` since it is odd.
      -- Therefore, `b` must be a power of 13.
      -- Note that `b = 9 ^ (2 * m) + 9 ^ m + 1 ≡ 3 [MOD 8]`.
      -- If we consider powers of 13 modulo 8, we see that they alterante 1, 5, 1, 5.
      -- This provides a contradiction.

      -- Note: We don't require the fact that `k > 0`.
      suffices ∃ k, b = 13 ^ k by
        rcases this with ⟨k, hk⟩
        have h_pow_mem : 13 ^ k % 8 ∈ ({1, 5} : Set ℕ) := by
          simpa using thirteen_pow_mod_eight_eq k
        suffices b % 8 = 3 by simp [← hk, this] at h_pow_mem
        suffices b ≡ 3 [MOD 8] by simpa [Nat.ModEq]
        unfold b
        calc _
        _ ≡ 1 + 1 + 1 [MOD 8] := by
          have : 9 ≡ 1 [MOD 8] := by simp [Nat.ModEq]
          refine .add (.add ?_ ?_) rfl
          · simpa using this.pow (2 * m)
          · simpa using this.pow m
        _ ≡ _ [MOD 8] := rfl

      suffices hb : b.primeFactors = {13} by
        use b.primeFactorsList.length
        refine Nat.eq_prime_pow_of_unique_prime_dvd (by simp) ?_
        intro x hx_prime hx_dvd
        suffices x ∈ b.primeFactors by simpa [hb]
        rw [Nat.mem_primeFactors]
        exact ⟨hx_prime, hx_dvd, by simp⟩

      -- TODO: cleanup

      rw [hx_ab, hab_coprime.primeFactors_mul,
        Finset.card_union_of_disjoint hab_coprime.disjoint_primeFactors] at h_card

      have ha_card : 2 ≤ a.primeFactors.card := by
        suffices ∃ s : Finset ℕ, 2 ≤ s.card ∧ s ⊆ a.primeFactors by
          rcases this with ⟨s, hs_card, hs_subset⟩
          exact le_trans hs_card (Finset.card_le_card hs_subset)

        use {p, 2}
        refine ⟨?_, ?_⟩
        · -- TODO: just use `.card = 2`?
          suffices Multiset.Nodup {p, 2} by
            simpa using (Multiset.toFinset_card_of_nodup this).ge
          suffices p ≠ 2 by simpa
          contrapose! hp_odd with hp
          simp [hp]

        · simp [Finset.subset_iff, Nat.mem_primeFactors_of_ne_zero ha_zero]  -- TODO
          refine ⟨?_, ?_⟩
          · exact ⟨hp_prime, hpa⟩
          · refine ⟨Nat.prime_two, ?_⟩
            -- Since `2 ∣ x = a * b` and `b` is odd, we must have `2 ∣ a`.
            have : 2 ∣ a ∨ 2 ∣ b := by
              refine Nat.prime_two.dvd_mul.mp ?_
              exact hx_ab ▸ hx2
            refine this.resolve_right ?_
            refine Odd.not_two_dvd_nat ?_
            -- TODO: check for repetition?
            refine Even.add_one (Odd.add_odd ?_ ?_) <;> simp [Odd.pow, Nat.odd_iff]

      -- TODO?
      have : b.primeFactors.card ≤ 1 := by
        suffices b.primeFactors.card + 2 ≤ 3 by simpa
        rw [add_comm]
        calc _
        _ ≤ a.primeFactors.card + b.primeFactors.card := by gcongr  -- TODO
        _ = 3 := h_card  -- TODO: move here?

      refine (Finset.eq_singleton_or_nontrivial ?_).resolve_right ?_
      · rw [Nat.mem_primeFactors]
        exact ⟨by norm_num, h13, by simp⟩
      · rw [← Finset.one_lt_card_iff_nontrivial]
        simpa
