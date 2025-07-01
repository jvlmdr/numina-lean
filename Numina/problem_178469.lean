-- https://cloud.kili-technology.com/label/projects/label/cmcbouv7300o6ueaxzuvpf263

import Mathlib

open Real

/- Let $n$ be an integer of the form $a^2 + b^2$ where $a$ and $b$ are relatively prime integers
and such that if $p$ is a prime, $p \leq \sqrt{n}$, then $p$ divides $a b$.
Determine all such $n$. -/

theorem number_theory_175773 (n : ℕ) :
    (∃ a b, a.Coprime b ∧ n = a^2 + b^2 ∧ ∀ p : ℕ, p ≤ √n → p.Prime → p ∣ a * b) ↔
    n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 13 := by
  -- Replace the real square root with integer condition `p ^ 2 ≤ n`.
  have h_le_sqrt (p n : ℕ) : p ≤ √n ↔ p ^ 2 ≤ n := by
    calc _
    _ ↔ ↑(p ^ 2) ≤ (n : ℝ) := by simp [le_sqrt]
    _ ↔ _ := Nat.cast_le
  simp only [h_le_sqrt]

  constructor
  · intro ⟨a, b, h_coprime, h_add, h_dvd⟩
    -- First consider whether `n` is prime, composite, or less than 2.
    by_cases hn_prime : n.Prime
    · refine .inr ?_
      wlog hab : a ≤ b generalizing a b
      · refine this b a h_coprime.symm ?_ ?_ (le_of_not_ge hab)
        · simpa [add_comm]
        · simpa [mul_comm]

      -- Replace `b` with `a + d`.
      obtain ⟨d, rfl⟩ : ∃ d, b = a + d := Nat.exists_eq_add_of_le hab
      rw [Nat.coprime_self_add_right] at h_coprime
      cases le_or_lt d 1 with
      | inl hd =>
        interval_cases d
        · have ha : a = 1 := by simpa using h_coprime
          have hn : n = 2 := by simpa [ha] using h_add
          exact .inl hn
        · -- TODO: the hard part
          sorry
      | inr hd =>
        -- TODO: comment
        let p := d.minFac
        have hp_prime : p.Prime := Nat.minFac_prime hd.ne'
        have hp_le : p ^ 2 ≤ n := by
          calc _
          _ ≤ d ^ 2 := by
            refine Nat.pow_le_pow_left ?_ 2
            exact Nat.minFac_le (by linarith)
          _ ≤ (a + d) ^ 2 := Nat.pow_le_pow_left (by simp) 2
          _ ≤ _ := by simp [h_add]

        -- Showing that `p < n` and `p ∣ n` contradicts the assumption that `n` is prime.
        exfalso
        refine Nat.not_prime_of_dvd_of_lt ?_ hp_prime.two_le ?_ hn_prime
        · rw [h_add]
          -- Rewrite `a ^ 2 + b ^ 2` as `(a - b) ^ 2 + 2 * a * b`.
          suffices p ∣ d ^ 2 + 2 * (a * (a + d)) by
            convert this using 1
            ring
          refine dvd_add ?_ ?_
          · exact dvd_pow d.minFac_dvd two_ne_zero
          · exact (h_dvd p hp_le hp_prime).mul_left 2
        · refine lt_of_lt_of_le ?_ hp_le
          exact lt_self_pow₀ hp_prime.one_lt one_lt_two

    · refine .inl ?_
      cases le_or_lt n 1 with
      | inl hn =>
        interval_cases n
        · -- Find a contradiction in that `a = b = 0`, hence their gcd is 0.
          exfalso
          obtain ⟨ha, hb⟩ : a = 0 ∧ b = 0 := by simpa using Nat.add_eq_zero.mp h_add.symm
          simp [ha, hb] at h_coprime
        · rfl
      | inr hn =>
        exfalso
        let p := n.minFac
        have hp_prime : p.Prime := Nat.minFac_prime (by linarith)
        specialize h_dvd p (Nat.minFac_sq_le_self (by linarith) hn_prime) hp_prime
        suffices p ∣ a ∧ p ∣ b from
          Nat.not_coprime_of_dvd_of_dvd hp_prime.one_lt this.1 this.2 h_coprime
        rw [hp_prime.dvd_mul] at h_dvd
        -- wlog hab : a ≤ b generalizing a b
        -- · rw [and_comm]
        --   refine this b a h_coprime.symm ?_ ?_ (le_of_not_ge hab)
        --   · simpa [add_comm] using h_add
        --   · simpa [or_comm] using h_dvd
        -- TODO: Can we use symmetry to avoid replication here?
        refine h_dvd.elim ?_ ?_
        · refine fun ha ↦ ⟨ha, ?_⟩
          suffices p ∣ b ^ 2 from hp_prime.dvd_of_dvd_pow this
          suffices p ∣ a ^ 2 + b ^ 2 by
            refine (Nat.dvd_add_iff_right ?_).mpr this
            exact dvd_pow ha two_ne_zero
          simpa [← h_add] using Nat.minFac_dvd n
        · refine fun hb ↦ ⟨?_, hb⟩
          suffices p ∣ a ^ 2 from hp_prime.dvd_of_dvd_pow this
          suffices p ∣ a ^ 2 + b ^ 2 by
            refine (Nat.dvd_add_iff_left ?_).mpr this
            exact dvd_pow hb two_ne_zero
          simpa [← h_add] using Nat.minFac_dvd n

  · -- Substitute the different values of `n` and provide `a, b` for each.
    revert n
    simp only [forall_eq_or_imp, forall_eq]
    -- Replace `p ^ 2 ≤ n` with `p ≤ Nat.sqrt n`, then use `interval_cases` to check all such `p`.
    simp only [← Nat.le_sqrt']
    split_ands
    · use 0, 1
      simp
    · refine ⟨1, 1, rfl, rfl, fun p hp ↦ ?_⟩
      interval_cases p <;> norm_num
    · refine ⟨1, 2, rfl, rfl, fun p hp ↦ ?_⟩
      interval_cases p <;> norm_num
    · refine ⟨2, 3, rfl, rfl, fun p hp ↦ ?_⟩
      interval_cases p <;> norm_num


  -- by_cases hn_prime : n.Prime
  -- · -- Exclude the non-prime solution `n = 1`.
  --   refine Iff.trans ?_ (or_iff_right hn_prime.ne_one).symm
  --   rw [exists_comm]
  --   calc _
  --   _ ↔ ∃ b, ∃ a, b ≤ a ∧ a ^ 2 + b ^ 2 = n ∧ a.Coprime b ∧
  --       ∀ p : ℕ, p.Prime → p ^ 2 ≤ n → p ∣ a * b := by
  --     sorry

  --   _ ↔ ∃ b d, (b + d) ^ 2 + b ^ 2 = n ∧ (b + d).Coprime b ∧
  --       ∀ p : ℕ, p.Prime → p ^ 2 ≤ n → p ∣ (b + d) * b := by
  --     refine exists_congr fun b ↦ ?_
  --     simp only [le_iff_exists_add, ← exists_and_right]
  --     rw [exists_comm]
  --     simp

  --   _ ↔ ∃ d b, (b + d) ^ 2 + b ^ 2 = n ∧ (b + d).Coprime b ∧
  --       ∀ p : ℕ, p.Prime → p ^ 2 ≤ n → p ∣ (b + d) * b :=
  --     exists_comm

  --   _ ↔ (∃ b, b ^ 2 + b ^ 2 = n ∧ b = 1 ∧ ∀ p : ℕ, p.Prime → p ^ 2 ≤ n → p ∣ b * b) ∨
  --       ∃ d b, (b + d + 1) ^ 2 + b ^ 2 = n ∧
  --         (d + 1).Coprime b ∧ ∀ p : ℕ, p.Prime → p ^ 2 ≤ n → p ∣ (b + d + 1) * b := by
  --     rw [← Nat.or_exists_add_one]
  --     simp [add_assoc]

  --   _ ↔ (n = 2 ∧ ∀ p : ℕ, p.Prime → p ^ 2 ≤ n → p = 1) ∨
  --       ∃ d b, (b + d + 1) ^ 2 + b ^ 2 = n ∧
  --         (d + 1).Coprime b ∧ ∀ p : ℕ, p.Prime → p ^ 2 ≤ n → p ∣ (b + d + 1) * b := by
  --     -- TODO: re-order?
  --     simp [and_left_comm (b := _ = 1), eq_comm (b := n)]

  --   _ ↔ _ := by
  --     refine or_congr ?_ ?_
  --     · refine and_iff_left_of_imp fun hn p hp_prime hp ↦ ?_
  --       rcases hn with rfl
  --       exfalso
  --       refine hp_prime.two_le.not_lt ?_
  --       suffices p ^ 2 < 2 ^ 2 from lt_of_pow_lt_pow_left' 2 this
  --       linarith
  --     · calc _
  --       _ ↔ (∃ b, (b + 1) ^ 2 + b ^ 2 = n ∧ ∀ p : ℕ, p.Prime → p ^ 2 ≤ n → p ∣ (b + 1) * b) ∨
  --           ∃ d b, (b + d + 2) ^ 2 + b ^ 2 = n ∧ (d + 2).Coprime b ∧
  --             ∀ p : ℕ, p.Prime → p ^ 2 ≤ n → p ∣ (b + d + 2) * b := by
  --         rw [← Nat.or_exists_add_one]
  --         simp [add_assoc]
  --       -- TODO: is there not a way to avoid doing this?
  --       _ ↔ (n = 5 ∨ n = 13) ∨ False := by
  --         -- TODO: write as `n = a ^ 2 + b ^ 2` instead?
  --         refine or_congr ?_ ?_
  --         · rw [← Nat.or_exists_add_one]
  --           rw [← Nat.or_exists_add_one]
  --           rw [← Nat.or_exists_add_one]
  --           simp [add_assoc, eq_comm (b := n)]
  --           sorry
  --         · simp only [iff_false, not_exists, not_and]
  --           intro d b hn h_coprime h_dvd
  --           sorry

  --       _ ↔ _ := by simp

  --       -- rw [← Nat.or_exists_add_one]
  --       -- simp [add_assoc]
  --       -- sorry

  -- · -- Exclude the prime solutions.
  --   refine Iff.trans ?_ ((or_iff_left ?_).symm)
  --   swap
  --   · suffices ∀ n : ℕ, n = 2 ∨ n = 5 ∨ n = 13 → n.Prime from mt (this n) hn_prime
  --     norm_num

  --   -- TODO: Since `n` is composite...
  --   -- First eliminate the cases `n = 0` and `n = 1` (not prime or composite).
  --   cases le_or_lt n 1 with
  --   | inl hn =>
  --     interval_cases n
  --     · simp
  --     · refine (iff_true_right rfl).mpr ?_
  --       use 0, 1
  --       simp

  --   | inr hn =>
  --     refine (iff_false_right ?_).mpr ?_
  --     · linarith
  --     simp only [not_exists, not_and]
  --     intro a b hab h_coprime
  --     contrapose! h_coprime with h_dvd

  --     let p := n.minFac
  --     have hp_prime : p.Prime := Nat.minFac_prime (by linarith)
  --     specialize h_dvd p hp_prime (Nat.minFac_sq_le_self (by linarith) hn_prime)

  --     suffices p ∣ a ∧ p ∣ b from Nat.not_coprime_of_dvd_of_dvd hp_prime.one_lt this.1 this.2
  --     rw [hp_prime.dvd_mul] at h_dvd
  --     -- TODO: Can we use symmetry to avoid replication here?
  --     refine h_dvd.elim ?_ ?_
  --     · refine fun ha ↦ ⟨ha, ?_⟩
  --       suffices p ∣ b ^ 2 from hp_prime.dvd_of_dvd_pow this
  --       suffices p ∣ a ^ 2 + b ^ 2 by
  --         refine (Nat.dvd_add_iff_right ?_).mpr this
  --         exact dvd_pow ha two_ne_zero
  --       rw [hab]
  --       exact Nat.minFac_dvd n
  --     · refine fun hb ↦ ⟨?_, hb⟩
  --       suffices p ∣ a ^ 2 from hp_prime.dvd_of_dvd_pow this
  --       suffices p ∣ a ^ 2 + b ^ 2 by
  --         refine (Nat.dvd_add_iff_left ?_).mpr this
  --         exact dvd_pow hb two_ne_zero
  --       rw [hab]
  --       exact Nat.minFac_dvd n
