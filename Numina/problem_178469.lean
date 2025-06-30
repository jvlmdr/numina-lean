-- https://cloud.kili-technology.com/label/projects/label/cmcbouv7300o6ueaxzuvpf263

import Mathlib

open Real

/- Let $n$ be an integer of the form $a^2 + b^2$ where $a$ and $b$ are relatively prime integers
and such that if $p$ is a prime, $p \leq \sqrt{n}$, then $p$ divides $a b$.
Determine all such $n$. -/

theorem number_theory_175773 (n : ℕ) :
    (∃ a b, a^2 + b^2 = n ∧ Nat.Coprime a b ∧ ∀ p : ℕ, p.Prime → p ≤ √n → p ∣ a * b) ↔
    n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 13 := by
  -- constructor
  -- swap
  -- · revert n
  --   simp only [forall_eq_or_imp, forall_eq]
  --   split_ands
  --   · use 1, 1
  --     simp
  --     sorry
  --   · sorry
  --   · sorry


  -- have (p : ℕ) : p ≤ √n ↔ p ^ 2 ≤ 1 := by
  --   sorry

  -- TODO: split the 1 case from the 2, 5, 13 (prime) cases?

  by_cases hn_prime : n.Prime
  · sorry

  · -- TODO: Since `n` is composite...
    -- TODO: First eliminate the cases `n = 0` and `n = 1` (not prime or composite).
    cases le_or_lt n 1 with
    | inl hn =>
      interval_cases n
      · simp
      · suffices ∃ a b, a ^ 2 + b ^ 2 = 1 ∧ a.Coprime b ∧
            ∀ (p : ℕ), p.Prime → p ≤ 1 → p ∣ a * b by simpa
        use 0, 1
        simp
    | inr hn =>
      suffices ¬∃ a b, a ^ 2 + b ^ 2 = n ∧ a.Coprime b ∧
          ∀ (p : ℕ), Nat.Prime p → p ≤ √n → p ∣ a * b by
        simp only [this, false_iff]
        rw [not_or]
        split_ands
        · linarith
        · suffices ∀ n, n = 2 ∨ n = 5 ∨ n = 13 → n.Prime from mt (this n) hn_prime
          norm_num

      suffices ∀ a b, a ^ 2 + b ^ 2 = n → a.Coprime b →
          ¬∀ (p : ℕ), p.Prime → p ≤ √n → p ∣ a * b by simpa

      intro a b hab h_coprime
      contrapose! h_coprime with h_dvd
      let p := n.minFac
      have hp_prime : p.Prime := Nat.minFac_prime (by linarith)
      -- have hp_sq_le := Nat.minFac_sq_le_self (by linarith) hn_prime
      specialize h_dvd p hp_prime (by
        refine le_sqrt_of_sq_le ?_
        suffices ↑(n.minFac ^ 2) ≤ (n : ℝ) by simpa
        rw [Nat.cast_le]
        exact Nat.minFac_sq_le_self (by linarith) hn_prime)

      suffices p ∣ a ∧ p ∣ b from Nat.not_coprime_of_dvd_of_dvd hp_prime.one_lt this.1 this.2
      rw [hp_prime.dvd_mul] at h_dvd
      -- TODO: Can we use symmetry to avoid replication here?
      refine h_dvd.elim ?_ ?_
      · refine fun ha ↦ ⟨ha, ?_⟩
        suffices p ∣ b ^ 2 from hp_prime.dvd_of_dvd_pow this
        suffices p ∣ a ^ 2 + b ^ 2 by
          refine (Nat.dvd_add_iff_right ?_).mpr this
          exact dvd_pow ha two_ne_zero
        rw [hab]
        exact Nat.minFac_dvd n
      · refine fun hb ↦ ⟨?_, hb⟩
        suffices p ∣ a ^ 2 from hp_prime.dvd_of_dvd_pow this
        suffices p ∣ a ^ 2 + b ^ 2 by
          refine (Nat.dvd_add_iff_left ?_).mpr this
          exact dvd_pow hb two_ne_zero
        rw [hab]
        exact Nat.minFac_dvd n


  -- constructor
  -- · intro ⟨a, b, hn, h_coprime, h_dvd⟩
  --   -- By symmetry, we can assume `a ≤ b`.
  --   wlog hba : b ≤ a generalizing a b
  --   · refine this b a ?_ h_coprime.symm ?_ (le_of_not_ge hba)
  --     · simpa [add_comm (b ^ 2)]
  --     · simpa [mul_comm b]
  --   sorry
  -- sorry
