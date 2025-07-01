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
        · refine .inr ?_
          cases lt_or_le a 3 with
          | inl ha =>
            interval_cases a
            · suffices n = 1 from False.elim (Nat.not_prime_one (this ▸ hn_prime))
              simpa
            · exact .inl (by simpa)
            · exact .inr (by simpa)
          | inr ha =>
            -- TODO: the hard part
            exfalso

            -- First establish that `(a + 2) ^ 2 ≤ n`.
            have h_add_two : a ^ 2 + (a + 1) ^ 2 = (a - 3) * (a + 1) + (a + 2) ^ 2 := by
              suffices (a ^ 2 + (a + 1) ^ 2 : ℤ) = (a - 3) * (a + 1) + (a + 2) ^ 2 by
                rw [← Int.ofNat_inj]
                simpa [Nat.cast_sub ha]
              ring

            let p := (a + 2).minFac
            have hp_prime : p.Prime := Nat.minFac_prime (by simp)

            have h_dvd' := h_dvd p
              (by
                calc _
                _ ≤ (a + 2) ^ 2 := by
                  refine Nat.pow_le_pow_left ?_ 2
                  exact Nat.minFac_le (by simp)
                _ ≤ _ := by simp [h_add, h_add_two])
              hp_prime

            rw [Nat.Coprime.dvd_mul_right] at h_dvd'
            swap
            · refine Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd (a + 2)) ?_
              change (a + 1 + 1).Coprime (a + 1)
              simp

            suffices h_gcd : (a + 2).Coprime a by
              change (a + 2).gcd a = 1 at h_gcd
              refine hp_prime.two_le.not_lt ?_
              suffices p = 1 by simp [this]
              suffices p ∣ (a + 2).gcd a by simpa [h_gcd]
              refine Nat.dvd_gcd ?_ ?_
              · exact Nat.minFac_dvd (a + 2)
              · exact h_dvd'  -- TDOO: expand here?

            suffices Odd a by simpa
            suffices Even (a - 1) by
              convert this.add_one
              suffices 1 ≤ a by simp [this]
              linarith

            -- It suffices to show that any prime factors must be 2.
            suffices ∀ p : ℕ, p.Prime → p ∣ a - 1 → p = 2 by
              suffices 2 ∈ (a - 1).primeFactors by
                rw [even_iff_two_dvd]
                exact Nat.dvd_of_mem_primeFactors this
              suffices (a - 1).primeFactors = {2} by simp [this]
              rw [Finset.eq_singleton_iff_nonempty_unique_mem]
              split_ands
              · rw [Nat.nonempty_primeFactors, Nat.lt_sub_iff_add_lt]
                linarith
              · intro p hp
                exact this p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

            intro p hp_prime hp_dvd
            specialize h_dvd p ?_ hp_prime
            · rw [h_add]
              suffices p ≤ a from le_trans (Nat.pow_le_pow_left this 2) (by simp)
              calc _
              _ ≤ a - 1 := by
                refine Nat.le_of_dvd ?_ hp_dvd
                rw [tsub_pos_iff_lt]
                linarith
              _ ≤ a := Nat.sub_le a 1

            -- Since `a - 1` and `a` are coprime, `p` must divide `a + 1`.
            -- Therefore `p = 2`, since it must divide `(a + 1) - (a - 1)`.

            suffices p ∣ 2 from (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp this
            suffices p ∣ (a + 1) - (a - 1) by
              convert this using 1
              rw [Nat.add_sub_sub_cancel (by linarith)]
            refine Nat.dvd_sub' ?_ ?_
            · -- Use the fact that `a - 1` is coprime to `a`.
              refine Nat.Coprime.dvd_of_dvd_mul_left ?_ h_dvd
              refine Nat.Coprime.coprime_dvd_left hp_dvd ?_
              suffices (a - 1).Coprime (a - 1 + 1) by
                convert this using 1
                rw [Nat.sub_add_cancel (by linarith)]
              simp
            · exact hp_dvd  -- TODO: expand here?

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
