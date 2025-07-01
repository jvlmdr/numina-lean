-- https://cloud.kili-technology.com/label/projects/label/cmcbouv7300o6ueaxzuvpf263

import Mathlib

open Real

/- Let $n$ be an integer of the form $a^2 + b^2$ where $a$ and $b$ are relatively prime integers
and such that if $p$ is a prime, $p \leq \sqrt{n}$, then $p$ divides $a b$.
Determine all such $n$. -/

-- For a consecutive pair `a, a + 1`, we cannot have `3 ≤ a`.
lemma lemma_1 (n a : ℕ) (h_add : n = a ^ 2 + (a + 1) ^ 2)
    (h_dvd : ∀ p, p ^ 2 ≤ n → p.Prime → p ∣ a * (a + 1)) (ha : 3 ≤ a) :
    False := by
  -- First establish that `(a + 2) ^ 2 ≤ n`.
  have h_add_two : a ^ 2 + (a + 1) ^ 2 = (a - 3) * (a + 1) + (a + 2) ^ 2 := by
    suffices (a ^ 2 + (a + 1) ^ 2 : ℤ) = (a - 3) * (a + 1) + (a + 2) ^ 2 by
      rw [← Int.ofNat_inj]
      simpa [Nat.cast_sub ha]
    ring

  let p := (a + 2).minFac
  have hp_prime : p.Prime := Nat.minFac_prime (by simp)

  suffices h_gcd : (a + 2).Coprime a by
    refine hp_prime.two_le.not_lt ?_
    suffices p = 1 by simp [this]
    change (a + 2).gcd a = 1 at h_gcd
    suffices p ∣ (a + 2).gcd a by simpa [h_gcd]
    refine Nat.dvd_gcd ?_ ?_
    · exact Nat.minFac_dvd (a + 2)
    · suffices p ∣ a * (a + 1) by
        refine (Nat.Coprime.dvd_mul_right ?_).mp this
        refine Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd _) ?_
        change (a + 1 + 1).Coprime (a + 1)
        simp
      refine h_dvd p ?_ hp_prime
      calc _
      _ ≤ (a + 2) ^ 2 := by
        refine Nat.pow_le_pow_left ?_ 2
        exact Nat.minFac_le (by simp)
      _ ≤ _ := by simp [h_add, h_add_two]

  suffices Odd a by simpa
  suffices Even (a - 1) by
    convert this.add_one
    suffices 1 ≤ a by simp [this]
    linarith

  -- It suffices to show that any prime factor must be 2.
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
  -- Since `a - 1` and `a` are coprime, `p` must divide `a + 1`.
  -- Therefore `p = 2`, since it must divide `(a + 1) - (a - 1)`.
  suffices p ∣ 2 from (Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp this
  suffices p ∣ (a + 1) - (a - 1) by
    convert this using 1
    rw [Nat.add_sub_sub_cancel (by linarith)]
  refine Nat.dvd_sub' ?_ hp_dvd
  -- Use the fact that `a - 1` is coprime to `a`.
  refine Nat.Coprime.dvd_of_dvd_mul_left ?_ (h_dvd p ?_ hp_prime)
  · refine Nat.Coprime.coprime_dvd_left hp_dvd ?_
    suffices (a - 1).Coprime (a - 1 + 1) by
      convert this using 1
      rw [Nat.sub_add_cancel (by linarith)]
    simp
  · rw [h_add]
    suffices p ≤ a from le_trans (Nat.pow_le_pow_left this 2) (by simp)
    calc _
    _ ≤ a - 1 := by
      refine Nat.le_of_dvd ?_ hp_dvd
      rw [tsub_pos_iff_lt]
      linarith
    _ ≤ a := Nat.sub_le a 1

-- For a pair `a, b` with `a + 1 < b`, `n` cannot be prime.
lemma lemma_2 (n : ℕ) (a d : ℕ) (h_add : n = a ^ 2 + (a + d) ^ 2)
    (h_dvd : ∀ p, p ^ 2 ≤ n → p.Prime → p ∣ a * (a + d)) (hd : 1 < d) :
    ¬n.Prime := by
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

  refine Nat.not_prime_of_dvd_of_lt ?_ hp_prime.two_le ?_
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

-- For `n` composite, the existence of such `a, b` coprime leads to a contradiction.
lemma lemma_3 (n : ℕ) (hn : 1 < n) (hn_prime : ¬n.Prime) (a b : ℕ) (h_add : n = a ^ 2 + b ^ 2)
    (h_dvd : ∀ p, p ^ 2 ≤ n → p.Prime → p ∣ a * b) :
    ¬a.Coprime b := by
  let p := n.minFac
  have hp_prime : p.Prime := Nat.minFac_prime (by linarith)
  specialize h_dvd p (Nat.minFac_sq_le_self (by linarith) hn_prime) hp_prime
  rw [hp_prime.dvd_mul] at h_dvd
  suffices p ∣ a ∧ p ∣ b from Nat.not_coprime_of_dvd_of_dvd hp_prime.one_lt this.1 this.2
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
    -- First consider whether `n` is prime, composite, or below two.
    by_cases hn_prime : n.Prime
    · -- Since `n` is prime, we can exclude the `n = 1` solution.
      refine .inr ?_
      -- Introduce the assumption that `a ≤ b` via symmetry.
      wlog hab : a ≤ b generalizing a b
      · refine this b a h_coprime.symm ?_ ?_ (le_of_not_ge hab)
        · simpa [add_comm]
        · simpa [mul_comm]
      -- Replace `b` with `a + d`.
      obtain ⟨d, rfl⟩ : ∃ d, b = a + d := Nat.exists_eq_add_of_le hab
      rw [Nat.coprime_self_add_right] at h_coprime

      -- Consider the cases `b = a`, `b = a + 1`, and `b ≥ a + 2`.
      cases le_or_lt d 1 with
      | inl hd =>
        interval_cases d
        · -- When `b = a`, we have `a = 1` from `a.Coprime a`. This implies `n = 2`.
          have ha : a = 1 := by simpa using h_coprime
          have hn : n = 2 := by simpa [ha] using h_add
          exact .inl hn
        · -- Consider the cases `a = 0, 1, 2` and `a ≥ 3`.
          cases lt_or_le a 3 with
          | inl ha =>
            interval_cases a
            · -- For `a = 0, b = 1`, we obtain `n = 1`, which contradicts `n.Prime`.
              suffices n = 1 from False.elim (Nat.not_prime_one (this ▸ hn_prime))
              simpa
            · -- For `a = 1, b = 2`, we obtain `n = 5`, which is a valid solution.
              suffices n = 5 by simp [this]
              simpa
            · -- For `a = 2, b = 3`, we obtain `n = 13`, which is a valid solution.
              suffices n = 13 by simp [this]
              simpa
          | inr ha =>
            -- Show that there exists a contradiction.
            exfalso
            exact lemma_1 n a h_add h_dvd ha

      | inr hd =>
        exfalso
        -- This contradicts the assumption that `n` is prime.
        exact lemma_2 n a d h_add h_dvd hd hn_prime

    · refine .inl ?_
      cases le_or_lt n 1 with
      | inl hn =>
        interval_cases n
        · -- Find a contradiction in that `a = b = 0`, hence their gcd is 0, not 1.
          exfalso
          obtain ⟨ha, hb⟩ : a = 0 ∧ b = 0 := by simpa using Nat.add_eq_zero.mp h_add.symm
          simp [ha, hb] at h_coprime
        · rfl
      | inr hn =>
        exfalso
        exact lemma_3 n hn hn_prime a b h_add h_dvd h_coprime

  · -- Substitute the different solutions `n` and provide `a, b` for each.
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
