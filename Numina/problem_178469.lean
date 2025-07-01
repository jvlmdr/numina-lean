-- https://cloud.kili-technology.com/label/projects/label/cmcbouv7300o6ueaxzuvpf263

import Mathlib

open Real

/- Let $n$ be an integer of the form $a^2 + b^2$ where $a$ and $b$ are relatively prime integers
and such that if $p$ is a prime, $p \leq \sqrt{n}$, then $p$ divides $a b$.
Determine all such $n$. -/

-- The real inequality `p ≤ √n` is equivalent to inequality in the naturals `p ^ 2 ≤ n`.
lemma coe_le_sqrt_coe_iff (p n : ℕ) : p ≤ √n ↔ p ^ 2 ≤ n :=
  calc _
  _ ↔ ↑(p ^ 2) ≤ (n : ℝ) := by simp [le_sqrt]
  _ ↔ _ := Nat.cast_le

-- For `3 ≤ a`, we can rewrite `a ^ 2 + (a + 1) ^ 2` in terms of `(a + 2) ^ 2`.
lemma sq_add_sq_succ_of_three_le (a : ℕ) (ha : 3 ≤ a) :
    a ^ 2 + (a + 1) ^ 2 = (a - 3) * (a + 1) + (a + 2) ^ 2 := by
  -- Prove in `ℤ` where we can use `ring`.
  suffices (a ^ 2 + (a + 1) ^ 2 : ℤ) = (a - 3) * (a + 1) + (a + 2) ^ 2 by
    rw [← Int.ofNat_inj]
    simpa [Nat.cast_sub ha]
  ring

-- For a consecutive pair `a, a + 1` with `3 ≤ a`, we can show that `a - 1` is even.
theorem lemma_1 (n a : ℕ) (h_add : n = a ^ 2 + (a + 1) ^ 2)
    (h_dvd : ∀ (p : ℕ), p ^ 2 ≤ n → Nat.Prime p → p ∣ a * (a + 1)) (ha : 3 ≤ a) :
    Even (a - 1) := by
  -- It suffices to show that all prime factors are 2 (and `a - 1` is at least 2).
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
  specialize h_dvd p ?_ hp_prime
  · rw [h_add]
    suffices p ≤ a from le_trans (Nat.pow_le_pow_left this 2) (by simp)
    calc _
    _ ≤ a - 1 := by
      refine Nat.le_of_dvd ?_ hp_dvd
      rw [tsub_pos_iff_lt]
      linarith
    _ ≤ a := Nat.sub_le a 1
  suffices (a - 1).Coprime a from (this.coprime_dvd_left hp_dvd).dvd_of_dvd_mul_left h_dvd
  suffices (a - 1).Coprime (a - 1 + 1) by
    convert this
    rw [Nat.sub_add_cancel (by linarith)]
  simp

-- For a consecutive pair `a, a + 1` to satisfy the condition, we must have `a < 3`.
lemma lemma_2 (n a : ℕ) (h_add : n = a ^ 2 + (a + 1) ^ 2)
    (h_dvd : ∀ p, p ^ 2 ≤ n → p.Prime → p ∣ a * (a + 1)) : a < 3 := by
  suffices ¬3 ≤ a by simpa
  intro ha
  -- We will consider the prime factors of adjacent numbers `a - 1` and `a + 2`.
  -- Since we have `a + 2 ≤ n ^ 2`, the divisibility condition holds for all prime factors.
  -- Take any prime factor of `a + 2`.
  let p := (a + 2).minFac
  have hp_prime : p.Prime := Nat.minFac_prime (by simp)
  have hp_dvd : p ∣ a + 2 := Nat.minFac_dvd (a + 2)
  -- This prime factor `p ∣ a + 2` must divide `a` or `a + 1`.
  -- However, `a + 1` is coprime to `a + 2`, hence it must divide `a`.
  have hp : p ∣ a * (a + 1) := by
    refine h_dvd p ?_ hp_prime
    calc _
    _ ≤ (a + 2) ^ 2 := by
      refine Nat.pow_le_pow_left ?_ 2
      exact Nat.minFac_le (by simp)
    _ ≤ _ := by simp [h_add, sq_add_sq_succ_of_three_le _ ha]
  have hpa : p ∣ a := by
    have : (a + 1 + 1).Coprime (a + 1) := by simp
    exact (this.coprime_dvd_left hp_dvd).dvd_of_dvd_mul_right hp
  -- It will suffice to show that `a + 2` is also coprime to `a`.
  suffices p = 1 from Nat.not_prime_one (this ▸ hp_prime)
  suffices (a + 2).Coprime a by simpa [this.gcd_eq_one] using Nat.dvd_gcd hp_dvd hpa
  -- This is equivalent to `a` being coprime to 2, hence `a` being odd.
  suffices Odd a by simpa
  -- To establish this, we show that `a - 1` is even.
  -- This follows from `a - 1` and `a` being coprime.
  suffices Even (a - 1) by
    convert this.add_one
    suffices 1 ≤ a by simp [this]
    linarith
  exact lemma_1 n a h_add h_dvd ha

-- For a pair `a, b` with `a + 1 < b`, `n` cannot be prime.
lemma lemma_3 (n : ℕ) (hn_prime : n.Prime) (a d : ℕ) (h_add : n = a ^ 2 + (a + d) ^ 2)
    (h_dvd : ∀ p, p ^ 2 ≤ n → p.Prime → p ∣ a * (a + d)) : d ≤ 1 := by
  suffices ¬1 < d by simpa
  intro hd
  -- For `1 < d`, we can obtain a prime factor `p`.
  let p := d.minFac
  have hp_prime : p.Prime := Nat.minFac_prime hd.ne'
  -- Rewrite `a ^ 2 + b ^ 2` as `(a - b) ^ 2 + 2 * a * b` with `a - b = d`,
  -- then show that `p` divides both terms and is less than `n`.
  have hp_le : p ^ 2 ≤ n :=
    calc _
    _ ≤ d ^ 2 := by
      refine Nat.pow_le_pow_left ?_ 2
      exact Nat.minFac_le (by linarith)
    _ ≤ (a + d) ^ 2 := Nat.pow_le_pow_left (by simp) 2
    _ ≤ _ := by simp [h_add]
  refine Nat.not_prime_of_dvd_of_lt ?_ hp_prime.two_le ?_ hn_prime
  · rw [h_add]
    suffices p ∣ d ^ 2 + 2 * (a * (a + d)) by
      convert this using 1
      ring
    refine dvd_add ?_ ?_
    · exact dvd_pow d.minFac_dvd two_ne_zero
    · exact (h_dvd p hp_le hp_prime).mul_left 2
  · refine lt_of_lt_of_le ?_ hp_le
    exact lt_self_pow₀ hp_prime.one_lt one_lt_two

-- For `n` composite, the existence of such `a, b` coprime leads to a contradiction.
lemma lemma_4 (n : ℕ) (hn : 1 < n) (hn_prime : ¬n.Prime) (a b : ℕ) (h_add : n = a ^ 2 + b ^ 2)
    (h_dvd : ∀ p, p ^ 2 ≤ n → p.Prime → p ∣ a * b) :
    ¬a.Coprime b := by
  -- For `n` not prime, we can obtain some prime factor `p` less than or equal to `√n`.
  let p := n.minFac
  have hp_prime : p.Prime := Nat.minFac_prime (by linarith)
  specialize h_dvd p (Nat.minFac_sq_le_self (by linarith) hn_prime) hp_prime
  rw [hp_prime.dvd_mul] at h_dvd
  -- Since `p` divides one of `a` or `b` as well as `n = a^2 + b^2`,
  -- it must divide both `a` and `b`, providing a contradiction.
  suffices p ∣ a ∧ p ∣ b from Nat.not_coprime_of_dvd_of_dvd hp_prime.one_lt this.1 this.2
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
  simp only [coe_le_sqrt_coe_iff]

  constructor
  · intro ⟨a, b, h_coprime, h_add, h_dvd⟩
    -- First consider whether `n` is prime, composite, or below two.
    by_cases hn_prime : n.Prime
    · -- Since `n` is prime, we can exclude the `n = 1` solution.
      refine .inr ?_
      -- Introduce the assumption that `a ≤ b` via symmetry, then replace `b = a + d`.
      wlog hab : a ≤ b generalizing a b
      · refine this b a h_coprime.symm ?_ ?_ (le_of_not_ge hab)
        · simpa [add_comm]
        · simpa [mul_comm]
      obtain ⟨d, rfl⟩ : ∃ d, b = a + d := Nat.exists_eq_add_of_le hab
      rw [Nat.coprime_self_add_right] at h_coprime
      -- Only need to consider the cases `d ∈ {0, 1}`.
      have hd : d ≤ 1 := lemma_3 n hn_prime a d h_add h_dvd
      interval_cases d
      · -- When `b = a`, we have `a = 1` from `a.Coprime a`. This implies `n = 2`.
        have ha : a = 1 := by simpa using h_coprime
        have hn : n = 2 := by simpa [ha] using h_add
        exact .inl hn
      · -- Only need to consider the cases `a ∈ {0, 1, 2}`.
        have ha : a < 3 := lemma_2 n a h_add h_dvd
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
    · -- Since `n` is not prime, we only consider the `n = 1` case.
      refine .inl ?_
      -- Split based on whether `n` is composite or simply less than 2.
      cases le_or_lt n 1 with
      | inl hn =>
        interval_cases n
        · -- Find a contradiction in that `a = b = 0`, hence their gcd is 0, not 1.
          exfalso
          obtain ⟨ha, hb⟩ : a = 0 ∧ b = 0 := by simpa using Nat.add_eq_zero.mp h_add.symm
          simp [ha, hb] at h_coprime
        · rfl
      | inr hn =>
        -- Use the contradiction for `n` composite.
        exfalso
        exact lemma_4 n hn hn_prime a b h_add h_dvd h_coprime

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
