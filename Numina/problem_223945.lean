-- https://cloud.kili-technology.com/label/projects/review/cma3ygf29006kahay88o5hmwg

import Mathlib

/- Prove that for any natural $n \geqslant 2$ the number $2^{4 n+2} + 1$ is
not the product of two prime numbers. -/

theorem number_theory_223945 (n : ℕ) (hn : 2 ≤ n) :
    ¬∃ p q, 2 ^ (4 * n + 2) + 1 = p * q ∧ p.Prime ∧ q.Prime := by
  -- To simplify notation, let `m` be the number of interest.
  generalize hm : 2 ^ (4 * n + 2) + 1 = m
  -- It will suffice to find two distinct (non-trivial) factorizations of `m`.
  -- First, replace the existence of `p, q` by the number of factors being equal to 2.
  suffices m.primeFactorsList.length ≠ 2 by
    contrapose! this
    rcases this with ⟨p, q, rfl, hp, hq⟩
    calc _
    _ = p.primeFactorsList.length + q.primeFactorsList.length := by
      have := Nat.perm_primeFactorsList_mul hp.ne_zero hq.ne_zero
      simp [this.length_eq]
    _ = 2 := by simp [Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hq]
  -- Replace this with the existence of two factorizations.
  suffices ∃ a b, a ≠ 1 ∧ b ≠ 1 ∧ a * b = m ∧ ∃ c d, c ≠ 1 ∧ d ≠ 1 ∧ c * d = m ∧
      ¬[a, b].Perm [c, d] by
    intro h_len
    revert this
    -- We need a theorem for the uniqueness of the prime factorization based on its length.
    suffices ∀ u v, u ≠ 1 → v ≠ 1 → u * v = m → [u, v].Perm m.primeFactorsList by
      intro ⟨a, b, ha, hb, hab, c, d, hc, hd, hcd, h⟩
      exact h <| .trans (this a b ha hb hab) (this c d hc hd hcd).symm
    rintro a b ha hb rfl
    -- It will suffice to show that `a` and `b` are prime.
    suffices a.Prime ∧ b.Prime by
      refine Nat.primeFactorsList_unique ?_ ?_
      · simp
      · simpa using this
    -- Now use the fact that `a` and `b` have non-empty factoriations
    -- and their product has a factorization of length 2.
    suffices a.primeFactorsList.length = 1 ∧ b.primeFactorsList.length = 1 by
      revert this
      suffices ∀ n : ℕ, n.primeFactorsList.length = 1 → n.Prime from And.imp (this a) (this b)
      intro n
      rw [List.length_eq_one]
      refine forall_exists_index.mpr fun p h ↦ ?_
      have hn : n = p := by
        convert congrArg List.prod h
        · refine (Nat.prod_primeFactorsList fun hn ↦ ?_).symm
          simp [hn] at h
        · simp
      have hp : p.Prime := by
        suffices p ∈ n.primeFactorsList from Nat.prime_of_mem_primeFactorsList this
        simp [h]
      exact hn ▸ hp
    -- We further know that `a` and `b` are non-zero since their product is non-zero.
    -- This will be used to obtain the lengths of factorizations.
    have ⟨ha₀, hb₀⟩ : a ≠ 0 ∧ b ≠ 0 := by
      suffices a * b ≠ 0 by simpa using this
      simp [← hm]
    have ha_len : 0 < a.primeFactorsList.length := by simpa [Nat.pos_iff_ne_zero] using ⟨ha₀, ha⟩
    have hb_len : 0 < b.primeFactorsList.length := by simpa [Nat.pos_iff_ne_zero] using ⟨hb₀, hb⟩
    -- From `u + v = 2` and `0 < u, v`, we obtain `u = v = 1`.
    suffices a.primeFactorsList.length + b.primeFactorsList.length = 2 by constructor <;> linarith
    convert h_len
    simpa using (Nat.perm_primeFactorsList_mul ha₀ hb₀).length_eq.symm

  -- Establish the first factorization.
  let a : ℕ := 2 ^ (2 * n + 1) + 2 ^ (n + 1) + 1
  let b : ℕ := 2 ^ (2 * n + 1) - 2 ^ (n + 1) + 1
  have hab : a * b = 2 ^ (4 * n + 2) + 1 := by
    unfold a b
    -- Switch to `ℤ` to use `ring` without worrying about negatives.
    refine (Nat.cast_inj (R := ℤ)).mp ?_
    simp only [Nat.cast_mul, Nat.cast_add]
    rw [Nat.cast_sub]
    swap
    · refine Nat.pow_le_pow_right two_pos ?_
      linarith
    simp only [Nat.cast_pow]
    ring

  use a, b
  refine ⟨?_, ?_, hab.trans hm, ?_⟩
  -- Show that the factorization is non-trivial (neither factor is 1).
  · unfold a
    simp
  · unfold b
    suffices 2 ^ (n + 1) < 2 ^ (2 * n + 1) by simpa [Nat.sub_eq_zero_iff_le] using this
    refine Nat.pow_lt_pow_of_lt one_lt_two ?_
    linarith

  -- Establish the second factorization.
  -- Use the series `2^(4 n) - 2^(4 n - 2) + 2^(4 n - 4) - ... + 2^4 - 2^2 + 1`.
  -- Split into positive and negative sums.
  let c := 2 ^ 2 + 1
  let d := ∑ i in Finset.range (n + 1), 2 ^ (4 * i) - ∑ i in Finset.range n, 2 ^ (4 * i + 2)
  have hcd : c * d = 2 ^ (4 * n + 2) + 1 := by
    unfold c d
    calc _
    -- Expand the product and the truncated subtraction.
    _ = 4 * ∑ i ∈ Finset.range (n + 1), 2 ^ (4 * i)
        + ∑ i ∈ Finset.range (n + 1), 2 ^ (4 * i)
        - 4 * ∑ i ∈ Finset.range n, 2 ^ (4 * i + 2)
        - ∑ i ∈ Finset.range n, 2 ^ (4 * i + 2) := by
      simp only [mul_tsub, add_mul]
      simp [Nat.sub_add_eq]
    -- Move the constant factors around so that the summands resemble each other.
    _ = 4 * ∑ i ∈ Finset.range (n + 1), 2 ^ (4 * i)
        + ∑ i ∈ Finset.range (n + 1), 2 ^ (4 * i)
        - ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1))
        - 4 * ∑ i ∈ Finset.range n, 2 ^ (4 * i) := by
      simp only [Finset.mul_sum]
      congr
      · funext i
        ring
      · funext i
        ring
    -- Split the first and last term from the first two sums.
    _ = 4 * (2 ^ (4 * n) + ∑ i ∈ Finset.range n, 2 ^ (4 * i))
        + (1 + ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1)))
        - ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1))
        - 4 * ∑ i ∈ Finset.range n, 2 ^ (4 * i) := by
      congr
      · rw [Finset.sum_range_succ]
        ring
      · rw [Finset.sum_range_succ']
        ring
    -- Re-order the terms for cancellation.
    _ = 4 * 2 ^ (4 * n) + 1 +
        4 * ∑ i ∈ Finset.range n, 2 ^ (4 * i)
        + ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1))
        - ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1))
        - 4 * ∑ i ∈ Finset.range n, 2 ^ (4 * i) := by
      congr 2
      ring
    _ = _ := by
      simp only [Nat.add_sub_cancel_right]
      ring

  use c, d
  -- Show that the factorization is non-trivial (neither factor is 1).
  refine ⟨?_, ?_, hcd.trans hm, ?_⟩
  · norm_num
  · unfold d
    refine ne_of_gt ?_
    refine Nat.lt_sub_iff_add_lt'.mpr ?_
    rw [Finset.sum_range_succ']
    simp only [mul_zero, pow_zero, add_lt_add_iff_right]
    refine Finset.sum_lt_sum_of_nonempty ?_ ?_
    · suffices n ≠ 0 by simpa using this
      exact Nat.not_eq_zero_of_lt hn
    · intro i _
      refine Nat.pow_lt_pow_of_lt one_lt_two ?_
      simp [mul_add]

  -- Finally, show that the simplest factor `2 ^ 2 + 1 = 5` does not appear in the other list.
  suffices c ∉ [a, b] by
    refine mt (fun h_perm ↦ ?_) this
    refine h_perm.mem_iff.mpr ?_
    simp
  suffices c ≠ a ∧ c ≠ b by simpa using this
    -- Use the monotonicity of `2^(2 n + 1) - 2^(n + 1) + 1` and `2 ≤ n`.
  suffices c < b ∧ b ≤ a from ⟨(this.1.trans_le this.2).ne, this.1.ne⟩
  refine ⟨?_, ?_⟩
  · unfold b c
    calc _
    -- By monotonicity, it is sufficient to show true for `n = 2`.
    _ < 2 ^ (2 + 1) * (2 ^ 2 - 1) + 1 := by norm_num
    _ ≤ 2 ^ (n + 1) * (2 ^ n - 1) + 1 := by
      suffices Monotone (fun x ↦ 2 ^ (x + 1) * (2 ^ x - 1) + 1) from this hn
      refine .add_const (.mul' ?_ ?_) 1
      · refine fun x y hxy ↦ Nat.pow_le_pow_of_le one_lt_two ?_
        simpa using hxy
      · refine fun x y hxy ↦ Nat.sub_le_sub_right ?_ 1
        exact Nat.pow_le_pow_of_le one_lt_two hxy
    _ = _ := by
      rw [mul_tsub]
      congr 2 <;> ring
  · unfold a b
    gcongr
    exact (Nat.sub_le _ _).trans (Nat.le_add_right _ _)
