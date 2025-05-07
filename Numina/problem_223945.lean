-- https://cloud.kili-technology.com/label/projects/review/cma3ygf29006kahay88o5hmwg

import Mathlib

/- Prove that for any natural $n \geqslant 2$ the number $2^{4 n+2} + 1$ is
not the product of two prime numbers. -/

theorem number_theory_223945 (n : ℕ) (hn : 2 ≤ n) :
    ¬∃ p q, 2 ^ (4 * n + 2) + 1 = p * q ∧ p.Prime ∧ q.Prime := by

  suffices ∃ a b, 2 ^ (4 * n + 2) + 1 = a * b ∧ ∃ c d, 2 ^ (4 * n + 2) + 1 = c * d ∧
      ({a, b} : Multiset ℕ) ≠ {c, d} by
    simp only [not_exists]
    intro p q
    rcases this with ⟨a, b, hab, c, d, hcd, h⟩
    refine mt (fun ⟨hpq, hp, hq⟩ ↦ ?_) h
    generalize 2 ^ (4 * n + 2) + 1 = x at hpq hab hcd
    rcases hpq with rfl

    -- calc _
    -- _ = ((a * b).primeFactorsList : Multiset ℕ) := by sorry
    -- _ = (x.primeFactorsList : Multiset ℕ) := by rw [hab]
    -- _ = ((c * d).primeFactorsList : Multiset ℕ) := by rw [hcd]
    -- _ = _ := by sorry

    have := congrArg Nat.factorization hab
    rw [Nat.factorization_mul hp.ne_zero hq.ne_zero] at this
    rw [hp.factorization, hq.factorization] at this

    -- Check that it is convenient to prove {a, b} ≠ {c, d} before proceeding!
    sorry

  use 2 ^ (2 * n + 1) + 2 ^ (n + 1) + 1, 2 ^ (2 * n + 1) - 2 ^ (n + 1) + 1
  refine ⟨?_, ?_⟩
  · symm  -- TODO: eliminate?
    -- Switch to `ℤ` to use `ring` without worrying about negatives.
    refine (Nat.cast_inj (R := ℤ)).mp ?_
    simp only [Nat.cast_mul, Nat.cast_add]
    rw [Nat.cast_sub]
    swap
    · refine Nat.pow_le_pow_right two_pos ?_
      linarith
    simp only [Nat.cast_pow]
    ring

  -- Use the series `2^(4 n) - 2^(4 n - 2) + 2^(4 n - 4) - ... + 2^4 - 2^2 + 1`.
  -- Split the sum into positive and negative sums while working in `ℕ`.
  use 2 ^ 2 + 1, ∑ i in Finset.range (n + 1), 2 ^ (4 * i) - ∑ i in Finset.range n, 2 ^ (4 * i + 2)
  refine ⟨?_, ?_⟩
  · symm  -- TODO: eliminate?
    calc _
    _ = 2 ^ 2 * ∑ i ∈ Finset.range (n + 1), 2 ^ (4 * i)
        + ∑ i ∈ Finset.range (n + 1), 2 ^ (4 * i)
        - 2 ^ 2 * ∑ i ∈ Finset.range n, 2 ^ (4 * i + 2)
        - ∑ i ∈ Finset.range n, 2 ^ (4 * i + 2) := by
      simp only [mul_tsub, add_mul]
      simp [Nat.sub_add_eq]

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

    _ = 4 * (2 ^ (4 * n) + ∑ i ∈ Finset.range n, 2 ^ (4 * i))
        + (1 + ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1)))
        - ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1))
        - 4 * ∑ i ∈ Finset.range n, 2 ^ (4 * i) := by
      congr
      · rw [Finset.sum_range_succ]
        ring
      · rw [Finset.sum_range_succ']
        ring

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

  simp only [Nat.reducePow, Nat.reduceAdd]
  suffices 5 ∉
      ({2 ^ (2 * n + 1) + 2 ^ (n + 1) + 1, 2 ^ (2 * n + 1) - 2 ^ (n + 1) + 1} : Multiset ℕ) by
    refine mt (fun h ↦ ?_) this
    simp [h]

  suffices 5 ≠ 2 ^ (2 * n + 1) + 2 ^ (n + 1) + 1 ∧ 5 ≠ 2 ^ (2 * n + 1) - 2 ^ (n + 1) + 1 by
    simpa using this

  refine ⟨?_, ?_⟩
  · refine ne_of_lt ?_
    calc _
    _ < 2 ^ (2 * 2 + 1) + 2 ^ (2 + 1) + 1 := by norm_num
    _ ≤ _ := by
      suffices Monotone (fun x ↦ 2 ^ (2 * x + 1) + 2 ^ (x + 1) + 1) from this hn
      refine .add_const (.add ?_ ?_) 1
      · refine fun x y hxy ↦ Nat.pow_le_pow_of_le one_lt_two ?_
        simpa using hxy
      · refine fun x y hxy ↦ Nat.pow_le_pow_of_le one_lt_two ?_
        simpa using hxy
  · refine ne_of_lt ?_
    calc _
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
