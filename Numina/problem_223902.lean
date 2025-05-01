-- https://cloud.kili-technology.com/label/projects/label/cma1auc2a00s5thv5rx1q8i6i

import Mathlib

open Real

/- For how many primes $p$ does there exist an integer $n$ such that
$\sqrt{p+n} + \sqrt{n}$ is an integer.
(A) does not exist.
(B) there is only one.
(C) more than one, but a finite number.
(D) there are infinitely many. -/

theorem number_theory_223902 : Set.Infinite {p : ℕ | p.Prime ∧ ∃ n m : ℕ, √(p + n) + √n = m} := by
  -- We will prove that all odd primes satisfy the condition.
  suffices {p : ℕ | p.Prime} \ {2} ⊆ {p : ℕ | p.Prime ∧ ∃ n m : ℕ, √(p + n) + √n = m} by
    refine Set.Infinite.mono this ?_
    exact Nat.infinite_setOf_prime.diff (Set.finite_singleton 2)
  intro p
  simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
  refine fun ⟨hp, h_two⟩ ↦ ⟨hp, ?_⟩
  -- All primes `p ≠ 2` are odd, hence `p = 2 k + 1`.
  rcases hp.odd_of_ne_two h_two with ⟨k, rfl⟩
  -- If we set `n = k ^ 2`, then `p + n = 2 k + 1 + k ^ 2 = (k + 1) ^ 2`.
  -- Hence `√(p + n) + √n = (k + 1) + k = 2 k + 1`.
  use k ^ 2, 2 * k + 1
  calc _
  _ = √(2 * k + 1 + k ^ 2 : ℕ) + k := by simp
  -- Factorize into `(k + 1) ^ 2` in `ℕ`.
  _ = √((k + 1) ^ 2 : ℕ) + k := by congr 3; ring
  -- Move the coercion inside the power and use `sqrt_sq`.
  _ = √((k + 1 : ℕ) ^ 2) + k := by simp
  _ = ↑(k + 1) + k := by rw [sqrt_sq (Nat.cast_nonneg' _)]
  _ = ↑(k + 1 + k) := by simp
  _ = _ := by congr 1; ring
