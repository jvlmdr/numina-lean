import Mathlib

/- For $n$ a positive integer, let $R(n)$ be the sum of the remainders when $n$ is divided by
$2$, $3$, $4$, $5$, $6$, $7$, $8$, $9$, and $10$.
For example, $R(15) = 1 + 0 + 3 + 0 + 3 + 1 + 7 + 6 + 5 = 26$.
How many two-digit positive integers $n$ satisfy $R(n) = R(n+1)$?
(A) 0, (B) 1, (C) 2, (D) 3, (E) 4 -/

theorem number_theory_94998 (r : ℕ → ℕ)
    (hr : ∀ n, r n = ∑ k in Finset.Icc 2 10, n % k) :
    {n ∈ Finset.Icc 10 99 | r n = r (n + 1)}.card = 2 := by
  -- We could obtain this proof directly using `decide`.
  -- However, we prefer to obtain a proof that provides some insight into the problem.

  -- Note that we can add $9$ to $R(n)$ to get $R(n + 1)$, but must subtract $k$ for all $k|n+1$.
  have h_succ (n) : r (n + 1) + ∑ k in .Icc 2 10, (if k ∣ n + 1 then k else 0) = r n + 9 :=
    calc _
    _ = ∑ k ∈ Finset.Icc 2 10, ((n + 1) % k + if k ∣ n + 1 then k else 0) := by
      simp [hr, Finset.sum_add_distrib.symm]
    _ = ∑ k ∈ Finset.Icc 2 10, (n % k + 1) := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      -- Rewrite the modulo using division in order to use `Nat.succ_div`, which is
      -- defined in the terms we desire, `if k ∣ n + 1`.
      have hk_mod := Nat.mod_add_div n k
      have hk_mod_succ := Nat.mod_add_div (n + 1) k
      have := Eq.trans hk_mod_succ (congrArg (· + 1) hk_mod).symm
      rw [Nat.succ_div] at this
      simp only [mul_add, mul_ite, mul_one, mul_zero] at this
      refine (Nat.add_right_inj (n := k * (n / k))).mp ?_
      convert this using 1 <;> abel
    _ = _ := by simp [hr, Finset.sum_add_distrib]

  have h_succ' (n) : r n = r (n + 1) ↔ (∑ k in .Icc 2 10, if k ∣ n + 1 then k else 0) = 9 :=
    calc _
    _ ↔ r (n + 1) + ∑ k in .Icc 2 10, (if k ∣ n + 1 then k else 0) = r (n + 1) + 9 := by
      rw [h_succ, Nat.add_left_inj]
    _ ↔ _ := by
      rw [Nat.add_right_inj]
  simp only [h_succ'] -- TODO: Suffices?


  sorry
