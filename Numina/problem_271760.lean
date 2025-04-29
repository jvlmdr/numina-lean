-- https://cloud.kili-technology.com/label/projects/label/cma1au4rj00gwthv5baygjspl

import Mathlib

/- Prove that if you select four consecutive terms $a_{n-1}, a_{n}, a_{n+1}, a_{n+2}$
in the Fibonacci sequence and subtract the product of the middle terms $a_{n} a_{n+1}$
from the product of the outer terms $a_{n-1} a_{n+2}$, the result will be 1 or -1.
Prove that for any Fibonacci sequence, the absolute value of the expression
$u_{n-1} u_{n+2} - u_{n} u_{n+1}$ does not depend on $n$. -/

theorem number_theory_271760 {u : ℕ → ℝ}
    (hu : ∀ n, u (n + 2) = u n + u (n + 1)) :
    (∃ c, ∀ n, |u n * u (n + 3) - u (n + 1) * u (n + 2)| = c) ∧
    (u 0 = 0 → u 1 = 1 → ∀ n, u n * u (n + 3) - u (n + 1) * u (n + 2) ∈ ({1, -1} : Set _)) := by
  -- Give the expression of interest a name to simplify notation.
  let d (n : ℕ) : ℝ := u n * u (n + 3) - u (n + 1) * u (n + 2)
  suffices (∃ c, ∀ n, |d n| = c) ∧ (u 0 = 0 → u 1 = 1 → ∀ n, d n = 1 ∨ d n = -1) by
    simpa [d] using this
  -- Use the definition of the Fibonacci sequence to rewrite the expression.
  have hd (n) : d n = u n * u (n + 2) - u (n + 1) ^ 2 := by
    unfold d
    calc _
    _ = u n * u (n + 1) + u n * u (n + 2) - u (n + 1) * u (n + 2) := by simp [hu, mul_add]
    _ = u n * u (n + 2) - (u (n + 2) - u n) * u (n + 1) := by ring
    _ = _ := by rw [sq, sub_eq_of_eq_add' (hu n)]

  -- It will suffice to show that `d (n + 1) = -d n`.
  suffices ∀ n, d (n + 1) = -d n by
    refine ⟨?_, ?_⟩
    -- Use induction to show that there exists a constant equal to the absolute value.
    · use |d 0|
      intro n
      induction n with
      | zero => rfl
      | succ n IH => rw [this, abs_neg, IH]
    -- Use induction to show that the constant is 1 for the classical Fibonacci sequence.
    · intro h₀ h₁ n
      induction n with
      | zero => simp [d, hu, h₀, h₁]
      | succ n IH =>
        rw [this]
        refine IH.symm.imp (fun h ↦ ?_) fun h ↦ ?_
        · rw [h, neg_neg]
        · rw [h]

  intro n
  simp only [hd]
  calc u (n + 1) * u (n + 3) - u (n + 2) ^ 2
  -- Rewrite the two larger terms using the recursive definition.
  _ = u (n + 1) * (u (n + 1) + u (n + 2)) - (u n + u (n + 1)) ^ 2 := by simp [hu]
  -- Cancel squares and re-group terms, then use recursive definition again.
  _ = u (n + 1) * (u (n + 2) - u n - u n) - u n ^ 2 := by ring
  _ = u (n + 1) * (u (n + 1) - u n) - u n ^ 2 := by rw [sub_eq_of_eq_add' (hu n)]
  -- Re-group terms, then use recursive definition again.
  _ = u (n + 1) ^ 2 - u n * (u n + u (n + 1)) := by ring
  _ = u (n + 1) ^ 2 - u n * u (n + 2) := by rw [hu]
  _ = _ := by ring
