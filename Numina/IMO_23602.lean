-- https://cloud.kili-technology.com/label/projects/review/cmauuk3x300001rayfnv18ot0

import Mathlib

open Finset
open scoped Nat

/- Evaluate $S = \sum_{k=1}^{n} k (k+1) \cdots (k+p)$, where $n$ and $p$ are positive integers. -/

theorem algebra_23602 {n p : ℕ} :
    ∑ k ∈ Icc 1 n, ∏ i ∈ range (p + 1), (k + i) =
    (∏ i ∈ range (p + 2), (n + i)) / (p + 2) := by
  calc _
  -- Rewrite as sum over `range` with terms depending on `k + 1`.
  _ = ∑ k ∈ (range n).map (addRightEmbedding 1), ∏ i ∈ range (p + 1), (k + i) := by
    congr
    calc _
    _ = Ico 1 (n + 1) := rfl
    _ = map (addRightEmbedding 1) (Ico 0 n) := (map_add_right_Ico 0 n 1).symm
    _ = _ := by simp
  _ = ∑ k ∈ range n, ∏ i ∈ range (p + 1), (k + 1 + i) := by simp
  -- Replace the product with `ascFactorial`.
  _ = ∑ k ∈ range n, Nat.ascFactorial (k + 1) (p + 1) := by
    congr
    funext k
    symm
    exact Nat.ascFactorial_eq_prod_range (k + 1) (p + 1)
  -- Apply the identity `ascFactorial_eq_factorial_mul_choose`.
  _ = (p + 1)! * ∑ k ∈ range n, (k + p + 1).choose (p + 1) := by
    simp [Nat.ascFactorial_eq_factorial_mul_choose, add_assoc, Finset.mul_sum]
  -- Replace summand with a difference of binomials that will telescope.
  _ = (p + 1)! * ∑ k ∈ range n, ((k + p + 2).choose (p + 2) - (k + p + 1).choose (p + 2)) := by
    congr
    funext k
    refine Nat.eq_sub_of_add_eq ?_
    exact Nat.choose_succ_succ (k + p + 1) (p + 1)
  -- Cancel the telescoping terms.
  _ = (p + 1)! * (n + p + 1).choose (p + 2) := by
    congr
    convert sum_range_tsub (f := fun k ↦ (k + p + 1).choose (p + 2)) ?_ n using 1
    · congr
      funext k
      congr 2
      abel
    · simp
    · suffices Monotone (· + p + 1) from .comp (Nat.choose_mono (p + 2)) this
      simpa [add_assoc] using add_right_mono
  -- Rewrite as an explicit product using `Nat.ascFactorial_eq_factorial_mul_choose'`.
  _ = _ := by
    refine Nat.eq_div_of_mul_eq_right (by simp) ?_
    symm
    convert Nat.ascFactorial_eq_factorial_mul_choose' n (p + 2) using 1
    · symm
      exact Nat.ascFactorial_eq_prod_range n (p + 2)
    · rw [Nat.factorial_succ (p + 1), mul_assoc]
      rfl
