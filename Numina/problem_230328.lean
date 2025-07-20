-- https://cloud.kili-technology.com/label/projects/label/cma3ygf2a007zahayss2mze8r

import Mathlib

open Real

/- Let $k_{1} < k_{2} < k_{3} < \cdots$ be positive integers, and no two of them are consecutive,
and for $m = 1, 2, 3, \ldots$, $S_{m} = k_{1} + k_{2} + \cdots + k_{m}$. Prove that for every
positive integer $n$, the interval $[S_{n}, S_{n+1})$ contains at least one perfect square. -/

-- There is a square between two integers iff there is an integer between their square roots.
lemma square_mem_Ico_iff_mem_Ico_sqrt (n a b : ℕ) :
    n ^ 2 ∈ Set.Ico a b ↔ (n : ℝ) ∈ Set.Ico √a √b := by
  simp only [Set.mem_Ico]
  refine and_congr ?_ ?_
  · calc _
    _ ↔ √a ^ 2 ≤ ↑(n ^ 2) := by
      rw [sq_sqrt (Nat.cast_nonneg _)]
      exact Nat.cast_le.symm
    _ ↔ _ := by
      rw [Nat.cast_pow]
      refine sq_le_sq₀ ?_ ?_ <;> simp
  · calc _
    _ ↔ ↑(n ^ 2) < √b ^ 2 := by
      rw [sq_sqrt (Nat.cast_nonneg _)]
      exact Nat.cast_lt.symm
    _ ↔ _ := by
      rw [Nat.cast_pow]
      refine sq_lt_sq₀ ?_ ?_ <;> simp

-- Given a sequence `k` that increases by at least `r` in each step,
-- obtain a lower bound on the difference between elements `n` and `n + i`.
lemma le_of_le_diff {r : ℕ} {k : ℕ → ℕ} (hk : ∀ n, k n + r ≤ k (n + 1)) (n i : ℕ) :
    k n + r * i ≤ k (n + i) := by
  induction i with
  | zero => simp
  | succ i IH =>
    calc k n + r * (i + 1)
    _ = k n + r * i + r := by ring
    _ ≤ k (n + i) + r := by gcongr
    _ ≤ k (n + (i + 1)) := hk (n + i)

-- The series is bounded above by the square of the largest element.
-- This is obtained by bounding the sequence above by an arithmetic sequence.
lemma four_mul_sum_le_sq {k : ℕ → ℕ} (hk : ∀ n, k n + 2 ≤ k (n + 1)) (n : ℕ) :
    4 * ∑ i in Finset.range (n + 1), k i ≤ (k n + 1) ^ 2 := by
  let m := k n / 2
  let r := k n % 2
  have hmr : k n = 2 * m + r := (Nat.div_add_mod (k n) 2).symm
  have hr : r < 2 := Nat.mod_lt (k n) two_pos
  calc _
  -- Reverse sum and bound above by sum of `k n, k n - 2, ..., k n - 2 * n`.
  _ ≤ 4 * ∑ i in Finset.range (n + 1), (k n - 2 * i) := by
    rw [← Finset.sum_range_reflect]
    rw [add_tsub_cancel_right]
    gcongr with i hi
    refine Nat.le_sub_of_add_le ?_
    rw [Finset.mem_range_succ_iff] at hi
    simpa [hi] using le_of_le_diff hk (n - i) i
  -- Extend sum to `k n, k n - 2, ..., k n - 2 * m = r`.
  _ ≤ 4 * ∑ i in Finset.range (m + 1), (k n - 2 * i) := by
    gcongr
    -- Use `k 0 + 2 * n ≤ k n` to show that `n ≤ m` since `2 * n ≤ k n = 2 * m + r < 2 * (m + 1)`
    suffices n < m + 1 from Nat.le_of_lt_succ this
    suffices 2 * n < 2 * (m + 1) by simpa
    calc _
    _ ≤ k 0 + 2 * n := by simp
    _ ≤ k n := by simpa using le_of_le_diff hk 0 n
    _ = 2 * m + r := by rw [hmr]
    _ < 2 * m + 2 := by simpa using hr
  -- Replace `k n` with `2 * m + r`.
  _ = 4 * ∑ i in Finset.range (m + 1), (2 * (m - i) + r) := by
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range_succ_iff] at hi
    rw [hmr, mul_tsub]
    refine Nat.sub_add_comm ?_
    simpa using hi
  -- Un-reverse the sum again.
  _ = 4 * ∑ i in Finset.range (m + 1), (2 * i + r) := by
    simpa using Finset.sum_range_reflect (2 * · + r) (m + 1)
  _ = 4 * ((m + 1) * (m + r)) := by
    rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, mul_comm 2, Finset.sum_range_id_mul_two]
    simp
  _ ≤ _ := by
    rw [hmr]
    interval_cases r
    · suffices 4 * m * (m + 1) ≤ 4 * m * (m + 1) + 1 by convert this using 1 <;> ring
      simp
    · refine le_of_eq ?_
      ring

theorem number_theory_230328 (k : ℕ → ℕ) (hk : StrictMono k)
    (hk_pos : ∀ n, 0 < k n) (hk_consec : ∀ n, k (n + 1) ≠ k n + 1)
    (S : ℕ → ℕ) (hS : ∀ m, S m = ∑ i in Finset.range (m + 1), k i) (n : ℕ) :
    ∃ m, m ^ 2 ∈ Set.Ico (S n) (S (n + 1)) := by
  -- Since the sequence is strictly increasing and non-consecutive, it increases by at least 2.
  have hk (n : ℕ) : k n + 2 ≤ k (n + 1) := by
    change k n + 1 < k (n + 1)
    rw [lt_iff_le_and_ne]
    constructor
    · exact hk (lt_add_one n)
    · exact fun h ↦ hk_consec n h.symm

  -- This is equivalent to there being an integer between `√(S n)` and `√(S (n + 1))`.
  simp only [square_mem_Ico_iff_mem_Ico_sqrt]
  -- It suffices to show that the gap between two roots is at least 1.
  suffices √(S n) + 1 ≤ √(S (n + 1)) by
    simp only [Set.mem_Ico]
    -- Use the ceil of the lower bound.
    refine ⟨⌈√(S n)⌉₊, Nat.le_ceil _, ?_⟩
    refine lt_of_lt_of_le ?_ this
    exact Nat.ceil_lt_add_one (sqrt_nonneg _)

  -- Substitute `S (n + 1) = S n + k n`, square both sides, cancel `S n` terms.
  have hS_succ : S (n + 1) = S n + k (n + 1) := by simpa [hS] using Finset.sum_range_succ _ _
  suffices 2 * √(S n) + 1 ≤ k (n + 1) by
    refine le_sqrt_of_sq_le ?_
    simpa [hS_succ, add_sq, add_assoc]

  -- Consider bound in terms of `k n` rather than `k (n + 1)`.
  suffices 2 * √(S n) ≤ k n + 1 by
    calc _
    _ ≤ (↑(k n + 1 + 1) : ℝ) := by simpa using add_le_add_right this 1
    _ ≤ _ := Nat.cast_le.mpr (hk n)
  -- Take the square of both sides and return to the natural.
  refine (sq_le_sq₀ ?_ ?_).mp ?_
  · simp
  · refine add_nonneg ?_ ?_ <;> simp
  -- Employ the result for bounding the series from above.
  suffices 4 * (S n) ≤ (k n + 1) ^ 2 by
    convert (Nat.cast_le (α := ℝ)).mpr this using 1
    · rw [mul_pow, sq_sqrt (Nat.cast_nonneg _), Nat.cast_mul]
      ring
    · simp
  rw [hS]
  exact four_mul_sum_le_sq hk n
