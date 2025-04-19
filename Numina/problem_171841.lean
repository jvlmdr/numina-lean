-- https://cloud.kili-technology.com/label/projects/label/cm91j40co008sseaylhmcxbn8

import Mathlib

open Real Finset

/- Prove: For any $a_{1}, a_{2}, \cdots, a_{n} \in \mathbf{R}$, there exists
$k \in \{1, 2, \cdots, n\}$, such that for any non-negative real numbers
$b_{1} \geqslant b_{2} \geqslant \cdots \geqslant b_{n}$ not exceeding 1, we have
$\left|\sum_{i=1}^{n} b_{i} a_{i}\right| \leqslant \left|\sum_{i=1}^{k} a_{i}\right| $. -/

theorem inequalities_171841 (n : ℕ) (a : ℕ → ℝ) : ∃ k : ℕ,
    ∀ b : Fin n → ℝ, (∀ i, 0 ≤ b i) → (∀ i, b i ≤ 1) → Antitone b →
    |∑ i : Fin n, b i * a i| ≤ |∑ i ∈ range k, a i| := by

  -- Choose `k` from finite set to maximize `j ↦ |∑ i ∈ range j, a i|`.
  obtain ⟨k, hkn, hk_max⟩ : ∃ k ≤ n, ∀ j ≤ n, |∑ i ∈ range j, a i| ≤ |∑ i ∈ range k, a i| := by
    simpa using exists_max_image (Iic n) (fun j ↦ |∑ i ∈ range j, a i|) nonempty_Iic
  use k

  -- TODO: Move to top?
  cases n with
  | zero =>
    -- When `n` is zero, we have the trivial case `0 ≤ 0` using `k = 0`.
    simp
  | succ n =>

    intro b hb_zero hb_one hb_anti

    let b₀ : ℕ → ℝ := fun i ↦ if hi : i < n + 1 then b ⟨i, hi⟩ else 0
    -- TODO: Use in definition of k?
    let A : ℕ → ℝ := fun i ↦ ∑ j ∈ range i, a j

    calc _
    _ = |∑ i ∈ range (n + 1), (b₀ i - b₀ (i + 1)) * A (i + 1)| := by
      congr 1
      calc _
      _ = ∑ i : Fin (n + 1), b₀ i * a i := by
        unfold b₀
        simp
      _ = ∑ i ∈ range (n + 1), b₀ i * a i := Fin.sum_univ_eq_sum_range (fun i ↦ b₀ i * a i) _
      _ = ∑ i ∈ range (n + 1), b₀ i * (A (i + 1) - A i) := by
        unfold A
        simp only [sum_range_succ_sub_sum]

      -- _ = b' 0 * A 1 + ∑ i ∈ range n, b' (i + 1) * (A (i + 2) - A (i + 1)) := by
      --   rw [Finset.sum_range_succ', add_comm]
      --   sorry

      _ = ∑ i ∈ range n, b₀ (i + 1) * (A (i + 2) - A (i + 1)) + b₀ 0 * A 1 := by
        rw [Finset.sum_range_succ']
        suffices A 0 = 0 by simp [this]
        simp [A]

      _ = ∑ i ∈ range n, b₀ (i + 1) * A (i + 2) + b₀ 0 * A 1 -
          ∑ i ∈ range n, b₀ (i + 1) * A (i + 1) := by
        simp only [mul_sub, sum_sub_distrib]
        ring

      _ = ∑ i ∈ range (n + 1), b₀ i * A (i + 1) - ∑ i ∈ range (n + 1), b₀ (i + 1) * A (i + 1) := by
        congr 1
        · -- Extract the term on the left.
          rw [Finset.sum_range_succ']
        · -- Eliminate the term on the right.
          rw [Finset.sum_range_succ]
          suffices b₀ (n + 1) = 0 by simp [this]
          simp [b₀]
      _ = _ := by simp [sub_mul]

    _ ≤ _ := by sorry
