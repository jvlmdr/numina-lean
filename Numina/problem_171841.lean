-- https://cloud.kili-technology.com/label/projects/label/cm91j40co008sseaylhmcxbn8

import Mathlib

open Real Finset

/- Prove: For any $a_{1}, a_{2}, \cdots, a_{n} \in \mathbf{R}$, there exists
$k \in \{1, 2, \cdots, n\}$, such that for any non-negative real numbers
$b_{1} \geqslant b_{2} \geqslant \cdots \geqslant b_{n}$ not exceeding 1, we have
$\left|\sum_{i=1}^{n} b_{i} a_{i}\right| \leqslant \left|\sum_{i=1}^{k} a_{i}\right| $. -/

theorem inequalities_171841 (n : ℕ) (a : ℕ → ℝ) : ∃ k ≤ n,
    ∀ b : Fin n → ℝ, (∀ i, 0 ≤ b i) → (∀ i, b i ≤ 1) → Antitone b →
    |∑ i : Fin n, b i * a i| ≤ |∑ i ∈ range k, a i| := by
  -- Choose `k` from finite set to maximize `j ↦ |∑ i ∈ range j, a i|`.
  obtain ⟨k, hkn, hk_max⟩ : ∃ k ≤ n, ∀ j ≤ n, |∑ i ∈ range j, a i| ≤ |∑ i ∈ range k, a i| := by
    simpa using exists_max_image (Iic n) (fun j ↦ |∑ i ∈ range j, a i|) nonempty_Iic
  use k, hkn
  cases n with
  | zero =>
    -- When `n` is zero, we have the trivial case `0 ≤ 0` using `k = 0`.
    simp
  | succ n =>
    intro b hb_zero hb_one hb_anti
    -- Define an extended version of `b` taking zero beyond the range.
    let b₀ : ℕ → ℝ := fun i ↦ if hi : i < n + 1 then b ⟨i, hi⟩ else 0
    -- Define summation `A (i + 1) = a 0 + ⋯ + a i`.
    let A : ℕ → ℝ := fun i ↦ ∑ j ∈ range i, a j
    calc _
    _ = |∑ i ∈ range (n + 1), (b₀ i - b₀ (i + 1)) * A (i + 1)| := by
      congr 1
      calc _
      _ = ∑ i : Fin (n + 1), b₀ i * a i := by simp [b₀]
      _ = ∑ i ∈ range (n + 1), b₀ i * a i := Fin.sum_univ_eq_sum_range (fun i ↦ b₀ i * a i) _
      -- Replace `a i` with `A (i + 1) - A i`.
      _ = ∑ i ∈ range (n + 1), b₀ i * (A (i + 1) - A i) := by simp [A, sum_range_succ_sub_sum]
      -- Separate sum over `n + 1` elements into two sums over `n` elements, offset by 1.
      -- Extract and simplify the first term in the sum.
      _ = ∑ i ∈ range n, b₀ (i + 1) * (A (i + 2) - A (i + 1)) + b₀ 0 * A 1 := by
        rw [sum_range_succ']
        suffices A 0 = 0 by simp [this]
        simp [A]
      _ = ∑ i ∈ range n, b₀ (i + 1) * A (i + 2) + b₀ 0 * A 1 -
          ∑ i ∈ range n, b₀ (i + 1) * A (i + 1) := by
        simp only [mul_sub, sum_sub_distrib]
        ring
      -- Extend first sum on the left, second sum on the right.
      _ = ∑ i ∈ range (n + 1), b₀ i * A (i + 1) - ∑ i ∈ range (n + 1), b₀ (i + 1) * A (i + 1) := by
        congr 1
        · rw [sum_range_succ']
        · -- The additional new term is equal to zero since `b₀ (n + 1) = 0`.
          rw [sum_range_succ]
          suffices b₀ (n + 1) = 0 by simp [this]
          simp [b₀]
      _ = _ := by simp [sub_mul]
    -- Move the absolute value inside the sum to obtain an upper bound.
    _ ≤ _ := abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ range (n + 1), |b₀ i - b₀ (i + 1)| * |A (i + 1)| := by simp [abs_mul]
    _ ≤ ∑ i ∈ range (n + 1), |b₀ i - b₀ (i + 1)| * |A k| := by
      refine sum_le_sum fun i hi ↦ ?_
      rw [mem_range] at hi
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      unfold A
      refine hk_max (i + 1) hi
    _ = (∑ i ∈ range (n + 1), |b₀ i - b₀ (i + 1)|) * |A k| := .symm <| sum_mul _ _ _
    _ = |A k| * ∑ i ∈ range (n + 1), |b₀ i - b₀ (i + 1)| := mul_comm _ _
    -- Since `b i` are in decreasing order, we can eliminate the abs.
    _ = |A k| * ∑ i ∈ range (n + 1), (b₀ i - b₀ (i + 1)) := by
      suffices Antitone b₀ by
        congr
        funext i
        simpa using this i.le_succ
      intro u v huv
      unfold b₀
      by_cases hv : v < n + 1
      · have hu : u < n + 1 := huv.trans_lt hv
        simpa [hu, hv] using @hb_anti ⟨u, hu⟩ ⟨v, hv⟩ huv
      · simpa [hv] using dite_nonneg (fun hu ↦ hb_zero _) fun _ ↦ le_refl 0
    -- Use the telescope identity.
    _ = |A k| * (b₀ 0 - b₀ (n + 1)) := by rw [sum_range_sub']
    -- Eliminate `b₀ (n + 1) = 0`.
    _ = |A k| * b₀ 0 := by
      suffices b₀ (n + 1) = 0 by simp [this]
      simp [b₀]
    -- Use the fact that `b₀ 0 ≤ 1` to obtain final bound.
    _ ≤ |A k| := by
      suffices b₀ 0 ≤ 1 by exact mul_le_of_le_one_right (abs_nonneg (A k)) this
      simpa [b₀] using hb_one 0
    _ = _ := rfl
