-- https://cloud.kili-technology.com/label/projects/label/cma1au4rj00hgthv57l3srvpg

import Mathlib

/- Given the natural numbers
a = 2 * (1 + 2 + 3 + ⋯ + 2016) - 2016
b = 1 + 1 * 2 + 1 * 2 * 3 + 1 * 2 * 3 * 4 + … + 1 * 2 * 3 * ⋯ * 2016
Show that:
a) a is a perfect square;
b) b is not a perfect square. -/

theorem number_theory_105222 :
    IsSquare (2 * ∑ i ∈ Finset.Icc 1 2016, i - 2016) ∧
    ¬IsSquare (∑ i ∈ Finset.Icc 1 2016, ∏ j ∈ Finset.Icc 1 i, j) := by
  constructor
  · -- We can prove (a) for general n.
    suffices ∀ n, IsSquare (2 * ∑ i ∈ Finset.Icc 1 n, i - n) from this 2016
    intro n
    use n
    cases n with
    | zero => simp
    | succ n =>
      calc _
      -- Rewrite as sum over `Finset.range` in order to use `Finset.sum_range_id_mul_two`.
      _ = 2 * (∑ i ∈ Finset.Icc 1 n, i + (n + 1)) - (n + 1) := by simp [Finset.sum_Icc_succ_top]
      _ = 2 * ∑ i ∈ Finset.Icc 1 n, i + (n + 1) := by
        rw [mul_add]
        simp [Nat.add_sub_assoc, two_mul]
      _ = 2 * ∑ i ∈ Finset.Ico 1 (n + 1), i + (n + 1) := rfl
      _ = 2 * ∑ i ∈ Finset.range (n + 1), i + (n + 1) := by simp [Finset.sum_range_eq_add_Ico]
      -- Then it is trivial to show that the expression is a square.
      _ = _ := by
        rw [mul_comm 2, Finset.sum_range_id_mul_two, add_tsub_cancel_right]
        ring
  · -- For `i ≥ 5`, every term in the sum will be divisible by 10 (1 * 2 * 3 * 4 * 5 * ...).
    -- Therefore it will suffice to show that the last digit is not a square modulo 10.
    -- This strategy will work for general `n ≥ 4`.
    suffices ∀ n ≥ 4, ¬IsSquare (∑ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc 1 i, j) from
      this 2016 (by norm_num)
    intro n hn

    -- Use the fact that `IsSquare x` implies `IsSquare (x : Fin b)` for any `b ≠ 0`.
    -- Use coercion to `Fin 10` rather than `% 10` for easier manipulation of sum and product.
    have h_fin (b : ℕ) [NeZero b] (x : ℕ) : IsSquare x → IsSquare (x : Fin b) :=
      Exists.imp' (fun x ↦ (x : Fin b)) fun m hx ↦ hx ▸ Nat.cast_mul m m
    -- Apply the contrapositive implication.
    refine mt (h_fin 10 _) ?_
    -- Move the cast to the inner expression.
    simp only [Nat.cast_sum, Nat.cast_prod]

    -- The first 4 terms are 1 + 2 + 6 + 24 = 33, hence the last digit is 3.
    suffices ∑ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc 1 i, (j : Fin 10) = 3 by
      rw [this]
      -- Could use `decide` at this point to check the 10 cases automatically,
      -- but it's preferable to obtain the result explicitly.
      -- Enumerate the squares modulo 10 by taking the image of univ.
      suffices 3 ∉ Finset.image (fun x ↦ x * x) (.univ : Finset (Fin 10)) by
        simpa [IsSquare, eq_comm] using this
      -- Switch to `Finset ℕ` to simplify with `Finset.range_succ`.
      rw [← Finset.mem_map' Fin.valEmbedding]
      -- The set of squares modulo 10 is {0, 1, 4, 5, 6, 9}.
      have : 3 ∉ Finset.image (fun x ↦ x * x % 10) (.range 10) := by simp [Finset.range_succ]
      exact this

    calc _
    -- Separate the first four terms in the sum.
    _ = ∑ i ∈ Finset.Icc 1 4 ∪ Finset.Ioc 4 n, ∏ j ∈ Finset.Icc 1 i, ↑j := by
      congr
      symm
      simpa [Set.ext_iff, Finset.ext_iff] using Set.Icc_union_Ioc_eq_Icc NeZero.one_le hn
    _ = ∑ i ∈ Finset.Icc 1 5, ∏ j ∈ Finset.Ioc 1 i, (j : Fin 10) := by
      refine Finset.sum_union_eq_left fun i ↦ ?_
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      intro hi hi'
      -- Separate the first 5 terms of the product.
      calc _
      _ = ∏ j ∈ Finset.Icc 1 5 ∪ Finset.Ioc 5 i, (j : Fin 10) := by
        congr
        symm
        simpa [Set.ext_iff, Finset.ext_iff] using Set.Icc_union_Ioc_eq_Icc NeZero.one_le hi.1
      _ = 0 * ∏ j ∈ Finset.Ioc 5 i, (j : Fin 10) := by
        refine Finset.prod_union ?_
        refine Finset.disjoint_left.mpr fun j ↦ ?_
        simp only [Finset.mem_Icc, Finset.mem_Ioc]
        intro h h'
        linarith
      _ = _ := by simp
    _ = 3 := rfl
