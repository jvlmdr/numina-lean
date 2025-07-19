-- https://cloud.kili-technology.com/label/projects/label/cm7enii3r00nxzz87ugjp9o4o
-- https://artofproblemsolving.com/wiki/index.php/2020_AMC_12B_Problems/Problem_21

import Mathlib

/- How many positive integers n satisfy $(n + 1000) / 70 = \lfloor \sqrt{n} \rfloor$?
(Recall that $\lfloor x \rfloor$ is the greatest integer not exceeding $x$.)
(A) 2
(B) 4
(C) 6
(D) 30
(E) 32 -/

theorem number_theory_93855 :
    Set.ncard {n : ℕ | 0 < n ∧ (n + 1000 : ℝ) / 70 = ⌊√n⌋₊} = 6 := by
  simp only [Real.nat_floor_real_sqrt_eq_nat_sqrt]

  -- We know that `(n + 1000) / 70` is an integer; `70 ∣ n + 1000`.
  -- This simplifies to `70 ∣ n + 20` since 1000 = 70 * 14.
  -- This means `∃ k, n + 20 = 70 * k` or `n = 70 * k - 20`.
  -- Not valid for `k = 0`, therefore re-parameterize `∃ m, n = 70 * m + 50`.
  -- (Not trivial to consider `70 ∣ n - 50` as it requires `50 ≤ n` everywhere.)
  have h_reparam : Set.ncard {n : ℕ | 0 < n ∧ (n + 1000 : ℝ) / 70 = n.sqrt} =
      Set.ncard {m : ℕ | m + 15 = (70 * m + 50).sqrt} := by
    calc _
    -- Rewrite the real division constraint as integer multiplication.
    _ = Set.ncard {n : ℕ | 0 < n ∧ n + 1000 = 70 * n.sqrt} := by
      congr
      ext n
      simp only [Set.mem_setOf, and_congr_right_iff]
      intro _
      rw [div_eq_iff (by norm_num), mul_comm]
      rw [← Nat.cast_inj (R := ℝ)]
      simp
    -- Eliminate the extraneous condition `0 < n`.
    _ = Set.ncard {n : ℕ | n + 1000 = 70 * n.sqrt} := by
      congr
      ext n
      simp only [Set.mem_setOf, and_iff_right_iff_imp]
      intro hn
      refine Nat.zero_lt_of_ne_zero ?_
      contrapose! hn
      simp [hn]
    -- Introduce `k` such that `n + 20 = 70 * k`, and `n + 1000 = 70 * (k + 14)`.
    -- The constraint `0 ≤ n` is equivalent to `1 ≤ k`.
    _ = Set.ncard ((70 * · - 20) '' {k : ℕ | 0 < k ∧ k + 14 = (70 * k - 20).sqrt}) := by
      congr
      ext n
      simp only [Set.mem_setOf, Set.mem_image]
      constructor
      · intro hn
        have hn_dvd : 70 ∣ n + 20 := by
          suffices 70 ∣ n + 20 + 70 * 14 by simpa using this
          exact Dvd.intro n.sqrt hn.symm
        use (n + 20) / 70
        rw [Nat.mul_div_cancel' hn_dvd]
        simp only [add_tsub_cancel_right, and_true]
        refine ⟨?_, ?_⟩
        · have : 70 ≤ n + 20 := Nat.le_of_dvd (by simp) hn_dvd
          refine (Nat.one_le_div_iff ?_).mpr this
          norm_num
        · rw [← Nat.mul_right_inj (by norm_num : 70 ≠ 0)]
          convert hn using 1
          rw [mul_add]
          rw [Nat.mul_div_cancel' hn_dvd]
      · simp only [forall_exists_index, and_imp]
        intro m hm_pos hm hn
        have hm_gt : 20 < 70 * m := by
          have : 1 ≤ m := hm_pos
          have : 70 ≤ 70 * m := Nat.mul_le_mul_left 70 hm_pos
          exact lt_of_lt_of_le (by norm_num) this
        rw [← hn, ← hm, mul_add]
        rw [← Nat.sub_add_comm hm_gt.le]
        simp
    -- Re-parameterize `k = m.succ` to eliminate the positivity constraint.
    _ = Set.ncard (((70 * · - 20) ∘ Nat.succ) ''
        {m : ℕ | m.succ + 14 = (70 * m.succ - 20).sqrt}) := by
      rw [Set.image_comp]
      refine congrArg Set.ncard (congrArg _ ?_)
      calc {k | 0 < k ∧ k + 14 = (70 * k - 20).sqrt}
      _ = Nat.succ '' (Nat.succ ⁻¹' {k | 0 < k ∧ k + 14 = (70 * k - 20).sqrt}) := by
        rw [Set.image_preimage_eq_iff.mpr]
        · simpa only [Nat.range_succ] using Set.inter_subset_left
      _ = Nat.succ '' {a | a.succ + 14 = (70 * a.succ - 20).sqrt} := by
        simp [Set.preimage_setOf_eq]
    -- Fold the `succ` into the function; eliminate the subtraction.
    _ = Set.ncard ((70 * · + 50) '' {m : ℕ | m + 15 = (70 * m + 50).sqrt}) := by rfl
    -- By injectivity, the cardinality of the image is the same.
    _ = Set.ncard ({m : ℕ | m + 15 = (70 * m + 50).sqrt}) :=
      Set.ncard_image_of_injective _ fun a b ↦ by simp

  -- Then it remains to characterize the set of `m` which satisfy the equality.
  have h_eq_sqrt (m : ℕ) : m + 15 = (70 * m + 50).sqrt ↔
      (5 ≤ m ∧ m ≤ 35) ∧ (m ≤ 6 ∨ 32 ≤ m) := by
    calc _
    _ ↔ (m + 15) ^ 2 ≤ 70 * m + 50 ∧ 70 * m + 50 < (m + 16) ^ 2 := by
      rw [Nat.eq_sqrt']
    _ ↔ (m + 15 : ℝ) ^ 2 ≤ 70 * m + 50 ∧ 70 * m + 50 < (m + 16 : ℝ) ^ 2 := by
      refine and_congr ?_ ?_
      · rw [← Nat.cast_le (α := ℝ)]
        simp
      · rw [← Nat.cast_lt (α := ℝ)]
        simp
    _ ↔ |(m - 20 : ℝ)| ≤ √225 ∧ √155 < |(m - 19 : ℝ)| := by
      rw [← sub_nonpos, ← sub_pos]
      -- Consider the general form:
      -- `(x + b)^2 - (70 * x + 50)`
      -- `x^2 + 2bx + b^2 - 2*35x - 50`
      -- `x^2 - 2(35 - b)x + b^2 - 50`
      -- `(x - (35 - b))^2 - (35 - b)^2 + b^2 - 50`
      -- `(x - (35 - b))^2 - 35^2 + 2*35b - b^2 + b^2 - 50`
      -- `(x - (35 - b))^2 - (35(35 - 2b) + 50)`
      have h_quad (b x : ℝ) : (x + b) ^ 2 - (70 * x + 50) =
          (x - (35 - b)) ^ 2 - (35 * (35 - 2 * b) + 50) := by ring
      rw [h_quad, h_quad, sub_nonpos, sub_pos]
      refine and_congr ?_ ?_
      · rw [← sq_abs]
        rw [← Real.le_sqrt (abs_nonneg _) (by norm_num)]
        norm_num
      · rw [← sq_abs]
        rw [← Real.sqrt_lt (by norm_num) (abs_nonneg _)]
        norm_num
    _ ↔ (20 - 15 ≤ (m : ℝ) ∧ (m : ℝ) ≤ 20 + 15) ∧ (m < 19 - √155 ∨ 19 + √155 < m) := by
      refine and_congr ?_ ?_
      · have h225 : √225 = 15 := by rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
        rw [abs_le, h225]
        exact and_congr le_sub_iff_add_le' tsub_le_iff_left
      · rw [lt_abs, neg_sub]
        rw [or_comm]
        exact or_congr lt_tsub_comm lt_tsub_iff_left
    _ ↔ _ := by
      refine and_congr ?_ ?_
      · norm_num
      · refine or_congr ?_ ?_
        · rw [← not_le, ← Nat.ceil_le, not_le]
          suffices ⌈19 - √155⌉₊ = 7 by rw [this, Nat.lt_succ]
          rw [Nat.ceil_eq_iff (by norm_num)]
          constructor
          · rw [lt_sub_comm, Real.sqrt_lt] <;> norm_num
          · rw [sub_le_comm, Real.le_sqrt] <;> norm_num
        · rw [← not_le, ← Nat.le_floor_iff (by simp [add_nonneg]), not_le]
          rw [add_comm, Nat.floor_add_ofNat (Real.sqrt_nonneg _)]
          suffices ⌊√155⌋₊ = 12 by rw [this, Nat.succ_le_iff]
          rw [Nat.floor_eq_iff (Real.sqrt_nonneg _)]
          constructor
          · rw [Real.le_sqrt] <;> norm_num
          · rw [Real.sqrt_lt] <;> norm_num

  calc _
  _ = {m | m + 15 = (70 * m + 50).sqrt}.ncard := h_reparam
  _ = {m | (5 ≤ m ∧ m ≤ 35) ∧ (m ≤ 6 ∨ 32 ≤ m)}.ncard := by rw [Set.ext h_eq_sqrt]
  _ = (Finset.toSet (.Icc 5 6 ∪ .Icc 32 35)).ncard := by
    congr
    ext m
    simp only [Set.mem_setOf, Finset.coe_union, Finset.coe_Icc, Set.mem_union, Set.mem_Icc]
    rw [and_or_left]
    refine or_congr ?_ ?_
    · rw [and_assoc]
      simp only [and_congr_right_iff, and_iff_right_iff_imp]
      intro h1 h2
      linarith
    · rw [and_comm, ← and_assoc]
      simp only [and_congr_left_iff, and_iff_left_iff_imp]
      intro h1 h2
      linarith
  _ = 6 := by
    rw [Set.ncard_coe_Finset]
    rfl
