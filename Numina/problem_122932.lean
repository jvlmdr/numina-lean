-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9y000pueaxlaz2izkl

import Mathlib

open Real

/- How many integers $m$ satisfy both the following properties:
(i) $1 \leq m \leq 5000$;
(ii) $[\sqrt{m}]=[\sqrt{m+125}]$ ?
(Here $[x]$ denotes the largest integer not exceeding $x$, for any real number $x$.) -/

-- Defined in analogy to `Finset.Ioc_disjoint_Ioc_of_le` in Mathlib.
lemma Finset.Ico_disjoint_Ico_of_le {α : Type*} [PartialOrder α] [LocallyFiniteOrder α]
    (a b c : α) {d : α} (hbc : b ≤ c) : Disjoint (Ico a b) (Ico c d) :=
  disjoint_left.2 fun _ h1 h2 ↦ not_and_of_not_left _
    ((mem_Ico.1 h1).2.trans_le hbc).not_le (mem_Ico.1 h2)

theorem number_theory_122932 :
    {m : ℕ | m ∈ Set.Icc 1 5000 ∧ ⌊√m⌋₊ = ⌊√(m + 125)⌋₊}.ncard = 72 := by
  calc _
  -- Switch to `Nat.sqrt`.
  _ = {m | m ∈ Set.Icc 1 5000 ∧ m.sqrt = (m + 125).sqrt}.ncard := by
    simp [← nat_floor_real_sqrt_eq_nat_sqrt]
  _ = {m | m ∈ Set.Icc 1 5000 ∧ ∃ k, k = m.sqrt ∧ k = (m + 125).sqrt}.ncard := by simp

  -- Translate equality of `Nat.sqrt` into an interval condition.
  _ = {m | m ∈ Set.Icc 1 5000 ∧ ∃ k, m ∈ Set.Ico (k ^ 2) ((k + 1) ^ 2) ∧
      m + 125 ∈ Set.Ico (k ^ 2) ((k + 1) ^ 2)}.ncard := by
    simp [Nat.eq_sqrt, sq]
  -- Write as membership of `m + 125` in the intersection of two sets.
  _ = {m | m ∈ Set.Icc 1 5000 ∧ ∃ k, m + 125 ∈
      Set.Ico (k ^ 2 + 125) ((k + 1) ^ 2 + 125) ∩ Set.Ico (k ^ 2) ((k + 1) ^ 2)}.ncard := by
    simp
  -- Take the intersection of the two intervals.
  _ = {m | m ∈ Set.Icc 1 5000 ∧ ∃ k, m + 125 ∈ Set.Ico (k ^ 2 + 125) ((k + 1) ^ 2)}.ncard := by
    simp [Set.Ico_inter_Ico]

  -- Establish fixed bounds on `k`.
  -- The lower bound comes from `k ^ 2 + 125 ≤ m < (k + 1) ^ 2`.
  -- The upper bound comes from `k ^ 2 ≤ m ≤ 5000`.
  _ = {m | m ∈ Set.Icc 1 5000 ∧ ∃ k ∈ Set.Ioc 62 70,
      m + 125 ∈ Set.Ico (k ^ 2 + 125) ((k + 1) ^ 2)}.ncard := by
    congr
    ext m
    simp only [Set.mem_setOf_eq]
    rw [and_congr_right_iff]
    intro hm
    refine exists_congr fun k ↦ ?_
    rw [iff_and_self]
    intro hk
    refine And.intro ?_ ?_
    · have hk : k ^ 2 + 125 < (k + 1) ^ 2 := by simpa using Set.nonempty_of_mem hk
      -- The `k ^ 2` terms cancel, leaving `125 < 2 * k + 1`, identical to `2 * 62 < 2 * k`.
      linarith
    · -- Combined `k ^ 2 ≤ m` and `m ≤ 5000`.
      have hk : k ^ 2 ≤ 5000 := by
        simp only [Set.mem_Icc] at hm
        simp only [Set.mem_Ico, add_le_add_iff_right] at hk
        exact le_trans hk.1 hm.2
      -- The bound comes from `Nat.sqrt 5000 = 70`.
      rw [← Nat.le_sqrt'] at hk
      convert hk
      norm_num

  -- Establish that we can drop the constraint on `m`.
  _ = {m | ∃ k ∈ Set.Ioc 62 70, m + 125 ∈ Set.Ico (k ^ 2 + 125) ((k + 1) ^ 2)}.ncard := by
    congr
    ext m
    simp only [Set.mem_setOf_eq]
    rw [and_iff_right_iff_imp]
    intro ⟨k, hk, hm⟩
    simp only [Set.mem_Ico, add_le_add_iff_right] at hm
    simp only [Set.mem_Ioc] at hk
    refine And.intro ?_ ?_
    · -- The lower bound `1 ≤ m` follows from `k ^ 2 ≤ m` with `62 < k`.
      refine le_trans ?_ hm.1
      exact Nat.one_le_pow 2 k (by linarith)
    · -- The upper bound `m ≤ 5000` follows from `m + 125 < (k + 1) ^ 2` with `k ≤ 70`.
      suffices m + 125 ≤ 5125 by simpa
      calc _
      _ ≤ (k + 1) ^ 2 := hm.2.le
      _ ≤ (70 + 1) ^ 2 := Nat.pow_le_pow_left (by linarith) 2
      _ ≤ 5125 := by norm_num

  -- Write the constraint on `m` rather than `m + 125`.
  _ = {m | ∃ k ∈ Set.Ioc 62 70, m ∈ Set.Ico (k ^ 2) ((k + 1) ^ 2 - 125)}.ncard := by
    simp [Nat.lt_sub_iff_add_lt]

  -- Write as a union of finite sets indexed by `k`.
  -- Use `Finset.preimage` to obtain the membership of `· + 125` in the set.
  _ = ((Finset.Ioc 62 70).biUnion fun k ↦ Finset.Ico (k ^ 2) ((k + 1) ^ 2 - 125)).card := by
    rw [← Set.ncard_coe_Finset]
    congr
    ext m
    simp [-Set.mem_Ico]

  -- Show that the sets are disjoint, hence their independent counts can be summed.
  _ = ∑ k ∈ Finset.Ioc 62 70, (Finset.Ico (k ^ 2) ((k + 1) ^ 2 - 125)).card := by
    refine Finset.card_biUnion ?_
    intro k₁ hk₁ k₂ hk₂ hk_ne
    clear hk₁ hk₂
    wlog hk_le : k₁ ≤ k₂ generalizing k₁ k₂
    · rw [disjoint_comm]
      exact this k₂ k₁ hk_ne.symm (le_of_not_ge hk_le)
    have hk_lt : k₁ < k₂ := lt_of_le_of_ne hk_le hk_ne
    refine Finset.Ico_disjoint_Ico_of_le _ _ _ ?_
    calc _
    _ ≤ (k₁ + 1) ^ 2 := by simp
    _ ≤ k₂ ^ 2 := Nat.pow_le_pow_of_le_left hk_lt 2

  -- Eliminate the quadratic terms from the sum.
  _ = 2 * ∑ k ∈ Finset.Ioc 62 70, (k - 62) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    calc _
    _ = k ^ 2 + 2 * k - 2 * 62 - k ^ 2 := by simp [add_sq]
    _ = k ^ 2 + (2 * k - 2 * 62) - k ^ 2 := by
      rw [Nat.add_sub_assoc]
      gcongr
      simp only [Finset.mem_Ioc] at hk
      exact hk.1.le
    _ = 2 * (k - 62) := by simp [mul_tsub]

  -- At this point, the sum can simply be evaluated.
  -- It can be shown that it reduces to 2 * (1 + 2 + ⋯ + 8) = 8 * 9.
  _ = 2 * ∑ k ∈ Finset.range 9, k := rfl
  _ = _ := by simp [Finset.sum_range_id]
