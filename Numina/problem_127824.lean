-- https://cloud.kili-technology.com/label/projects/label/cmcbouv7300n3ueaxzr2tyxwi

import Mathlib

open Finset

open scoped List

/- Prove that for any positive numbers $a_1, a_2, \cdots, a_n$, the inequality
$$
\frac{1}{a_1} + \frac{2}{a_1 + a_2} + \cdots + \frac{n}{a_1 + \cdots + a_n} <
  4 \left(\frac{1}{a_1} + \cdots + \frac{1}{a_n}\right)
$$
holds. -/

lemma sublist_sum_take_len_le_sum_of_sorted {s l : List ℝ} (hsl : s <+ l) (hl : l.Sorted (· ≤ ·)) :
    (l.take s.length).sum ≤ s.sum := by
  induction hsl with
  | slnil => simp
  | @cons₂ s l x hsl IH => simpa using IH hl.of_cons
  | @cons s l x hsl IH =>
    refine le_trans ?_ (IH hl.of_cons)
    refine List.Forall₂.sum_le_sum ?_
    have hl := hl.chain
    rw [List.chain_iff_forall₂] at hl
    cases hl with
    | inl hl => simpa [hl] using hsl
    | inr hl =>
      convert List.forall₂_take s.length hl using 1
      cases s.length.eq_zero_or_pos with
      | inl hs => simp [hs]
      | inr hs =>
        calc _
        _ = List.take s.length ((x :: l).take (l.length - 1 + 1)) := by
          rw [Nat.sub_add_cancel (le_trans hs hsl.length_le)]
          rw [List.take_take, inf_of_le_left hsl.length_le]
        _ = _ := by simp [List.dropLast_eq_take]

-- lemma sublist_sum_take_le_sum_take_of_sorted {s l : List ℝ} (hsl : s <+ l) (hl : l.Sorted (· ≤ ·))
--     {n : ℕ} (hn : n ≤ s.length) :
--     (l.take n).sum ≤ (s.take n).sum := by
--   convert sublist_sum_take_len_le_sum_of_sorted ((s.take_sublist n).trans hsl) hl
--   simpa using hn

lemma subperm_sum_take_len_le_sum_of_sorted {s l : List ℝ} (hsl : s <+~ l) (hl : l.Sorted (· ≤ ·)) :
    (l.take s.length).sum ≤ s.sum := by
  rcases hsl with ⟨t, hts, htl⟩
  convert sublist_sum_take_len_le_sum_of_sorted htl hl using 1
  · rw [hts.length_eq]
  · rw [hts.sum_eq]

lemma subperm_sum_take_le_sum_take_of_sorted {s l : List ℝ} (hsl : s <+~ l) (hl : l.Sorted (· ≤ ·))
    {n : ℕ} (hn : n ≤ s.length) :
    (l.take n).sum ≤ (s.take n).sum := by
  convert subperm_sum_take_len_le_sum_of_sorted ((s.take_sublist n).subperm.trans hsl) hl
  simpa using hn


lemma lemma_a (a : ℕ → ℝ) (ha_pos : ∀ i, 0 < a i) (ha_mono : Monotone a) (i : ℕ) :
    (i + 1) / ∑ j ∈ range (i + 1), a j ≤ (a 0)⁻¹ := by
  calc _
  _ ≤ (i + 1) / ((i + 1) * a 0) := by
    refine div_le_div_of_nonneg_left ?_ ?_ ?_
    · linarith
    · exact mul_pos (by linarith) (ha_pos 0)
    calc _
    _ = ∑ j ∈ range (i + 1), a 0 := by simp
    _ ≤ _ := sum_le_sum fun j hi ↦ ha_mono (Nat.zero_le j)
  _ = _ := by
    refine div_mul_cancel_left₀ ?_ _
    exact Nat.cast_add_one_ne_zero i

example (a : ℕ → ℝ) (ha_pos : ∀ i, 0 < a i) (ha_mono : Monotone a) (k : ℕ) (hk : 2 ≤ k) :
    ∑ i ∈ range (2 * k), (i + 1) / ∑ j ∈ range (i + 1), a j ≤ 4 * ∑ i ∈ range (k - 1), (a i)⁻¹ ∧
    ∑ i ∈ range (2 * k + 1), (i + 1) / ∑ j ∈ range (i + 1), a j ≤ 4 * ∑ i ∈ range k, (a i)⁻¹ := by
  induction k, hk using Nat.le_induction with
  | base =>
    split_ands
    · -- We do not have strict inequality if all `a i` are equal.
      calc _
      _ = ∑ i ∈ range 4, (i + 1) / ∑ j ∈ range (i + 1), a j := by simp
      _ ≤ ∑ i ∈ range 4, (a 0)⁻¹ := sum_le_sum fun i hi ↦ lemma_a a ha_pos ha_mono i
      _ = _ := by simp

    · -- It is just as easy to show strict inequality for the odd case.
      refine le_of_lt ?_
      calc _
      _ = ∑ i ∈ range 5, (i + 1) / ∑ j ∈ range (i + 1), a j := by simp
      _ = ∑ i ∈ insert 1 ((range 5).erase 1), (i + 1) / ∑ j ∈ range (i + 1), a j := by simp
      _ < 4 / a 0 + 4 / a 1 := by
        rw [Finset.sum_insert (by simp), add_comm]
        refine add_lt_add_of_le_of_lt ?_ ?_
        · calc _
          _ ≤ ∑ i ∈ (range 5).erase 1, (a 0)⁻¹ := sum_le_sum fun i _ ↦ lemma_a a ha_pos ha_mono i
          _ = _ := by simp [div_eq_mul_inv]
        · refine div_lt_div₀ ?_ ?_ zero_le_four (ha_pos 1)
          · norm_num
          · simpa [sum_range_succ] using (ha_pos 0).le
      _ = 4 * ((a 0)⁻¹ + (a 1)⁻¹) := by ring
      _ = _ := by simp [sum_range_succ]

  | succ k hk IH =>
    sorry


theorem inequalities_127824 {n : ℕ} (hn_pos : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    ∑ i, i / (∑ j ≤ i, a j) < 4 * ∑ i, (a i)⁻¹ := by

  -- TODO: clear `n` too?
  revert a
  suffices ∀ l : List ℝ, (∀ x ∈ l, 0 < x) → l.length = n →
      ∑ i ∈ range n, i / (l.take (i + 1)).sum < 4 * (l.map (·⁻¹)).sum by
    intro a ha
    convert this ((List.finRange n).map a) (by simpa) (by simp)
    · sorry
    · sorry

  -- TODO: remove `n` too?
  intro l hl_pos hl_len

  wlog h_sorted : l.Sorted (· ≤ ·) generalizing l
  · have hl_nil : l ≠ [] := by
      refine List.ne_nil_of_length_pos ?_
      exact hl_len ▸ hn_pos

    let s := l.insertionSort (· ≤ ·)
    have hs_perm : s ~ l := l.perm_insertionSort (· ≤ ·)
    have hs_sorted : s.Sorted (· ≤ ·) := l.sorted_insertionSort (· ≤ ·)

    calc _
    _ ≤ ∑ i ∈ range n, i / (s.take (i + 1)).sum := by
      refine sum_le_sum fun i hi ↦ ?_
      refine div_le_div_of_nonneg_left (by simp) ?_ ?_
      · refine List.sum_pos _ ?_ ?_
        · refine fun x hx ↦ hl_pos x ?_
          rw [← hs_perm.mem_iff]
          exact List.mem_of_mem_take hx
        · suffices s ≠ [] by simpa
          refine mt ?_ hl_nil
          intro hs
          simpa [hs] using hs_perm
      -- Use the lemma for the first `n` elements having lesser sum than any other `n` elements.
      refine subperm_sum_take_le_sum_take_of_sorted hs_perm.symm.subperm hs_sorted ?_
      linarith [List.mem_range.mp hi]

    _ < 4 * (s.map fun x ↦ x⁻¹).sum := by
      refine this s ?_ ?_ ?_
      · exact fun x hx ↦ hl_pos x (hs_perm.mem_iff.mp hx)
      · exact hs_perm.length_eq ▸ hl_len
      · exact hs_sorted
    _ = 4 * (l.map (·⁻¹)).sum := by rw [(hs_perm.map fun x ↦ x⁻¹).sum_eq]


  sorry

  -- suffices ∀ n, 4 ≤ n →
  --     ∀ k, n = 2 * (k + 1) → ∑ i ∈ range n, i / ∑ j ≤ i, a i < 4 * ∑ i < , (a i)⁻¹ by
