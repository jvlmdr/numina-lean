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

theorem inequalities_127824 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    ∑ i, i / (∑ j ≤ i, a j) < 4 * ∑ i, (a i)⁻¹ := by

  -- TODO: clear `n` too?
  revert a
  suffices ∀ l : List ℝ, (∀ x ∈ l, 0 < x) → l.length = n →
      ∑ i ∈ range n, i / (l.take (i + 1)).sum < 4 * (l.map (·⁻¹)).sum by
    intro a ha
    convert this ((List.finRange n).map a) (by simpa) (by simp)
    · sorry
    · sorry

  intro l hl_pos hl_len

  wlog h_sorted : l.Sorted (· ≤ ·) generalizing l
  · have hl_nil : l ≠ [] := by
      refine List.ne_nil_of_length_pos ?_
      exact hl_len ▸ hn

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
