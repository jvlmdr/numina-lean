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

-- -- TODO: can we use `range ⌊(k - 1) / 2⌋₊` and unify?
-- lemma lemma_b' (a : ℕ → ℝ) (ha_pos : ∀ i, 0 < a i) (ha_mono : Monotone a) (k : ℕ) (hk : 2 ≤ k) :
--     ∑ i ∈ range (2 * k), (i + 1) / ∑ j ∈ range (i + 1), a j ≤ 4 * ∑ i ∈ range (k - 1), (a i)⁻¹ ∧
--     ∑ i ∈ range (2 * k + 1), (i + 1) / ∑ j ∈ range (i + 1), a j ≤ 4 * ∑ i ∈ range k, (a i)⁻¹ := by
--   induction k, hk using Nat.le_induction with
--   | base =>
--     split_ands
--     · -- We do not have strict inequality if all `a i` are equal.
--       calc _
--       _ = ∑ i ∈ range 4, (i + 1) / ∑ j ∈ range (i + 1), a j := by simp
--       _ ≤ ∑ i ∈ range 4, (a 0)⁻¹ := sum_le_sum fun i hi ↦ lemma_a a ha_pos ha_mono i
--       _ = _ := by simp

--     · -- It is just as easy to show strict inequality for the odd case.
--       refine le_of_lt ?_
--       calc _
--       _ = ∑ i ∈ range 5, (i + 1) / ∑ j ∈ range (i + 1), a j := by simp
--       _ = ∑ i ∈ insert 1 ((range 5).erase 1), (i + 1) / ∑ j ∈ range (i + 1), a j := by simp
--       _ < 4 / a 0 + 4 / a 1 := by
--         rw [Finset.sum_insert (by simp), add_comm]
--         refine add_lt_add_of_le_of_lt ?_ ?_
--         · calc _
--           _ ≤ ∑ i ∈ (range 5).erase 1, (a 0)⁻¹ := sum_le_sum fun i _ ↦ lemma_a a ha_pos ha_mono i
--           _ = _ := by simp [div_eq_mul_inv]
--         · refine div_lt_div₀ ?_ ?_ zero_le_four (ha_pos 1)
--           · norm_num
--           · simpa [sum_range_succ] using (ha_pos 0).le
--       _ = 4 * ((a 0)⁻¹ + (a 1)⁻¹) := by ring
--       _ = _ := by simp [sum_range_succ]

--   | succ k hk IH =>
--     split_ands
--     · suffices (2 * k + 1) / ∑ j ∈ range (2 * k + 1), a j +
--           (2 * k + 2) / ∑ j ∈ range (2 * k + 2), a j ≤ 4 * (a (k - 1))⁻¹ by
--         calc _
--         -- Break out two terms from the left sum.
--         _ = ∑ i ∈ range (2 * k), (i + 1) / ∑ j ∈ range (i + 1), a j +
--             ((2 * k + 1) / ∑ j ∈ range (2 * k + 1), a j +
--             (2 * k + 2) / ∑ j ∈ range (2 * k + 2), a j) := by
--           simp [mul_add, sum_range_succ, add_assoc, one_add_one_eq_two]
--         -- Apply the inductive hypothesis and the bound for the two terms.
--         _ ≤ 4 * ∑ i ∈ range (k - 1), (a i)⁻¹ + 4 * (a (k - 1))⁻¹ := add_le_add IH.1 this
--         -- Break out one term from the right sum.
--         _ ≤ 4 * ∑ i ∈ range (k - 1 + 1), (a i)⁻¹ := by simp [sum_range_succ, mul_add]
--         _ = _ := by
--           suffices 1 ≤ k by simp [this]
--           linarith

--       calc _
--       _ ≤ (2 * k + 1) / ((k + 2) * a (k - 1)) + (2 * k + 2) / ((k + 3) * a (k - 1)) := by
--         refine add_le_add ?_ ?_
--         · refine div_le_div_of_nonneg_left (by linarith) ?_ ?_
--           · exact mul_pos (by linarith) (ha_pos (k - 1))
--           calc _
--           _ = ∑ j ∈ Ico (k - 1) (2 * k + 1), a (k - 1) := by
--             rw [sum_const, nsmul_eq_mul, Nat.card_Ico]
--             congr
--             -- TODO: simplify?
--             rw [Nat.cast_sub (Nat.sub_le_of_le_add (by linarith))]
--             rw [Nat.cast_sub (by linarith)]
--             simp only [Nat.cast_add, Nat.cast_mul]
--             ring
--           _ ≤ ∑ j ∈ Ico (k - 1) (2 * k + 1), a j :=
--             sum_le_sum fun i hi ↦ ha_mono (mem_Ico.mp hi).1
--           _ ≤ ∑ j ∈ Ico 0 (2 * k + 1), a j :=
--             sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_left (by linarith))
--               fun i hi hi' ↦ (ha_pos i).le
--           _ = _ := by simp

--         · refine div_le_div_of_nonneg_left (by linarith) ?_ ?_
--           · exact mul_pos (by linarith) (ha_pos (k - 1))
--           calc _
--           _ = ∑ j ∈ Ico (k - 1) (2 * k + 2), a (k - 1) := by
--             rw [sum_const, nsmul_eq_mul, Nat.card_Ico]
--             congr
--             -- TODO: simplify?
--             rw [Nat.cast_sub (Nat.sub_le_of_le_add (by linarith))]
--             rw [Nat.cast_sub (by linarith)]
--             simp only [Nat.cast_add, Nat.cast_mul]
--             ring
--           _ ≤ ∑ j ∈ Ico (k - 1) (2 * k + 2), a j :=
--             sum_le_sum fun i hi ↦ ha_mono (mem_Ico.mp hi).1
--           _ ≤ ∑ j ∈ Ico 0 (2 * k + 2), a j :=
--             sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico_left (by linarith))
--               fun i hi hi' ↦ (ha_pos i).le
--           _ = _ := by simp

--       _ = (2 * ((k + 2⁻¹) / (k + 2)) + 2 * ((k + 1) / (k + 3))) * (a (k - 1))⁻¹ := by
--         simp only [← div_div]
--         ring
--       _ ≤ (2 + 2) * (a (k - 1))⁻¹ := by
--         refine mul_le_mul_of_nonneg_right ?_ (inv_pos_of_pos <| ha_pos (k - 1)).le
--         refine add_le_add ?_ ?_ <;> rw [mul_le_iff_le_one_right, div_le_one₀] <;> linarith
--       _ = _ := by rw [two_add_two_eq_four]

--     · suffices (2 * k + 2) / ∑ j ∈ range (2 * k + 2), a j +
--           (2 * k + 3) / ∑ j ∈ range (2 * k + 3), a j ≤ 4 * (a k)⁻¹ by
--         calc _
--         -- Break out two terms from the left sum.
--         _ = ∑ i ∈ range ((2 * k + 1) + 2), (i + 1) / ∑ j ∈ range (i + 1), a j := by simp [mul_add]
--         _ = ∑ i ∈ range (2 * k + 1), (i + 1) / ∑ j ∈ range (i + 1), a j +
--             ((2 * k + 2) / ∑ j ∈ range (2 * k + 2), a j +
--             (2 * k + 3) / ∑ j ∈ range (2 * k + 3), a j) := by
--           simp [sum_range_succ, add_assoc, ← one_add_one_eq_two, ← two_add_one_eq_three]
--         -- Apply the inductive hypothesis and the bound for the two terms.
--         _ ≤ 4 * ∑ i ∈ range k, (a i)⁻¹ + 4 * (a k)⁻¹ := add_le_add IH.2 this
--         -- Break out one term from the right sum.
--         _ ≤ 4 * ∑ i ∈ range (k + 1), (a i)⁻¹ := by simp [sum_range_succ, mul_add]

--       calc _
--       _ ≤ (2 * k + 2) / ((k + 1) * a k) + (2 * k + 3) / ((k + 2) * a k) := by
--         refine add_le_add ?_ ?_
--         · refine div_le_div_of_nonneg_left (by linarith) ?_ ?_
--           · exact mul_pos (by linarith) (ha_pos k)
--           calc _
--           _ = ∑ j ∈ Ico (k + 1) (2 * (k + 1)), a k := by simp [two_mul]
--           _ = ∑ j ∈ Ico (k + 1) (2 * k + 2), a k := by simp [mul_add]
--           _ ≤ ∑ j ∈ Ico (k + 1) (2 * k + 2), a j := by
--             refine sum_le_sum fun i hi ↦ ha_mono ?_
--             simp only [mem_Ico] at hi
--             linarith
--           _ ≤ _ := by
--             refine sum_le_sum_of_subset_of_nonneg ?_ fun i hi hi' ↦ (ha_pos i).le
--             intro x
--             simp

--         · refine div_le_div_of_nonneg_left ?_ ?_ ?_
--           · linarith
--           · exact mul_pos (by linarith) (ha_pos k)
--           calc _
--           _ = ∑ j ∈ Ico (k + 1) (2 * k + 3), a k := by
--             suffices (k + 2 : ℝ) = ↑(2 * k + 2 - k) by simp [this]
--             rw [Nat.cast_sub (by linarith)]
--             simp only [Nat.cast_add, Nat.cast_mul]
--             ring

--           _ ≤ ∑ j ∈ Ico (k + 1) (2 * k + 3), a j := by
--             refine sum_le_sum fun i hi ↦ ha_mono ?_
--             linarith [mem_Ico.mp hi]
--           _ ≤ _ :=
--             sum_le_sum_of_subset_of_nonneg (fun i ↦ by simp) fun i hi hi' ↦ (ha_pos i).le

--       _ = (2 * ((k + 1) / (k + 1)) + 2 * ((k + 3 / 2) / (k + 2))) * (a k)⁻¹ := by
--         simp only [← div_div]
--         ring
--       _ ≤ (2 + 2) * (a k)⁻¹ := by
--         refine mul_le_mul_of_nonneg_right ?_ (inv_pos_of_pos <| ha_pos k).le
--         refine add_le_add ?_ ?_ <;> rw [mul_le_iff_le_one_right, div_le_one₀] <;> linarith
--       _ = _ := by rw [two_add_two_eq_four]


-- TODO: replace with `n + 1` to avoid `n - 1`?
lemma lemma_b (a : ℕ → ℝ) (ha_pos : ∀ i, 0 < a i) (ha_mono : Monotone a) (n : ℕ) (hn : 4 ≤ n) :
    ∑ i ∈ range n, ↑(i + 1) / ∑ j ∈ range (i + 1), a j ≤
      4 * ∑ i ∈ range ((n - 1) / 2), (a i)⁻¹ := by

  rw [le_iff_exists_add'] at hn
  rcases hn with ⟨n, rfl⟩
  simp only [Nat.add_one_sub_one]

  -- Replace `n + 4` with `n + 3 + 1`.
  change ∑ i ∈ range (n + 3 + 1), _ ≤ _

  induction n using Nat.twoStepInduction with
  | zero =>
    -- suffices ∑ i ∈ range 4, ↑(i + 1) / ∑ j ∈ range (i + 1), a j ≤ 4 * (a 0)⁻¹ by simpa
    calc _
    _ = ∑ i ∈ range 4, ↑(i + 1) / ∑ j ∈ range (i + 1), a j := by simp
    _ ≤ ∑ i ∈ range 4, 1 / a 0 := by
      refine sum_le_sum fun i hi ↦ ?_
      refine (div_le_div_iff₀ ?_ (ha_pos 0)).mpr ?_
      · exact sum_pos (fun i hi ↦ ha_pos i) nonempty_range_succ
      calc _
      _ = ∑ _ ∈ range (i + 1), a 0 := by simp
      _ ≤ ∑ j ∈ range (i + 1), a j := sum_le_sum fun j hj ↦ ha_mono j.zero_le
      _ = _ := by simp
    _ = _ := by simp

  | one =>
    simp
    sorry

  | more n IH₀ IH₁ =>
    clear IH₁
    -- Whether `n` is even or odd, we get 2 terms on the left, 1 term on the right.
    change ∑ i ∈ range (n + 3 + 1 + 2), _ ≤ 4 * ∑ i ∈ range ((n + 3 + 2) / 2), _
    rw [Nat.add_div_right _ two_pos]
    rw [sum_range_add _ (n + 3 + 1) 2, sum_range_add _ ((n + 3) / 2) 1, mul_add]

    refine add_le_add IH₀ ?_
    clear IH₀

    simp [sum_range_add _ 1 1, -Nat.cast_add, -Nat.cast_mul]  -- TODO (have simp below)

    -- TODO: check that we need to handle `n = 5` separately
    cases (n + 3).even_or_odd with
    | inl h_even =>
      rw [even_iff_exists_two_mul] at h_even
      rcases h_even with ⟨m, hm⟩
      simp [hm, add_assoc, -Nat.cast_add, -Nat.cast_mul]  -- TODO
      calc _
      -- Bound each sum below using the occurrences of `a m` to bound each fraction above.
      _ ≤ ↑(2 * m + 2) / (↑(m + 2) * a m) + ↑(2 * m + 3) / (↑(m + 3) * a m) := by
        refine add_le_add ?_ ?_
        · refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) ?_ ?_
          · exact mul_pos (Nat.cast_pos.mpr <| by simp) (ha_pos m)
          calc _
          _ = ∑ i ∈ Ico m (m + 2 + m), a m := by simp
          _ = ∑ i ∈ Ico m (2 * m + 2), a m := by congr 2; ring
          _ ≤ ∑ i ∈ Ico m (2 * m + 2), a i := sum_le_sum fun i hi ↦ ha_mono (mem_Ico.mp hi).1
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun i ↦ by simp) fun i hi _ ↦ (ha_pos i).le
        · refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) ?_ ?_
          · exact mul_pos (Nat.cast_pos.mpr <| by simp) (ha_pos m)
          calc _
          _ = ∑ i ∈ Ico m (m + 3 + m), a m := by simp
          _ = ∑ i ∈ Ico m (2 * m + 3), a m := by congr 2; ring
          _ ≤ ∑ i ∈ Ico m (2 * m + 3), a i := sum_le_sum fun i hi ↦ ha_mono (mem_Ico.mp hi).1
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun i ↦ by simp) fun i hi _ ↦ (ha_pos i).le
      -- Factor out `2 / a m` and show that each coefficient is `≤ 1`.
      _ = 2 * (a m)⁻¹ * ((m + 1) / (m + 2) + (m + 3 / 2) / (m + 3)) := by
        simp only [Nat.cast_add, Nat.cast_mul, ← div_div]
        ring
      _ ≤ 2 * (a m)⁻¹ * (1 + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by simpa using (ha_pos m).le)
        refine add_le_add ?_ ?_ <;> rw [div_le_one₀] <;> linarith
      _ = _ := by ring

    | inr h_odd =>
      rcases h_odd with ⟨m, hm⟩
      simp [hm, add_assoc, -Nat.cast_add, -Nat.cast_mul, Nat.mul_add_div]  -- TODO
      calc _
      -- Bound each sum below using the occurrences of `a m` to bound each fraction above.
      _ ≤ ↑(2 * m + 3) / (↑(m + 3) * a m) + ↑(2 * m + 4) / (↑(m + 4) * a m) := by
        refine add_le_add ?_ ?_
        · refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) ?_ ?_
          · exact mul_pos (Nat.cast_pos.mpr <| by simp) (ha_pos m)
          calc _
          _ = ∑ i ∈ Ico m (m + 3 + m), a m := by simp
          _ = ∑ i ∈ Ico m (2 * m + 3), a m := by congr 2; ring
          _ ≤ ∑ i ∈ Ico m (2 * m + 3), a i := sum_le_sum fun i hi ↦ ha_mono (mem_Ico.mp hi).1
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun i ↦ by simp) fun i hi _ ↦ (ha_pos i).le
        · refine div_le_div_of_nonneg_left (Nat.cast_nonneg _) ?_ ?_
          · exact mul_pos (Nat.cast_pos.mpr <| by simp) (ha_pos m)
          calc _
          _ = ∑ i ∈ Ico m (m + 4 + m), a m := by simp
          _ = ∑ i ∈ Ico m (2 * m + 4), a m := by congr 2; ring
          _ ≤ ∑ i ∈ Ico m (2 * m + 4), a i := sum_le_sum fun i hi ↦ ha_mono (mem_Ico.mp hi).1
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun i ↦ by simp) fun i hi _ ↦ (ha_pos i).le
      -- Factor out `2 / a m` and show that each coefficient is `≤ 1`.
      _ = 2 * (a m)⁻¹ * ((m + 3 / 2) / (m + 3) + (m + 2) / (m + 4)) := by
        simp only [Nat.cast_add, Nat.cast_mul, ← div_div]
        ring
      _ ≤ 2 * (a m)⁻¹ * (1 + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by simpa using (ha_pos m).le)
        refine add_le_add ?_ ?_ <;> rw [div_le_one₀] <;> linarith
      _ = _ := by ring


theorem inequalities_127824 {n : ℕ} (hn_pos : 0 < n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    ∑ i, (i + 1) / (∑ j ≤ i, a j) < 4 * ∑ i, (a i)⁻¹ := by

  -- TODO: clear `n` too?
  revert a
  suffices ∀ l : List ℝ, (∀ x ∈ l, 0 < x) → l.length = n →
      ∑ i ∈ range n, (i + 1) / (l.take (i + 1)).sum < 4 * (l.map (·⁻¹)).sum by
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
    _ ≤ ∑ i ∈ range n, (i + 1) / (s.take (i + 1)).sum := by
      refine sum_le_sum fun i hi ↦ ?_
      refine div_le_div_of_nonneg_left (by linarith) ?_ ?_
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

  revert l
  suffices ∀ (a : ℕ → ℝ), (∀ i, 0 < a i) → Monotone a →
      ∑ i ∈ range n, (i + 1) / (∑ j ∈ range (i + 1), a j) < 4 * ∑ i ∈ range n, (a i)⁻¹ by
    sorry

  intro a ha_pos ha_mono

  cases lt_or_le n 4 with
  | inl hn =>
    obtain ⟨n, rfl⟩ : ∃ m, m + 1 = n := Nat.exists_add_one_eq.mpr hn_pos
    calc _
    _ ≤ ∑ i ∈ range (n + 1), (a 0)⁻¹ := sum_le_sum fun i hi ↦ lemma_a a ha_pos ha_mono i
    _ = (n + 1) * (a 0)⁻¹ := by simp
    _ < 4 * (a 0)⁻¹ := by
      refine (mul_lt_mul_iff_of_pos_right ?_).mpr ?_
      · exact inv_pos_of_pos (ha_pos 0)
      · suffices ↑(n + 1) < ((4 : ℕ) : ℝ) by simpa
        exact Nat.cast_lt.mpr hn
    _ ≤ 4 * (a 0)⁻¹ + 4 * ∑ i ∈ range n, (a (i + 1))⁻¹ := by
      suffices 0 ≤ ∑ i ∈ range n, (a (i + 1))⁻¹ by simpa
      exact sum_nonneg fun i hi ↦ (inv_pos_of_pos <| ha_pos (i + 1)).le
    _ = _ := by
      rw [sum_range_succ']
      ring

  | inr hn =>
    cases n.even_or_odd with
    | inl hk =>
      obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := hk.exists_two_nsmul n
      refine lt_of_le_of_lt (lemma_b a ha_pos ha_mono k (by linarith)).1 ?_
      gcongr
      refine sum_lt_sum_of_subset (i := k) ?_ ?_ ?_ ?_ ?_
      · simp only [range_subset, tsub_le_iff_right]
        linarith
      · simp only [mem_range]
        linarith
      · simp
      · exact inv_pos_of_pos <| ha_pos k
      · exact fun j hj _ ↦ (inv_pos_of_pos <| ha_pos j).le
    | inr h =>
      obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := h
      refine lt_of_le_of_lt (lemma_b a ha_pos ha_mono k (by linarith)).2 ?_
      gcongr
      refine sum_lt_sum_of_subset (i := k) ?_ ?_ ?_ ?_ ?_
      · simp only [range_subset]
        linarith
      · simp only [mem_range]
        linarith
      · simp
      · exact inv_pos_of_pos <| ha_pos k
      · exact fun j hj _ ↦ (inv_pos_of_pos <| ha_pos j).le
