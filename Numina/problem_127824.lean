-- https://cloud.kili-technology.com/label/projects/label/cmcbouv7300n3ueaxzr2tyxwi

import Mathlib

namespace problem_127824

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

lemma subperm_sum_take_len_le_sum_of_sorted {s l : List ℝ} (hsl : s <+~ l) (hl : l.Sorted (· ≤ ·)) :
    (l.take s.length).sum ≤ s.sum := by
  rcases hsl with ⟨t, hts, htl⟩
  convert sublist_sum_take_len_le_sum_of_sorted htl hl using 1
  · rw [hts.length_eq]
  · rw [hts.sum_eq]

lemma subperm_sum_take_le_sum_take_of_sorted {s l : List ℝ} (hsl : s <+~ l) (hl : l.Sorted (· ≤ ·))
    (n : ℕ) (hn : n ≤ s.length) :
    (l.take n).sum ≤ (s.take n).sum := by
  convert subperm_sum_take_len_le_sum_of_sorted ((s.take_sublist n).subperm.trans hsl) hl
  simpa using hn

-- Rewrite `finRange` in terms of `List.range`.
lemma finRange_eq_map_coe_range (n : ℕ) :
    List.finRange (n + 1) = List.map (↑) (List.range (n + 1)) := by
  refine Fin.val_injective.list_map ?_
  calc _
  _ = List.map id (List.range (n + 1)) := by simp
  _ = _ := by
    rw [List.map_map, List.map_inj_left]
    intro i hi
    refine (Fin.val_cast_of_lt ?_).symm
    exact (List.mem_range.mp hi)

-- The sum over `Iic i` of a function on `Fin n` can be rewritten as a `List.sum`.
lemma sum_Iic_eq_sum_take_ofFn {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℝ) (i : Fin n) :
    ∑ j ≤ i, a j = (List.take (i + 1) (List.ofFn a)).sum := by
  cases n with
  | zero => contradiction
  | succ n =>
    calc _
    -- Rewrite as a sum over `List.range (i + 1)`.
    _ = ∑ j ∈ map Fin.valEmbedding (Iic i), a j := by
      rw [sum_map]
      simp
    _ = ∑ j ∈ (List.range (i + 1)).toFinset, a j := by
      congr
      ext j
      simp [Nat.lt_add_one_iff]
    _ = (List.map a (List.map (↑) (List.range (i + 1)))).sum := by
      rw [List.sum_toFinset _ (List.nodup_range _)]
      simp [Function.comp_def]
    -- Rewrite as a sum over `List.take` of `List.finRange`.
    _ = (List.map a (List.take (i + 1) (List.finRange (n + 1)))).sum := by
      rw [finRange_eq_map_coe_range, ← List.map_take, List.take_range]
      congr
      simpa using Fin.is_le i
    _ = _ := by
      rw [List.ofFn_eq_map]
      simp

-- For `a` increasing, each terms is bounded above by the inverse of the smallest term.
-- Here we consider `a : ℕ → ℝ` instead of `Fin (n + 1) → ℝ` to simplify the proof.
lemma lemma_1 (a : ℕ → ℝ) (ha_pos : ∀ i, 0 < a i) (ha_mono : Monotone a) (i : ℕ) :
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

-- Specialize the lemma above for `a` defined on `Fin (n + 1)`.
lemma lemma_1_fin (n : ℕ) (a : Fin (n + 1) → ℝ) (ha_pos : ∀ i, 0 < a i) (ha_mono : Monotone a)
    (i : Fin (n + 1)) :
    (i + 1 : ℕ) / ∑ j ≤ i, a j ≤ (a 0)⁻¹ := by
  let f (i : ℕ) : Fin (n + 1) := ⟨i ⊓ n, Nat.lt_add_one_of_le inf_le_right⟩
  have hf_apply_val (i : Fin (n + 1)) : f (i : ℕ) = i :=
    Fin.val_inj.mp (min_eq_left (Fin.is_le i))
  convert lemma_1 (a ∘ f) ?_ ?_ i
  · simp
  · calc _
    _ = ∑ j ∈ map Fin.valEmbedding (Iic i), a (f j) := by
      rw [sum_map]
      simp [hf_apply_val]
    _ = _ := by
      congr
      ext j
      simp [Nat.lt_add_one_iff]
  · simp [f]
  · exact fun i ↦ ha_pos (f i)
  · exact ha_mono.comp fun i j h ↦ inf_le_inf_right n h

-- The inductive hypothesis for `2 ≤ n`.
-- Here we consider `a : ℕ → ℝ` instead of `Fin (n + 1) → ℝ` to simplify the proof.
lemma lemma_2 (a : ℕ → ℝ) (ha_pos : ∀ i, 0 < a i) (ha_mono : Monotone a) (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ range (n + 1), ↑(i + 1) / ∑ j ∈ range (i + 1), a j ≤
      4 * ∑ i ∈ range (n / 2), (a i)⁻¹ := by
  -- Replace `n` with `n + 2` for the first two steps.
  rw [le_iff_exists_add'] at hn
  rcases hn with ⟨n, rfl⟩
  induction n using Nat.twoStepInduction with
  | zero =>
    refine le_of_lt ?_
    calc _
    _ = ∑ x ∈ range 3, (↑x + 1) / ∑ j ∈ range (x + 1), a j := by simp
    _ ≤ ∑ i ∈ range 3, 1 / a 0 := by
      refine sum_le_sum fun i hi ↦ ?_
      refine (div_le_div_iff₀ ?_ (ha_pos 0)).mpr ?_
      · exact sum_pos (fun i hi ↦ ha_pos i) nonempty_range_succ
      calc _
      _ = ∑ _ ∈ range (i + 1), a 0 := by simp
      _ ≤ ∑ j ∈ range (i + 1), a j := sum_le_sum fun j hj ↦ ha_mono j.zero_le
      _ = _ := by simp
    _ = 3 * (a 0)⁻¹ := by simp
    _ < 4 * (a 0)⁻¹ := by
      refine (mul_lt_mul_iff_of_pos_right ?_).mpr ?_
      · simpa using ha_pos 0
      · norm_num
    _ = _ := by simp

  | one =>
    simp
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

  | more n IH₀ IH₁ =>
    clear IH₁
    -- Whether `n` is even or odd, we get 2 terms on the left, 1 term on the right.
    change ∑ i ∈ range (n + 2 + 1 + 2), _ ≤ 4 * ∑ i ∈ range ((n + 2 + 2) / 2), _
    rw [sum_range_add _ (n + 2 + 1) 2]
    rw [Nat.add_div_right (n + 2) two_pos, sum_range_add _ ((n + 2) / 2) 1, mul_add]
    refine add_le_add IH₀ ?_
    clear IH₀
    -- Return from `n + 2` to general `k`.
    generalize n + 2 = k
    suffices ↑(k + 2) / ∑ x ∈ range (k + 2), a x + ↑(k + 3) / ∑ x ∈ range (k + 3), a x ≤
        4 * (a (k / 2))⁻¹ by
      simpa [sum_range_succ _ 1, add_assoc, -Nat.cast_add]

    cases k.even_or_odd with
    | inl h_even =>
      rw [even_iff_exists_two_mul] at h_even
      rcases h_even with ⟨m, hm⟩
      rw [hm, Nat.mul_div_cancel_left _ two_pos]
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
      rw [hm, Nat.mul_add_div two_pos]
      simp only [add_assoc, Nat.reduceAdd, Nat.reduceDiv, add_zero]
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

-- Specialize the inductive hypothesis to a function defined on `Fin (n + 1)`.
lemma lemma_2_fin (n : ℕ) (hn : 2 ≤ n) (a : Fin (n + 1) → ℝ) (ha_pos : ∀ i, 0 < a i)
    (ha_mono : Monotone a) :
    ∑ i : Fin (n + 1), (i + 1 : ℕ) / ∑ j ≤ i, a j ≤ 4 * ∑ i < (Fin.last n) / 2, (a i)⁻¹ := by
  let f (i : ℕ) : Fin (n + 1) := ⟨i ⊓ n, Nat.lt_add_one_of_le inf_le_right⟩
  have hf_apply_val (i : Fin (n + 1)) : f (i : ℕ) = i :=
    Fin.val_inj.mp (min_eq_left (Fin.is_le i))
  convert lemma_2 (a ∘ f) ?_ ?_ n hn
  · rw [sum_range]
    refine sum_congr rfl fun i _ ↦ ?_
    congr 1
    calc _
    _ = ∑ j ∈ (Iic i).map Fin.valEmbedding, a (f j) := by
      rw [sum_map]
      refine sum_congr rfl fun j hj ↦ ?_
      simp [hf_apply_val]
    _ = _ := by
      congr
      ext j
      simp [Nat.lt_add_one_iff]
  · calc _
    _ = ∑ j ∈ (Iio (Fin.last n / 2)).map Fin.valEmbedding, (a (f j))⁻¹ := by
      rw [sum_map]
      simp [hf_apply_val]
    _ = _ := by
      congr
      ext j
      suffices ((2 : Fin (n + 1)) : ℕ) = 2 by simp [this]
      rw [Fin.coe_ofNat_eq_mod]
      refine Nat.mod_eq_of_lt (by linarith)
  · exact fun i ↦ ha_pos (f i)
  · exact ha_mono.comp fun i j h ↦ inf_le_inf_right n h

theorem inequalities_127824 {n : ℕ} (hn_pos : 0 < n) (a : Fin n → ℝ) (ha_pos : ∀ i, 0 < a i) :
    ∑ i : Fin n, (i + 1 : ℕ) / (∑ j ≤ i, a j) < 4 * ∑ i, (a i)⁻¹ := by
  -- We can assume that `i ≤ j → a i ≤ a j` since, otherwise, we could bound the left above using
  -- the sorted sequence (and the right would be unchanged).
  -- Convert the sum over `Iic i` into a `List.take` expression.
  simp only [sum_Iic_eq_sum_take_ofFn hn_pos.ne']
  wlog ha_mono : Monotone a generalizing a
  · -- Construct a function `b : Fin n → ℝ` which is a sorted version of `a`.
    let l := List.ofFn a
    let s := l.insertionSort (· ≤ ·)
    have hl_len : l.length = n := by simp [l]
    have hs_len : s.length = n := by simp [s, l]
    have hl_nil : l ≠ [] := List.ne_nil_of_length_pos (by simpa [hl_len])
    have hl_pos : ∀ x ∈ l, 0 < x := by simpa [l] using ha_pos
    have hs_perm : s ~ l := l.perm_insertionSort _
    have hs_sorted : s.Sorted (· ≤ ·) := l.sorted_insertionSort _
    have hb : ∃ b : Fin n → ℝ, List.ofFn b = s := hs_len ▸ ⟨_, s.ofFn_get⟩
    rcases hb with ⟨b, hb⟩
    calc _
    -- Since the partial sum is bounded below, its inverse is bounded above.
    _ ≤ ∑ i : Fin n, (i + 1 : ℕ) / (s.take (i + 1)).sum := by
      refine sum_le_sum fun i hi ↦ ?_
      refine div_le_div_of_nonneg_left (by linarith) ?_ ?_
      · refine List.sum_pos _ ?_ ?_
        · refine fun x hx ↦ hl_pos x ?_
          refine hs_perm.mem_iff.mp ?_
          exact List.mem_of_mem_take hx
        · suffices s ≠ [] by simpa
          refine mt ?_ hl_nil
          intro hs
          simpa [hs] using hs_perm
      refine subperm_sum_take_le_sum_take_of_sorted hs_perm.symm.subperm hs_sorted (i + 1) ?_
      rw [hl_len]
      exact i.isLt
    -- Apply the lemma to the sorted list `b`.
    _ = ∑ i : Fin n, (i + 1 : ℕ) / ((List.ofFn b).take (i + 1)).sum := by rw [hb]
    _ < 4 * ∑ i, (b i)⁻¹ := by
      refine this b ?_ ?_
      · rw [← List.forall_mem_ofFn_iff, hb]
        refine fun x hx ↦ hl_pos x ?_
        exact hs_perm.mem_iff.mp hx
      · rw [← List.sorted_le_ofFn_iff, hb]
        exact hs_sorted
    -- Use the fact that the lists have equal sum since one is a permutation of the other.
    _ = 4 * ∑ i : Fin n, (a i)⁻¹ := by
      congr 1
      convert (hs_perm.map fun x ↦ x⁻¹).sum_eq using 1
      · simp [← hb, List.sum_ofFn]
      · simp [l, List.sum_ofFn]

  -- Switch back to the `Iic i` form.
  simp only [← sum_Iic_eq_sum_take_ofFn hn_pos.ne']
  -- For `n < 4`, the equation is trivially satisfied using the first term.
  cases lt_or_le n 4 with
  | inl hn =>
    obtain ⟨n, rfl⟩ : ∃ m, m + 1 = n := Nat.exists_add_one_eq.mpr hn_pos
    calc _
    _ ≤ ∑ i : Fin (n + 1), (a 0)⁻¹ := sum_le_sum fun i hi ↦ lemma_1_fin _ a ha_pos ha_mono i
    -- Bound above using just the first term of the sum.
    _ = (n + 1) * (a 0)⁻¹ := by simp
    _ < 4 * (a 0)⁻¹ := by
      refine (mul_lt_mul_iff_of_pos_right ?_).mpr ?_
      · exact inv_pos_of_pos (ha_pos 0)
      · suffices ↑(n + 1) < ((4 : ℕ) : ℝ) by simpa
        exact Nat.cast_lt.mpr hn
    _ ≤ 4 * (a 0)⁻¹ + 4 * ∑ i : Fin n, (a i.succ)⁻¹ := by
      suffices 0 ≤ ∑ i : Fin n, (a i.succ)⁻¹ by simpa
      exact sum_nonneg fun i hi ↦ (inv_pos_of_pos <| ha_pos i.succ).le
    _ = 4 * ∑ i : Fin (n + 1), (a i)⁻¹ := by
      rw [Fin.sum_univ_succ]
      ring

  | inr hn =>
    cases n with
    | zero => contradiction
    | succ n =>
      -- Apply the inductive hypothesis using monotonicity.
      calc _
      _ ≤ 4 * ∑ i ∈ Iio (Fin.last n / 2), (a i)⁻¹ := lemma_2_fin n (by linarith) a ha_pos ha_mono
      _ < 4 * ∑ i : Fin (n + 1), (a i)⁻¹ := by
        gcongr
        -- Use the n-th element to establish strict inequality.
        refine sum_lt_sum_of_subset (subset_univ _) (mem_univ _) ?_ (inv_pos_of_pos (ha_pos n))
          fun i hi _ ↦ (inv_pos_of_pos (ha_pos i)).le
        simp [Fin.le_last]

end problem_127824
