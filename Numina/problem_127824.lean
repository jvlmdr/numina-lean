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

lemma sum_Iic_eq_sum_take_ofFn {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℝ) (i : Fin n) :
    ∑ j ≤ i, a j = (List.take (i + 1) (List.ofFn a)).sum := by
  cases n with
  | zero => contradiction
  | succ n =>
    calc _
    _ = ∑ j ∈ map Fin.valEmbedding (Iic i), a j := by
      rw [sum_map]
      simp
    _ = ∑ j ∈ (List.range (i + 1)).toFinset, a j := by
      congr
      ext j
      simp [Nat.lt_add_one_iff]
    -- TODO: check whether this can be made more succinct
    _ = List.sum (.map (a ∘ (↑)) (.range (i + 1))) := List.sum_toFinset _ (List.nodup_range _)
    _ = List.sum (.map (a ∘ (↑)) (.take (i + 1) (.range (n + 1)))) := by
      rw [List.take_range]
      simp [Fin.is_le]
    _ = List.sum (.map (a ∘ (↑)) (.take (i + 1) (.map Fin.val (.finRange (n + 1))))) := by
      simp
    _ = List.sum (.take (i + 1) (.map a (.finRange (n + 1)))) := by
      rw [List.map_take, List.map_map]
      simp [Function.comp_def]
    _ = _ := by rw [List.ofFn_eq_map]

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

lemma lemma_a_fin (n : ℕ) (a : Fin (n + 1) → ℝ) (ha_pos : ∀ i, 0 < a i) (ha_mono : Monotone a)
    (i : Fin (n + 1)) :
    (i + 1 : ℕ) / ∑ j ≤ i, a j ≤ (a 0)⁻¹ := by
  let f (i : ℕ) : Fin (n + 1) := ⟨i ⊓ n, Nat.lt_add_one_of_le inf_le_right⟩
  have hf_apply_val (i : Fin (n + 1)) : f (i : ℕ) = i :=
    Fin.val_inj.mp (min_eq_left (Fin.is_le i))
  convert lemma_a (a ∘ f) ?_ ?_ i
  · simp
  · calc _
    _ = ∑ j ∈ map Fin.valEmbedding (Iic i), a j := by
      rw [sum_map]
      simp
    _ = ∑ j ≤ (i : ℕ), a j := by simp
    _ = ∑ j ∈ range (i + 1), a (f j) := by
      unfold f
      symm
      refine sum_congr ?_ ?_
      · ext j
        simp [Nat.lt_add_one_iff]
      · intro j hj
        congr
        have hjn : j < n + 1 := lt_of_le_of_lt (mem_Iic.mp hj) i.isLt
        calc _
        _ = j := min_eq_left (Nat.le_of_lt_succ hjn)
        _ = _ := (Nat.mod_eq_of_lt hjn).symm
  · simp [f]
  · exact fun i ↦ ha_pos (f i)
  · exact ha_mono.comp fun i j h ↦ inf_le_inf_right n h

lemma lemma_b (a : ℕ → ℝ) (ha_pos : ∀ i, 0 < a i) (ha_mono : Monotone a) (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ range (n + 1), ↑(i + 1) / ∑ j ∈ range (i + 1), a j ≤
      4 * ∑ i ∈ range (n / 2), (a i)⁻¹ := by
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

  | more n IH₀ IH₁ =>
    clear IH₁
    -- Whether `n` is even or odd, we get 2 terms on the left, 1 term on the right.
    change ∑ i ∈ range (n + 2 + 1 + 2), _ ≤ 4 * ∑ i ∈ range ((n + 2 + 2) / 2), _
    rw [sum_range_add _ (n + 2 + 1) 2]
    rw [Nat.add_div_right (n + 2) two_pos, sum_range_add _ ((n + 2) / 2) 1, mul_add]
    refine add_le_add IH₀ ?_
    clear IH₀
    -- Replace `n + 2` with general `n`.
    generalize n + 2 = k
    suffices ↑(k + 2) / ∑ x ∈ range (k + 2), a x + ↑(k + 3) / ∑ x ∈ range (k + 3), a x ≤
        4 * (a (k / 2))⁻¹ by
      simpa [sum_range_succ _ 1, add_assoc, -Nat.cast_add]

    cases k.even_or_odd with
    | inl h_even =>
      rw [even_iff_exists_two_mul] at h_even
      rcases h_even with ⟨m, hm⟩
      rw [hm]
      simp [add_assoc, -Nat.cast_add, -Nat.cast_mul]  -- TODO
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

lemma lemma_b_fin (n : ℕ) (hn : 2 ≤ n) (a : Fin (n + 1) → ℝ) (ha_pos : ∀ i, 0 < a i)
    (ha_mono : Monotone a) :
    ∑ i : Fin (n + 1), (i + 1 : ℕ) / ∑ j ≤ i, a j ≤ 4 * ∑ i < (Fin.last n) / 2, (a i)⁻¹ := by
  let f (i : ℕ) : Fin (n + 1) := ⟨i ⊓ n, Nat.lt_add_one_of_le inf_le_right⟩
  have hf_apply_val (i : Fin (n + 1)) : f (i : ℕ) = i :=
    Fin.val_inj.mp (min_eq_left (Fin.is_le i))

  convert lemma_b (a ∘ f) ?_ ?_ n hn
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

  simp only [sum_Iic_eq_sum_take_ofFn hn_pos.ne']

  wlog ha_mono : Monotone a generalizing a
  · let l := List.ofFn a
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
    _ = ∑ i : Fin n, (i + 1 : ℕ) / ((List.ofFn b).take (i + 1)).sum := by rw [hb]
    _ < 4 * ∑ i : Fin n, (b i)⁻¹ := by
      refine this b ?_ ?_
      · rw [← List.forall_mem_ofFn_iff]
        rw [hb]
        refine fun x hx ↦ hl_pos x ?_
        exact hs_perm.mem_iff.mp hx
      · rw [← List.sorted_le_ofFn_iff]
        rw [hb]
        exact hs_sorted
    _ = 4 * List.sum (.map (fun x ↦ x⁻¹) s) := by
      congr 1
      rw [← hb]
      simp [List.sum_ofFn]
    _ = 4 * List.sum (.map (fun x ↦ x⁻¹) l) := by
      congr 1
      exact (hs_perm.map _).sum_eq
    _ = _ := by
      unfold l
      congr 1
      simp [List.sum_ofFn]

  simp only [← sum_Iic_eq_sum_take_ofFn hn_pos.ne']

  cases lt_or_le n 4 with
  | inl hn =>
    obtain ⟨n, rfl⟩ : ∃ m, m + 1 = n := Nat.exists_add_one_eq.mpr hn_pos
    calc _
    _ ≤ ∑ i : Fin (n + 1), (a 0)⁻¹ := sum_le_sum fun i hi ↦ lemma_a_fin _ a ha_pos ha_mono i
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
    -- Replace `n` with `n + 1` to facilitate use of the lemma, which uses `n - 1`.
    cases n with
    | zero => contradiction
    | succ n =>
      calc _
      _ ≤ 4 * ∑ i ∈ Iio (Fin.last n / 2), (a i)⁻¹ := lemma_b_fin n (by linarith) a ha_pos ha_mono
      _ < _ := by
        gcongr
        refine sum_lt_sum_of_subset ?_ ?_ ?_ (inv_pos_of_pos (ha_pos n))
            fun i hi _ ↦ (inv_pos_of_pos (ha_pos i)).le
        · exact subset_univ _
        · exact mem_univ _
        · simp [Fin.le_last]
