-- https://cloud.kili-technology.com/label/projects/label/cm91j3x7x003jseaym8rsjnwu

import Mathlib

open Real

/- Find all pairs of positive integers $m$ and $n$ for which
$\sqrt{m^{2} - 4} < 2 \sqrt{n} - m < \sqrt{m^{2} - 2}$. -/

theorem inequalities_290058 :
    {(m, n) : ℕ × ℕ | 0 < m ∧ 0 < n ∧ (0 : ℝ) ≤ m^2 - 4 ∧
      2 * √n - m ∈ Set.Ioo √(m^2 - 4) √(m^2 - 2)} =
    {(m, n) : ℕ × ℕ | 2 ≤ m ∧ n = m^2 - 2} := by

  -- Isolate the condition that there is a unique `n = m^2 - 2` for each `m`.
  suffices ∀ m n : ℕ, 2 ≤ m → 0 < n →
      (2 * √n - m ∈ Set.Ioo √(m^2 - 4) √(m^2 - 2) ↔ n = m^2 - 2) by
    ext ⟨m, n⟩
    specialize this m n
    simp only [Set.mem_setOf_eq]
    calc _
    -- Show that `(0 : ℝ) ≤ m^2 - 4` is equivalent to `2 ≤ m`.
    _ ↔ 0 < m ∧ 0 < n ∧ 2 ≤ m ∧ 2 * √n - m ∈ Set.Ioo √(m^2 - 4) √(m^2 - 2) := by
      simp only [and_congr_right_iff, and_congr_left_iff]
      intro hm hn _
      calc _
      _ ↔ (4 : ℝ) ≤ ↑(m^2) := by simp
      _ ↔ 2 ^ 2 ≤ m^2 := Nat.cast_le
      _ ↔ 2 ≤ m := Nat.pow_le_pow_iff_left (by norm_num)
    -- Use simpler implication `this`.
    _ ↔ 0 < m ∧ 0 < n ∧ 2 ≤ m ∧ n = m^2 - 2 := by
      simp only [and_congr_right_iff]
      exact fun _ hn hm ↦ this hm hn
    -- Show that `0 < m` and `0 < n` are satisfied by `2 ≤ m` and `n = m^2 - 2`.
    _ ↔ _ := by
      simp only [← and_assoc, and_congr_left_iff, and_iff_right_iff_imp]
      intro hn hm
      refine ⟨?_, ?_⟩
      · linarith
      · rw [hn, Nat.sub_pos_iff_lt]
        suffices 2 ^ 2 ≤ m^2 by linarith
        exact Nat.pow_le_pow_of_le_left hm 2

  intro m n hm hn
  have hm_sq : 4 ≤ m ^ 2 := Nat.pow_le_pow_left hm 2
  have hm_sq_re : (4 : ℝ) ≤ m ^ 2 := by
    suffices (4 : ℝ) ≤ m ^ 2 by simpa [Fin.forall_fin_two] using this
    simpa using (Nat.cast_le (α := ℝ)).mpr hm_sq

  calc _
  -- First re-arrange to obtain real interval in which `n` lies given `m`.
  _ ↔ 2 * √n ∈ Set.Ioo (√(m^2 - 4) + m) (√(m^2 - 2) + m) := by
    rw [Set.sub_mem_Ioo_iff_left]
  _ ↔ ↑n ∈ Set.Ioo ((m^2 - 2 + m * √(m^2 - 4)) / 2) ((m^2 - 1 + m * √(m^2 - 2)) / 2) := by
    refine and_congr ?_ ?_
    · calc √(m^2 - 4) + m < 2 * √n
      _ ↔ m + √(m^2 - 4) < 2 * √n := by rw [add_comm]
      _ ↔ (m + √(m^2 - 4)) ^ 2 < (2 * √n) ^ 2 := by
        symm
        refine pow_lt_pow_iff_left₀ (add_nonneg ?_ ?_) ?_ two_ne_zero <;> simp
      _ ↔ m^2 + (m^2 - 4) + 2 * m * √(m^2 - 4) < 4 * n := by
        simp only [add_sq', mul_pow, sq_sqrt, Nat.cast_nonneg]
        rw [sq_sqrt (by linarith)]
        norm_num
      _ ↔ _ := by
        refine propext_iff.mp ?_
        congr 1 <;> ring
      _ ↔ m^2 - 2 + m * √(m^2 - 4) < 2 * n := mul_lt_mul_iff_of_pos_left two_pos
      _ ↔ (m^2 - 2 + m * √(m^2 - 4)) / 2 < n := (div_lt_iff₀' two_pos).symm
    · calc 2 * √n < √(m^2 - 2) + m
      _ ↔ 2 * √n < m + √(m^2 - 2) := by rw [add_comm]
      _ ↔ (2 * √n) ^ 2 < (m + √(m^2 - 2)) ^ 2 := by
        symm
        refine pow_lt_pow_iff_left₀ ?_ (add_nonneg ?_ ?_) two_ne_zero <;> simp
      _ ↔ 4 * n < m^2 + (m^2 - 2) + 2 * m * √(m^2 - 2) := by
        simp only [add_sq', mul_pow, sq_sqrt, Nat.cast_nonneg]
        rw [sq_sqrt (by linarith)]
        norm_num
      _ ↔ _ := by
        refine propext_iff.mp ?_
        congr 1 <;> ring
      _ ↔ 2 * n < m^2 - 1 + m * √(m^2 - 2) := mul_lt_mul_iff_of_pos_left two_pos
      _ ↔ n < (m^2 - 1 + m * √(m^2 - 2)) / 2 := (lt_div_iff₀' two_pos).symm

  _ ↔ n = m^2 - 2 := by
    generalize ha : (m^2 - 2 + m * √(m^2 - 4)) / 2 = a
    generalize hb : (m^2 - 1 + m * √(m^2 - 2)) / 2 = b
    -- If `a < n < b` and `a < m^2 - 2 < b` then, in order to obtain `n = m^2 - 2`,
    -- it suffices to show that `m^2 - 3` and `m^2 - 1` are not in `Set.Ioo a b`.
    -- That is, there is only one natural number between `a` and `b`.
    suffices ↑(m^2 - 2 : ℕ) ∈ Set.Ioo a b ∧ ↑(m^2 - 2 - 1 : ℕ) ≤ a ∧ b ≤ ↑(m^2 - 2 + 1 : ℕ) by
      generalize hx_eq : m^2 - 2 = x at this ⊢
      -- The reverse direction is trivial given the assumptions.
      refine ⟨fun ⟨hna, hnb⟩ ↦ ?_, fun hn ↦ hn ▸ this.1⟩
      rcases this with ⟨⟨hxa, hxb⟩, hx_pred, hx_succ⟩
      refine Nat.le_antisymm ?_ ?_
      · refine Nat.le_of_lt_succ ?_
        exact Nat.cast_lt.mp (hnb.trans_le hx_succ)
      · refine Nat.le_of_pred_lt ?_
        exact Nat.cast_lt.mp (hx_pred.trans_lt hna)
    -- Move the subtraction from `ℕ` (truncated subtraction) to `ℝ`.
    suffices (m ^ 2 - 2 : ℝ) ∈ Set.Ioo a b ∧ m ^ 2 - 3 ≤ a ∧ b ≤ m ^ 2 - 1 by
      convert this
      · rw [Nat.cast_sub (by linarith : 2 ≤ m^2)]
        simp
      · rw [Nat.sub_sub, Nat.cast_sub (by linarith : 3 ≤ m^2)]
        simp
      · rw [← tsub_tsub_assoc (by linarith : 2 ≤ m^2) one_le_two]
        rw [Nat.add_one_sub_one, Nat.cast_sub (by linarith : 1 ≤ m^2)]
        simp

    rw [Set.mem_Ioo, ← ha, ← hb]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [div_lt_iff₀' two_pos]
      -- Need to show:
      -- `m^2 - 2 + m √(m^2 - 4) < 2 (m^2 - 2)`
      -- `m √(m^2 - 4) < m^2 - 2`
      rw [two_mul]
      gcongr
      -- This is the (strict) AM-GM inequality:
      -- `√(m^2 (m^2 - 4)) < 1/2 m^2 + 1/2 (m^2 - 4)`
      -- Mathlib has `geom_mean_le_arith_mean2_weighted`, specialized to two terms,
      -- but there is currently no strict version.
      convert (geom_mean_lt_arith_mean_weighted_iff_of_pos .univ ![1/2, 1/2] ![m^2, m^2 - 4]
        (by simp [Fin.forall_fin_two]) (by simpa using add_halves (1 : ℝ)) ?_).mpr ?_ using 1
      · -- Geometric mean.
        calc _
        _ = √(m ^ 2) * √(m ^ 2 - 4) := by simp
        _ = _ := by simp [sqrt_eq_rpow]
      · -- Arithmetic mean.
        calc _
        _ = (2⁻¹ * m ^ 2 + 2⁻¹ * (m ^ 2 - 4) : ℝ) := by ring
        _ = _ := by simp
      · -- Non-negativity.
        simpa [Fin.forall_fin_two] using hm_sq_re
      · -- The two elements are not equal (required for strict inequality).
        use 0, Finset.mem_univ 0, 1, Finset.mem_univ 1, ne_of_gt ?_
        simp

    · rw [lt_div_iff₀' two_pos]
      -- Need to show:
      -- `2 (m^2 - 2) < m^2 - 1 + m √(m^2 - 2)`
      -- Treat as two terms; use `m^2 - 2 < m^2 - 1` and `m^2 - 2 < m √(m^2 - 2)`.
      -- Alternatively, could reduce to `m^2 - 3 < m * √(m^2 - 2)`.
      rw [two_mul]
      refine add_lt_add_of_lt_of_le (by simp) ?_
      calc _
      _ = √((m^2 - 2) ^ 2) := .symm <| sqrt_sq <| by linarith
      _ = √(m^2 - 2) * √(m^2 - 2) := by rw [sq, sqrt_mul (by linarith)]
      _ ≤ √(m^2) * √(m^2 - 2) := by
        gcongr
        simp
      _ = m * √(m^2 - 2) := by simp

    · rw [le_div_iff₀' two_pos]
      -- Need to show:
      -- `2 (m^2 - 3) ≤ m^2 - 2 + m √(m^2 - 4)`
      -- `m^2 - 4 ≤ m √(m^2 - 4)`
      suffices m ^ 2 - 4 ≤ m * √(m^2 - 4) by
        refine le_add_of_sub_left_le ?_
        calc _
        _ = (m^2 - 4 : ℝ) := by ring
        _ ≤ _ := this
      calc _
      _ = √((m^2 - 4) ^ 2) := .symm <| sqrt_sq <| by linarith
      _ ≤ √(m^2 - 4) * √(m^2 - 4) := by rw [sq, sqrt_mul (by linarith)]
      _ ≤ √(m^2) * √(m^2 - 4) := by
        gcongr
        simp
      _ = _ := by simp

    · rw [div_le_iff₀' two_pos]
      -- Need to show:
      -- `m^2 - 1 + m √(m^2 - 2) ≤ 2 (m^2 - 1)`
      -- `m √(m^2 - 2) ≤ m^2 - 1`
      -- Use AM-GM inequality again (non-strict version this time).
      rw [two_mul]
      gcongr
      convert geom_mean_le_arith_mean2_weighted one_half_pos.le one_half_pos.le (sq_nonneg (m : ℝ))
        (by linarith : (0 : ℝ) ≤ m^2 - 2) (add_halves (1 : ℝ)) using 1
      · calc _
        _ = √(m^2) * √(m^2 - 2) := by simp
        _ = _ := by simp [sqrt_eq_rpow]
      · calc _
        _ = (2⁻¹ * m^2 + 2⁻¹ * (m^2 - 2) : ℝ) := by ring
        _ = _ := by simp
