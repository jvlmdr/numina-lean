-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi300104nayzlcfz716

import Mathlib

/- Find the positive integer tuple $(a, b, c)$ such that $a^2 + b + 3 = (b^2 - c^2)^2$. -/

theorem number_theory_280132 (a b c : ℤ) (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c)
    (h : a ^ 2 + b + 3 = (b ^ 2 - c ^ 2) ^ 2) :
    (a, b, c) = (2, 2, 1) := by
  -- Introduce `n = |b ^ 2 - c ^ 2|` for readability.
  replace h : a ^ 2 + b + 3 = |b ^ 2 - c ^ 2| ^ 2 := by simpa using h
  generalize hn_def : |b ^ 2 - c ^2| = n at h
  have hn_nonneg := hn_def ▸ abs_nonneg (b ^ 2 - c ^ 2)

  -- Bound `n` from below using `5 ≤ a^2 + b + 3 = n^2`.
  have hn : 3 ≤ n := by
    suffices n ^ 2 > 2 ^ 2 from lt_of_pow_lt_pow_left₀ 2 hn_nonneg this
    calc _
    _ = a ^ 2 + b + 3 := h.symm
    _ ≥ 1 + 1 + 3 := by
      refine add_le_add_right (add_le_add ?_ hb_pos) 3
      suffices 1 ≤ |a| by simpa
      exact le_abs.mpr (Or.inl ha_pos)

  -- It follows that `b ≠ c` since `n ≠ 0`.
  have hbc : b ≠ c := by
    suffices n ≠ 0 by
      refine mt (fun this ↦ ?_) this
      simp [← hn_def, this]
    exact (two_pos.trans hn).ne'
  -- Use this to bound `b` above using `n`.
  have hbn : b < n := by
    calc n
    _ = |b + c| * |b - c| := by simpa [sq_sub_sq, abs_mul] using hn_def.symm
    _ ≥ |b + c| := by
      refine le_mul_of_one_le_right (abs_nonneg _) ?_
      refine Int.one_le_abs ?_
      exact sub_ne_zero_of_ne hbc
    _ = b + c := abs_of_nonneg (by linarith)
    _ ≥ b + 1 := Int.add_le_add_left hc_pos b

  -- Trivial to similarly bound `a` above using `n`.
  have han : a < n := by
    suffices a ^ 2 < n ^ 2 from lt_of_pow_lt_pow_left₀ 2 hn_nonneg this
    calc _
    _ < a ^ 2 + (b + 3) := by linarith
    _ = a ^ 2 + b + 3 := by ring
    _ = _ := h

  -- Combine the bounds on `a` and `b` to bound `n` from above.
  replace hn : n = 3 := by
    refine le_antisymm ?_ hn
    -- `n ^ 2 ≤ (n - 1) ^ 2 + (n - 1) + 3 = n (n - 1) + 3 = n ^ 2 - n + 3`
    suffices 0 ≤ -n + 3 by linarith
    suffices n ^ 2 ≤ n ^ 2 + (-n + 3) from nonneg_of_le_add_right this
    calc _
    _ = a ^ 2 + b + 3 := h.symm
    _ ≤ (n - 1) ^ 2 + (n - 1) + 3 := by
      refine Int.add_le_add_right ?_ 3
      refine add_le_add (pow_le_pow_left₀ ha_pos.le ?_ 2) ?_
      · exact Int.le_sub_one_of_lt han
      · exact Int.le_sub_one_of_lt hbn
    _ = _ := by ring

  -- Substitute `n = 3`.
  rw [hn] at han hbn h hn_def
  clear hn hn_nonneg n

  -- Have `a ∈ {1, 2}` and `b ∈ {1, 2}` since `0 < a, b < 3`.
  have ha : a = 1 ∨ a = 2 := by
    suffices a ∈ ({1, 2} : Finset ℤ) by simpa using this
    exact Finset.mem_Ioo.mpr ⟨ha_pos, han⟩
  have hb : b = 1 ∨ b = 2 := by
    suffices b ∈ ({1, 2} : Finset ℤ) by simpa using this
    exact Finset.mem_Ioo.mpr ⟨hb_pos, hbn⟩
  -- Consider the four cases of `a ∈ {1, 2}` and `b ∈ {1, 2}`.
  cases ha with
  | inl ha =>
    cases hb with
    | inl hb => simp [ha, hb] at h  -- a = 1, b = 1; contradiction.
    | inr hb => simp [ha, hb] at h  -- a = 1, b = 2; contradiction.
  | inr ha =>
    cases hb with
    | inl hb => simp [ha, hb] at h  -- a = 2, b = 1; contradiction.
    | inr hb =>
      -- Now it remains to show that c = 1.
      suffices hc : c ^ 2 = 1 by
        replace hc : c = 1 ∨ c = -1 := by simpa using hc
        cases hc with
        | inl hc => simp [ha, hb, hc]
        | inr hc => linarith  -- c = -1; contradiction.
      replace hc : 4 - c ^ 2 = 3 ∨ 4 - c ^ 2 = -3 := by simpa [hb, abs_eq] using hn_def
      cases hc with
      | inl hc => linarith  -- `4 - c^2 = 3` provides `c^2 = 1`.
      | inr hc =>
        replace hc : c ^ 2 = 7 := by linarith
        -- Contradiction since 7 is not a square.
        suffices ¬IsSquare (7 : ℤ) from this.elim <| isSquare_of_exists_sq 7 ⟨c, hc.symm⟩
        refine Prime.not_square ?_
        norm_num
