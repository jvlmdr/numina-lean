-- https://cloud.kili-technology.com/label/projects/label/cm7eniblv00c5zz87491hw2nt
-- https://artofproblemsolving.com/wiki/index.php/2001_AMC_12_Problems/Problem_25

import Mathlib

/- Consider sequences of positive real numbers of the form x, 2000, y, … in which
every term after the first is 1 less than the product of its two immediate neighbors.
For how many different values of x does the term 2001 appear somewhere in the sequence?
(A) 1
(B) 2
(C) 3
(D) 4
(E) more than 4 -/

theorem algebra_95209 (a : ℝ → ℕ → ℝ) (h_pos : ∀ x n, 0 < a x n)
    (ha0 : ∀ x, a x 0 = x) (ha1 : ∀ x, a x 1 = 2000)
    (ha : ∀ x n, a x (n + 1) = a x n * a x (n + 2) - 1) :
    ∃ s : Finset ℝ, {x > 0 | 2001 ∈ Set.range (a x)} = s ∧ s.card = 4 := by
  -- Obtain an expression for the next element in the sequence given previous elements.
  -- a (n + 1) = a n * a (n + 2) - 1
  -- a (n + 2) = (a (n + 1) + 1) / a n
  have ha_next x n : a x (n + 2) = (a x (n + 1) + 1) / a x n := by
    rw [eq_div_iff (h_pos x n).ne']
    refine eq_add_of_sub_eq ?_
    symm
    convert ha x n using 1
    ring
  -- Simplify the expression for consecutive elements until we find a pattern.
  have ha2 x : a x 2 = 2001 / x := by
    calc _
    _ = _ := by
      rw [ha_next, ha1, ha0]
      norm_num
  have ha3 x (hx : 0 < x) : a x 3 = (2001 + x) / (2000 * x) := by
    calc _
    _ = (2001 / x + 1) / 2000 := by rw [ha_next, ha2, ha1]
    _ = ((2001 + x) / x) / 2000 := by
      simp only [add_div]
      rw [div_self hx.ne']
    _ = _ := by ring
  have ha4 x (hx : 0 < x) : a x 4 = (1 + x) / 2000 := by
    calc _
    _ = ((2001 + x) / (2000 * x) + 1) / (2001 / x) := by rw [ha_next, ha3 x hx, ha2 x]
    _ = ((2001 + x + 2000 * x) / (2000 * x)) / (2001 / x) := by
      congr
      simp only [add_div]
      rw [div_self]
      simpa using hx.ne'
    _ = ((2001 * (1 + x)) / (2000 * x)) / (2001 / x) := by ring
    _ = (2001 * (1 + x)) / (2001 * 2000) := by
      rw [div_div]
      congr 1
      rw [mul_comm 2001, mul_assoc]
      congr
      exact mul_div_cancel₀ _ hx.ne'
    _ = _ := by
      refine mul_div_mul_left _ _ ?_
      norm_num
  have ha5 x (hx : 0 < x) : a x 5 = x := by
    calc _
    _ = ((1 + x) / 2000 + 1) / ((2001 + x) / (2000 * x)) := by rw [ha_next, ha4 x hx, ha3 x hx]
    _ = ((2001 + x) / 2000) / ((2001 + x) / 2000 / x) := by ring
    _ = (((2001 + x) / 2000) / ((2001 + x) / 2000)) * x := by rw [← div_mul]
    _ = _ := by
      rw [div_self (div_pos (add_pos (by norm_num) hx) (by norm_num)).ne']
      simp only [one_mul]
  have ha6 x (hx : 0 < x) : a x 6 = 2000 := by
    rw [ha_next, ha5 x hx, ha4 x hx]
    rw [← div_mul, add_comm]
    rw [div_self (add_pos one_pos hx).ne']
    simp only [one_mul]

  -- We have found a cycle: obtain Function.Periodic.
  have hp x (hx : 0 < x) : (a x).Periodic 5 := fun n ↦ by
    induction n using Nat.twoStepInduction with
    | zero => rw [ha5 x hx, ha0]
    | one => rw [ha6 x hx, ha1]
    | more n IH0 IH1 => rw [ha_next, IH0, IH1, ha_next]

  -- Enumerate the finite range of each sequence `fun n ↦ a x n`.
  -- First a preliminary result that couldn't be found in Mathlib.
  have h_range_mod {c : ℕ} (hc : 0 < c) : Set.range (· % c) = Set.Iio c := by
    ext n
    simp only [Set.mem_range, Set.mem_setOf_eq]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ Nat.mod_lt i hc, fun hn ↦ ⟨n, Nat.mod_eq_of_lt hn⟩⟩
  have h_range x (hx : 0 < x) : Set.range (a x) =
      [x, 2000, 2001 / x, (2001 + x) / (2000 * x), (1 + x) / 2000].toFinset := by
    calc _
    _ = a x '' Set.Iio 5 := by
      -- Using periodicity, the range is equal to the image of a finite set.
      calc _
      _ = Set.range (a x ∘ (· % 5)) := by
        refine congrArg _ <| funext fun n ↦ ?_
        rw [Function.comp_apply]
        rw [(hp x hx).map_mod_nat]
      _ = _ := by
        rw [Set.range_comp]
        rw [h_range_mod (by norm_num)]
    _ = (Finset.range 5).image (a x) := by
      simp only [Finset.coe_image, Finset.coe_range]
    _ = [a x 0, a x 1, a x 2, a x 3, a x 4].toFinset := rfl
    _ = _ := by rw [ha0, ha1, ha2, ha3 x hx, ha4 x hx]
  -- Eliminate the case 2001 = 2000.
  have h_2001_range x (hx : 0 < x) : 2001 ∈ Set.range (a x) ↔
      2001 ∈ [x, 2001 / x, (2001 + x) / (2000 * x), (1 + x) / 2000] := by
    simp [h_range x hx]

  -- Determine the solutions.
  -- n = 0: 2001 = x
  -- n = 2: 2001 = 2001 / x ↔ x = 1
  -- n = 3: 2001 = (2001 + x) / (2000 * x) ↔ x = 2001 / (2001 * 2000 - 1)
  -- n = 4: 2001 = (1 + x) / 2000 ↔ x = 2001 * 2000 - 1
  use [2001, 1, 2001 / (2001 * 2000 - 1), 2001 * 2000 - 1].toFinset
  generalize hxs : ([2001, 1, 2001 / (2001 * 2000 - 1), 2001 * 2000 - 1] : List ℝ) = xs
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Set.mem_setOf_eq, List.coe_toFinset]
    -- Extract x > 0 from the iff.
    have hxs_pos : x ∈ xs → x > 0 := by
      rw [← hxs]
      revert x
      norm_num
    rw [iff_and_self.mpr hxs_pos]
    rw [and_congr_right_iff]
    intro hx
    -- Put the solutions in correspondence with the range.
    rw [h_2001_range x hx, ← hxs]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    refine or_congr ?_ ?_
    · rw [eq_comm]
    refine or_congr ?_ ?_
    · simp [eq_div_iff hx.ne']
    refine or_congr ?_ ?_
    · rw [eq_div_iff (by simp [hx.ne']), eq_div_iff (by norm_num)]
      rw [mul_sub, mul_one, sub_eq_iff_eq_add]
      simp only [mul_comm x, ← mul_assoc]
    · rw [eq_div_iff (by norm_num)]
      rw [eq_sub_iff_add_eq']
      exact eq_comm
  · -- Prove that the solutions are unique.
    rw [← hxs]
    refine List.toFinset_card_of_nodup ?_
    norm_num
