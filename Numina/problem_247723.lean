-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi300054naylh80hnwo

import Mathlib

open Real

/- Solve the equation
$$
\sqrt{5 x + 1} - 2 \sqrt{4 - x} + \sqrt{5} \sqrt{x + 2} = \sqrt{61 - 4 x}
$$
-/

theorem algebra_247723 (x : ℝ)
    (hx₁ : 0 ≤ 5 * x + 1) (hx₂ : 0 ≤ 4 - x) (hx₃ : 0 ≤ x + 2) (hx₄ : 0 ≤ 61 - 4 * x) :
    √(5 * x + 1) - 2 * √(4 - x) + √5 * √(x + 2) = √(61 - 4 * x) ↔ x = 3 := by
  calc _
  -- Bring all terms to one side.
  _ ↔ √(5 * x + 1) + √5 * √(x + 2) - (√(61 - 4 * x) + 2 * √(4 - x)) = 0 := by
    rw [sub_add_eq_add_sub, sub_eq_iff_eq_add, sub_eq_zero]
  -- All four terms are strictly monotonic; there is at most one solution.
  _ ↔ _ := by
    suffices StrictMonoOn (fun x ↦ √(5 * x + 1) + √5 * √(x + 2) - (√(61 - 4 * x) + 2 * √(4 - x)))
        (Set.Icc (-5⁻¹) 4) by
      convert this.eq_iff_eq (a := x) (b := 3) ?_ ?_ using 2
      · -- At x = 3, we have `f x = √16 + √25 - (√49 + 2) = 0`.
        symm
        calc _
        _ = √16 + √5 * √5 - (√49 + 2) := by norm_num
        _ = √(4 ^ 2) + √(5 ^ 2) - (√(7 ^ 2) + 2) := by
          congr
          · norm_num
          · simp
          · norm_num
        _ = 4 + 5 - (7 + 2) := by simp
        _ = 0 := by norm_num
      -- Remains to show that `-1/5 ≤ x ≤ 4` and 3 lies in this interval.
      · refine ⟨?_, ?_⟩ <;> linarith
      · refine ⟨?_, ?_⟩ <;> norm_num
    -- Establish strict monotonicity by treating each term.
    refine .add (.add ?_ ?_) (StrictAntiOn.neg (.add ?_ ?_))
    · intro x hx y hy h
      rw [Set.mem_Icc] at hx
      refine sqrt_lt_sqrt ?_ ?_
      · linarith
      · simpa using h
    · intro x hx y hy h
      rw [Set.mem_Icc] at hx
      suffices √(x + 2) < √(y + 2) by simpa using this
      refine sqrt_lt_sqrt ?_ ?_
      · linarith
      · simpa using h
    · intro x hx y hy h
      rw [Set.mem_Icc] at hy
      refine sqrt_lt_sqrt ?_ ?_
      · linarith
      · simpa using h
    · intro x hx y hy h
      rw [Set.mem_Icc] at hy
      suffices √(4 - y) < √(4 - x) by simpa using this
      refine sqrt_lt_sqrt ?_ ?_
      · linarith
      · simpa using h
