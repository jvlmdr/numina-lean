-- https://cloud.kili-technology.com/label/projects/label/cm91j3x7x0033seay8912djwh

import Mathlib

/- There do not exist integers $x, y$ such that $x^2 + 3 x y - 2 y^2 = 122$. -/

theorem number_theory_289784 : ¬∃ x y : ℤ, x ^ 2 + 3 * x * y - 2 * y ^ 2 = 122 := by
  simp only [not_exists]
  intro x y
  -- Multiply both sides by 2 ^ 2.
  suffices 4 * (x ^ 2 + 3 * x * y - 2 * y ^ 2) ≠ 4 * 122 from
    fun h ↦ this <| congrArg (4 * ·) h
  -- Complete the square on the left side.
  suffices (2 * x + 3 * y) ^ 2 - 17 * y ^ 2 ≠ 488 by
    convert this using 1
    ring
  -- It suffices to show that equality does not hold modulo 17.
  suffices (2 * x + 3 * y) ^ 2 % 17 ≠ 12 by
    refine mt (fun h ↦ ?_) this
    simpa [Int.sub_emod] using congrArg (fun z : ℤ ↦ z % 17) h
  -- Now it suffices to show that 12 is not a quadratic residue modulo 17.
  suffices 12 ∉ Set.range (· ^ 2 % 17) by
    simp only [Set.mem_range, not_exists] at this
    refine fun h ↦ this (2 * x + 3 * y).natAbs ?_
    refine (Nat.cast_inj (R := ℤ)).mp ?_
    simpa using h
  -- This can be demonstrated by considering the squares of `Finset.range 17`.
  suffices Set.range (· ^ 2 % 17) = Finset.toSet {0, 1, 4, 9, 16, 8, 2, 15, 13} by simp [this]
  calc _
  _ = Finset.toSet ((Finset.range 17).image fun x ↦ x ^ 2 % 17) := by
    ext x
    simp only [Set.mem_range, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨?_, ?_⟩
    · refine Exists.imp' (· % 17) fun n h ↦ ?_
      refine ⟨Nat.mod_lt _ (Nat.succ_pos _), ?_⟩
      convert h using 1
      exact (Nat.pow_mod n 2 17).symm
    · exact Exists.imp fun n ⟨_, h⟩ ↦ h
  _ = _ := by
    -- Exhaustively evaluate all 17 squares modulo 17.
    refine congrArg Finset.toSet ?_
    decide
