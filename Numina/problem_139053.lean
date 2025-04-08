-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi3002k4nayigty563s

import Mathlib

open Real

/- Prove that √2, √3 and √5 cannot be terms in an arithmetic progression. -/

theorem number_theory_139053 : ¬∃ a d : ℝ,
    (∃ k : ℕ, √2 = a + k * d) ∧ (∃ k : ℕ, √3 = a + k * d) ∧ ∃ k : ℕ, √5 = a + k * d := by
  simp only [not_exists, not_and, forall_exists_index]
  intro a d k₂ hk₂ k₃ hk₃ k₅ hk₅
  -- We now seek a contradiction. The assumptions imply
  -- `√5 - √3 = (k₅ - k₂) * d`
  -- `√3 - √2 = (k₃ - k₂) * d`
  -- From this, we obtain `(√5 - √3) / (√2 - √3) = (k₅ - k₂) / (k₃ - k₂)`.
  -- The left side is irrational and the right side is rational.
  suffices Irrational ((√5 - √2) / (√3 - √2)) by
    refine Rat.not_irrational ((k₅ - k₂) / (k₃ - k₂)) ?_
    convert this using 1
    calc _
    _ = (k₅ - k₂ : ℝ) / (k₃ - k₂) := by simp
    _ = (k₅ - k₂) * d / ((k₃ - k₂) * d) := by
      refine (mul_div_mul_right _ _ ?_).symm
      have : √2 ≠ √3 := by simp
      refine mt (fun hd ↦ ?_) this
      simp [hk₂, hk₃, hd]
    _ = (k₅ * d - k₂ * d) / (k₃ * d - k₂ * d) := by simp [sub_mul]
    _ = _ := by simp [hk₂, hk₃, hk₅, add_sub_add_left_eq_sub]

  -- It remains to prove that the left side is irrational.
  suffices ∀ q : ℚ, (√5 - √2) / (√3 - √2) ≠ q by
    refine (irrational_iff_ne_rational _).mpr fun qa qb ↦ ?_
    simpa using this (qa / qb)
  intro q h
  -- We again seek a contradiction.
  -- Isolate one of the square roots and square both sides.
  have h : √5 - √2 = q * (√3 - √2) := by
    refine (div_eq_iff ?_).mp h
    simp [sub_ne_zero]
  rw [sub_eq_iff_eq_add'] at h
  -- Obtain `√5` as a linear (not convex) combination of `√2` and `√3`.
  have h : √5 = (1 - q) * √2 + q * √3 := .trans h (by ring)
  have h : 5 = (1 - q) ^ 2 * 2 + q ^ 2 * 3 + 2 * (1 - q) * q * √(2 * 3) := by
    convert congrArg (· ^ 2) h using 1
    · simp
    · simp only [add_sq, mul_pow, sqrt_mul, sq_sqrt, Nat.ofNat_nonneg]
      ring
  -- Gather the rational terms.
  have h : 5 = ((1 - q) ^ 2 * 2 + q ^ 2 * 3 : ℚ) + (2 * (1 - q) * q : ℚ) * √(2 * 3) := by
    simpa using h

  -- The left side is rational, the right side contains a single irrational term.
  refine (h ▸ not_irrational_ofNat 5) ?_
  refine .rat_add _ <| .rat_mul ?_ ?_
  · suffices Irrational √6 by
      convert this
      norm_num
    refine irrational_sqrt_ofNat_iff.mpr ?_
    suffices ∀ n, 6 ≠ n * n by simpa [IsSquare] using this
    -- Prove that 6 is not a square, since 2 ^ 2 = 4 and 3 ^ 2 = 9.
    intro n
    cases le_or_lt n 2 with
    | inl h =>
      suffices n * n ≤ 2 * 2 by linarith
      exact Nat.mul_le_mul h h
    | inr h =>
      suffices 3 * 3 ≤ n * n by linarith
      exact Nat.mul_le_mul h h
  · -- Cannot have q = 0 or q = 1, as these correspond to `√5 = √2` and `√5 = √3`.
    suffices 1 - q ≠ 0 ∧ q ≠ 0 by simpa using this
    refine ⟨?_, ?_⟩
    · suffices q ≠ 1 from sub_ne_zero_of_ne this.symm
      intro hq
      simp [hq] at h
    · intro hq
      simp [hq] at h
