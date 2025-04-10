-- https://cloud.kili-technology.com/label/projects/label/cm91j40co007pseayfgbazj55

import Mathlib

open Matrix Polynomial

/- If $A \in M_{n}(R)$ and $A^{3} = A + I_{n}$, prove that $det(A) > 0$. -/

theorem algebra_113877 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : A^3 = A + 1) : A.det > 0 := by
  -- First establish that matrices are non-singular using `A (A + I) (A - I) = I`.
  have h_nz : A.det ≠ 0 ∧ (A + 1).det ≠ 0 ∧ (A - 1).det ≠ 0 := by
    suffices (A * (A + 1) * (A - 1)).det ≠ 0 by simpa [and_assoc] using this
    suffices A * (A + 1) * (A - 1) = 1 by simp [this]
    calc _
    _ = A ^ 3 - A := by noncomm_ring
    _ = _ := sub_eq_iff_eq_add'.mpr h

  -- `A^3 = A + I` is equivalent to `A^2 (A + I) = A^2 + A + I`, where
  -- it can be shown that `A^2 + A + I` has positive determinant.
  suffices 0 < A.det ^ 3 from (odd_two_mul_add_one 1).pow_pos_iff.mp this
  suffices 0 < (A ^ 3).det by simpa using this
  suffices 0 < (A + 1).det by simpa [h] using this
  suffices 0 < A.det ^ 2 * (A + 1).det from pos_of_mul_pos_right this (sq_nonneg _)
  -- Switch from positivity to nonnegativity.
  suffices 0 ≤ A.det ^ 2 * (A + 1).det by
    refine lt_iff_le_and_ne.mpr ⟨this, ?_⟩
    refine (mul_ne_zero ?_ ?_).symm
    · simpa using h_nz.1
    · simpa using h_nz.2.1
  suffices 0 ≤ (A ^ 2 * (A + 1)).det by simpa using this
  suffices 0 ≤ (A ^ 2 + A + 1).det by
    convert this using 2
    calc _
    _ = A ^ 3 + A ^ 2 := by noncomm_ring
    _ = A + 1 + A ^ 2 := by rw [h]
    _ = _ := by noncomm_ring

  -- The eigenvalues of `A^2 + A + I` are `λ^2 + λ + 1` where `λ` is an eigenvalue of `A`.
  -- The determinant of `A^2 + A + I` is equal to the product of the eigenvalues.
  -- `det (A^2 + A + I) = ∏ i, (λ i ^ 2 + λ i + 1)`
  -- If `λ` is real, then `λ^2 + λ + 1 > 0`.
  -- If `λ` is complex, the conjugate pair has product `|λ^2 + λ + 1|^2 ≥ 0`.
  sorry
