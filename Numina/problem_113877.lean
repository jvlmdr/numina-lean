-- https://cloud.kili-technology.com/label/projects/label/cm91j40co007pseayfgbazj55

import Mathlib

open Matrix

/- If $A \in M_{n}(R)$ and $A^{3} = A + I_{n}$, prove that $det(A) > 0$. -/

theorem algebra_113877 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A^3 = A + 1) : A.det > 0 := by
  change 0 < A.det  -- TODO: Remove

  -- Writing the equation `A (A^2 - 1) = 1`, we see that we cannot have `det A = 0`.
  have h_zero : A.det ≠ 0 := by
    suffices (A * (A ^ 2 - 1)).det ≠ 0 by
      refine mt (fun this ↦ ?_) this
      simp [this]
    suffices A * (A ^ 2 - 1) = 1 by simp [this]
    calc _
    _ = A ^ 3 - A := by noncomm_ring
    _ = 1 := by simp [hA]

  have h_quad : 0 < (A^2 + A + 1).det := by
    have := RingHom.map_det (algebraMap ℝ ℂ) (A ^ 2 + A + 1)
    simp [-Complex.coe_algebraMap] at this

    rw [Matrix.det_eq_prod_roots_charpoly (R := ℂ)] at this
    rw [Matrix.map_add _ (by simp)] at this
    rw [Matrix.map_add _ (by simp)] at this
    simp only [sq] at this
    rw [Matrix.map_mul] at this
    simp only [← sq] at this
    rw [Matrix.map_one _ rfl rfl] at this
    generalize A.map (algebraMap ℝ ℂ) = B at this

    sorry

  -- TODO: Remove; not needed.
  -- Observe that `A = A^3 - 1 = (A - 1) (A^2 + A + 1)` and
  -- therefore `det A = det (A - 1) * det (A^2 + A + 1)`.
  have _ : 0 < A.det * (A - 1).det := by
    suffices A = (A - 1) * (A^2 + A + 1) by
      have : A.det = (A - 1).det * (A^2 + A + 1).det := by
        simpa using congrArg det this
      calc A.det * (A - 1).det
      _ = (A - 1).det ^ 2 * (A ^ 2 + A + 1).det := by
        rw [this]
        ring
      _ > 0 := by
        refine mul_pos (sq_pos_of_ne_zero ?_) h_quad
        refine mt (fun h ↦ ?_) h_zero
        simp [this, h]
    calc _
    _ = A ^ 3 - 1 := eq_sub_of_add_eq hA.symm
    _ = _ := by noncomm_ring

  -- Observe that `A^2 (A + 1) = A^2 + A + 1` and therefore
  -- `(det A)^2 * det (A + 1) = det (A^2 + A + 1) > 0`.
  have : 0 < (A + 1).det := by
    suffices A ^ 2 * (A + 1) = A ^ 2 + A + 1 by
      have : A.det ^ 2 * (A + 1).det = (A ^ 2 + A + 1).det := by
        simpa using congrArg det this
      suffices 0 < A.det ^ 2 * (A + 1).det from pos_of_mul_pos_right this (sq_nonneg _)
      rw [this]
      exact h_quad
    calc _
    _ = A ^ 3 + A ^ 2 := by noncomm_ring
    _ = _ := by
      rw [hA]
      noncomm_ring

  suffices 0 < A.det ^ 3 from (odd_two_mul_add_one 1).pow_pos_iff.mp this
  suffices 0 < (A ^ 3).det by simpa using this
  simpa [hA]  -- TODO: Re-order.
