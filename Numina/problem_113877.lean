-- https://cloud.kili-technology.com/label/projects/label/cm91j40co007pseayfgbazj55

import Mathlib

open Complex
open scoped Real

/- If $A \in M_{n}(\mathbb{R})$ and $A^{3} = A + I_{n}$, prove that $det(A) > 0$. -/

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

  -- Factorize `A ^ 2 + A + I` into `A^2 + A + I = (A - z I)(A - z* I)`.
  -- The roots are the conjugate pair of `z = (-1+i√3)/2 = e^(2π/3 i)`.
  -- Then show that the determinant is non-negative since
  -- `det(A^2 + A + I) = det(A - z I) det(A - z I)*`.
  let r := 2 * π / 3
  let z := cexp (r * I)
  suffices ((A ^ 2 + A + 1).det : ℂ) = ↑(‖(A.map ofReal - z • 1).det‖ ^ 2) by
    simp [ofReal_inj.mp this]

  calc ((A ^ 2 + A + 1).det : ℂ)
  -- Move `Complex.ofReal` inside the determinant using `RingHom`.
  _ = (algebraMap ℝ ℂ) (A ^ 2 + A + 1).det := by simp
  _ = ((algebraMap ℝ ℂ).mapMatrix (A ^ 2 + A + 1)).det := RingHom.map_det _ _
  _ = (A.map ofReal ^ 2 + A.map ofReal + 1).det := by
    simp only [map_add, map_pow]
    simp
  -- Factor into `(A - z)(A - z*)`.
  _ = ((A.map ofReal - z • 1) * (A.map ofReal - starRingEnd ℂ z • 1)).det := by
    congr
    generalize A.map ofReal = B
    calc _
    _ = B ^ 2 - (-1 : ℂ) • B + 1 := by simp
    -- Split -1 = e^(2π/3 I) + e^(-2π/3 I).
    _ = B ^ 2 - (exp (r * I) + starRingEnd ℂ (exp (r * I))) • B + 1 := by
      congr 3
      suffices -1 = 2 * Real.cos (2 * π / 3) by
        simpa [add_conj, Complex.ext_iff, cos_ofReal_re] using this
      rw [mul_div_assoc, Real.cos_two_mul, Real.cos_pi_div_three]
      norm_num
    -- Put in a form that can be reached by `simp`.
    _ = B ^ 2 - exp (r * I) • B - (starRingEnd ℂ (exp (r * I)) • B - 1) := by
      rw [add_smul]
      noncomm_ring
    _ = (B - exp (r * I) • 1) * (B - starRingEnd ℂ (exp (r * I)) • 1) := by
      simp [sub_mul, mul_sub, smul_sub, sq, smul_smul, conj_mul']
  _ = (A.map ofReal - z • 1).det * ((A.map ofReal - starRingEnd ℂ z • 1)).det := Matrix.det_mul _ _
  -- Move `starRingEnd ℂ` outside the of determinant using `RingHom`.
  _ = (A.map ofReal - z • 1).det * ((starRingEnd ℂ).mapMatrix (A.map ofReal - z • 1)).det := by
    simp [map_sub, Matrix.smul_one_eq_diagonal, Function.comp_def]
  _ = (A.map ofReal - z • 1).det * starRingEnd ℂ (A.map ofReal - z • 1).det := by
    rw [RingHom.map_det]
  _ = ↑(‖(A.map ofReal - z • 1).det‖ ^ 2) := by simp [mul_conj']
