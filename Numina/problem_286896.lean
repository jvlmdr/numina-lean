-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9z0026ueaxzlfxr182

import Mathlib

open Real Set
open scoped BigOperators

/- Let $x, y, z \in \mathbf{R}^{+}, x^{2}+y^{2}+z^{2}=1$. Find
$$
\frac{x^{5}}{y^{2}+z^{2}-y z}+\frac{y^{5}}{z^{2}+x^{2}-z x}+\frac{z^{5}}{x^{2}+y^{2}-x y}
$$
the minimum value. -/

-- lemma lemma_1 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
--     (h_sum : x^2 + y^2 + z^2 = 1) :


theorem inequalities_286896 :
  IsLeast
    {t | ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ x^2 + y^2 + z^2 = 1 ∧
      t = x^5 / (y^2 + z^2 - y * z) + y^5 / (z^2 + x^2 - z * x) + z^5 / (x^2 + y^2 - x * y)}
    (√3 / 3) := by
  rw [sqrt_div_self]
  -- TODO: is there a canonical way to obtain this from inequality with equality case?
  split_ands
  · rw [mem_setOf_eq]
    -- As will be shown below, the minimum value is obtained at `x = y = z = 1 / √3`.
    use (√3)⁻¹, (√3)⁻¹, (√3)⁻¹
    split_ands
    · simp
    · simp
    · simp
    · simpa using add_thirds (1 : ℝ)
    · -- TODO: quite fumbly...
      calc _
      _ = √3 ^ 4 / √3 ^ 4 / √3 := by simp
      _ = (√3 ^ 2 / √3 ^ 5) * √3 ^ 2 := by ring
      _ = (√3 ^ 5 / √3 ^ 2)⁻¹ * 3 := by simp [inv_div]
      _ = _ := by ring

  · rw [mem_lowerBounds]
    simp only [exists_and_left, mem_setOf_eq, forall_exists_index, and_imp]
    rintro _ x hx y hy z hz h_one rfl

    let f x y z : ℝ := x ^ 5 / (y ^ 2 + z ^ 2 - y * z)

    let g x y z : ℝ := x * y ^ 2 + x * z ^ 2 - x * y * z

    have hg_pos {x y z} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)  : 0 < g x y z := by
      suffices 0 < x * (y ^ 2 + z ^ 2 - y * z) by
        convert this using 1
        ring
      refine mul_pos hx ?_
      calc _
      _ ≤ (y - z) ^ 2 := sq_nonneg (y - z)
      _ = y ^ 2 + z ^ 2 - 2 * (y * z) := by ring
      _ < _ := by simp [hy, hz]

    -- Apply Cauchy-Schwarz inequality.
    have : (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≤
        (x ^ 6 / g x y z + y ^ 6 / g y z x + z ^ 6 / g z x y) * (g x y z + g y z x + g z x y) := by
      convert Finset.univ.sum_mul_sq_le_sq_mul_sq
        ![x ^ 3 / √(g x y z), y ^ 3 / √(g y z x), z ^ 3 / √(g z x y)]
        ![√(g x y z), √(g y z x), √(g z x y)]
      · simp [Fin.sum_univ_three, hx, hy, hz, (sqrt_pos.mpr (hg_pos _ _ _)).ne']
      · simp [Fin.sum_univ_three, hx, hy, hz, div_pow, (hg_pos _ _ _).le, ← pow_mul]
      · simp [Fin.sum_univ_three, hx, hy, hz, (hg_pos _ _ _).le]

    sorry
