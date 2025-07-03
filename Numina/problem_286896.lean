-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9z0026ueaxzlfxr182

import Mathlib

open Real Set
open scoped BigOperators

/- Let $x, y, z \in \mathbf{R}^{+}, x^{2}+y^{2}+z^{2}=1$. Find
$$
\frac{x^{5}}{y^{2}+z^{2}-y z}+\frac{y^{5}}{z^{2}+x^{2}-z x}+\frac{z^{5}}{x^{2}+y^{2}-x y}
$$
the minimum value. -/



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

    sorry
