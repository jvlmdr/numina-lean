-- https://cloud.kili-technology.com/label/projects/label/cmbj2n1xs00n6v7ay41zenqir

import Mathlib

open Real Set

/- Let $0 < x_{i} < π$ ($i = 1, 2, \ldots, n$), prove that:
$$
\prod_{i=1}^{n} \sin(x_{i}) \leqslant
  \left[\sin\left(\frac{1}{n} \sum_{i=1}^{n} x_{i}\right)\right]^{n} .
$$ -/

-- The image of `(0, π)` under `sin` is `(0, 1]`.
lemma image_sin_Ioo_zero_pi : Set.image sin (Ioo 0 π) = Ioc 0 1 := by
  ext y
  rw [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_Ioc]
    exact ⟨sin_pos_of_mem_Ioo hx, sin_le_one x⟩
  · intro hy
    rw [mem_Ioc] at hy
    use arcsin y
    constructor
    · rw [mem_Ioo]
      constructor
      · simpa using hy.1
      · calc _
        _ ≤ π / 2 := (arcsin_mem_Icc y).2
        _ < π := by simp [pi_pos]
    · refine sin_arcsin ?_ ?_ <;> linarith

-- The function `sin` is concave on `Icc 0 π`.
lemma concaveOn_Icc_sin : ConcaveOn ℝ (Icc 0 π) sin := by
  refine concaveOn_of_deriv2_nonpos (convex_Icc 0 π) continuousOn_sin ?_ ?_ ?_
  · exact differentiable_sin.differentiableOn
  · simpa using differentiable_cos.differentiableOn
  · suffices ∀ x ∈ Ioo 0 π, 0 ≤ sin x by simpa
    exact fun x hx ↦ (sin_pos_of_mem_Ioo hx).le

-- The function `log ∘ sin` is concave on `Ioo 0 π`.
lemma concaveOn_Ioo_log_comp_sin : ConcaveOn ℝ (Ioo 0 π) fun x ↦ log (sin x) := by
  refine ConcaveOn.comp (f := sin) (g := log) ?_ ?_ ?_
  · rw [image_sin_Ioo_zero_pi]
    exact strictConcaveOn_log_Ioi.concaveOn.subset Ioc_subset_Ioi_self (convex_Ioc 0 1)
  · exact concaveOn_Icc_sin.subset Ioo_subset_Icc_self (convex_Ioo 0 π)
  · rw [image_sin_Ioo_zero_pi]
    exact strictMonoOn_log.monotoneOn.mono Ioc_subset_Ioi_self

theorem inequalities_159991 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Ioo 0 π) :
    ∏ i, sin (x i) ≤ (sin (1 / n * ∑ i, x i)) ^ n := by
  have hn_real : 0 < (n : ℝ) := by simpa using hn
  -- Take the log of both sides.
  refine (log_le_log_iff ?_ ?_).mp ?_
  · refine Finset.prod_pos fun i _ ↦ sin_pos_of_mem_Ioo (hx i)
  · refine pow_pos ?_ n
    refine sin_pos_of_mem_Ioo ?_
    -- The average of a set of points in a convex set belongs to that set.
    -- Rewrite using `Finset.centerMass`.
    suffices (.univ : Finset (Fin n)).centerMass (fun _ ↦ (n : ℝ)⁻¹) x ∈ Ioo 0 π by
      convert this
      simp [Finset.centerMass, mul_inv_cancel₀ hn_real.ne', Finset.mul_sum]
    exact (convex_Ioo 0 π).centerMass_mem (by simp) (by simp [hn_real]) (by simpa using hx)
  -- Take the log of the power and the product.
  rw [log_pow, log_prod _ _ fun i _ ↦ (sin_pos_of_mem_Ioo (hx i)).ne']
  -- Divide both sides by `n`.
  suffices 1 / n * ∑ i, log (sin (x i)) ≤ log (sin (1 / n * ∑ i, x i)) by
    simpa only [one_div, inv_mul_le_iff₀ hn_real]
  -- Move the weight `1 / n` inside the summation for `ConcaveOn.le_map_sum`.
  simp only [Finset.mul_sum]
  exact concaveOn_Ioo_log_comp_sin.le_map_sum (by simp) (by simp [hn_real.ne']) fun i _ ↦ hx i
