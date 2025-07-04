-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9z0026ueaxzlfxr182

import Mathlib

open Real Set
open scoped BigOperators Finset

/- Let $x, y, z \in \mathbf{R}^{+}, x^{2}+y^{2}+z^{2}=1$. Find
$$
\frac{x^{5}}{y^{2}+z^{2}-y z}+\frac{y^{5}}{z^{2}+x^{2}-z x}+\frac{z^{5}}{x^{2}+y^{2}-x y}
$$
the minimum value. -/

-- lemma lemma_1 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
--     (h_sum : x^2 + y^2 + z^2 = 1) :

-- TODO: generalize to strict inequality if needed
lemma pow_mean_le_pow_mean_weighted_of_pos_of_lt {ι : Type*} (s : Finset ι) (p q : ℝ)
    (hp : 0 < p) (hpq : p < q) (w z : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i ∈ s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∑ i ∈ s, w i * z i ^ p) ^ p⁻¹ ≤ (∑ i ∈ s, w i * z i ^ q) ^ q⁻¹ := by
  -- Raise both sides to the power of `q`.
  refine (rpow_le_rpow_iff (z := q) ?_ ?_ (hp.trans hpq)).mp ?_
  · refine rpow_nonneg ?_ _
    exact Finset.sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hz i hi) p)
  · refine rpow_nonneg ?_ _
    exact Finset.sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hz i hi) q)
  -- Apply Jensen's inequality to the convex function `x ↦ x ^ (q / p)`.
  have hr : 1 < q / p := one_lt_div_iff.mpr <| Or.inl ⟨hp, hpq⟩
  have h_convex := (strictConvexOn_rpow hr).convexOn
  convert h_convex.map_sum_le hw hw' fun i hi ↦ rpow_nonneg (hz i hi) p using 1
  · rw [← rpow_mul (Finset.sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hz i hi) p))]
    rw [inv_mul_eq_div]
    simp
  · rw [← rpow_mul (Finset.sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (rpow_nonneg (hz i hi) q))]
    rw [inv_mul_cancel₀ (hp.trans hpq).ne', rpow_one]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← rpow_mul (hz i hi), mul_div_cancel₀ q hp.ne']
    simp

lemma pow_mean_le_pow_mean_of_pos_of_lt {ι : Type*} (s : Finset ι) (p q : ℝ)
    (hp : 0 < p) (hpq : p < q) (z : ι → ℝ) (hz : ∀ i ∈ s, 0 ≤ z i) :
    ((∑ i ∈ s, z i ^ p) / #s) ^ p⁻¹ ≤ ((∑ i ∈ s, z i ^ q) / #s) ^ q⁻¹ := by
  cases s.eq_empty_or_nonempty with
  | inl hs => simp [hs, hp.ne', (hp.trans hpq).ne']
  | inr hs =>
    convert pow_mean_le_pow_mean_weighted_of_pos_of_lt s p q hp hpq (fun _ ↦ 1 / #s) z ?_ ?_ hz
      using 1
    · simp [Finset.sum_div, inv_mul_eq_div]
    · simp [Finset.sum_div, inv_mul_eq_div]
    · simp
    · simp [hs.card_ne_zero]

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

    -- TODO: use `le_div_iff₀` instead?
    have := div_le_of_le_mul₀
      (by refine (add_pos (add_pos ?_ ?_) ?_).le <;> simp [hx, hy, hz, hg_pos])
      (by refine (add_pos (add_pos ?_ ?_) ?_).le <;> simp [hx, hy, hz, div_pos, hg_pos]) this

    -- TODO: use `g y z = y^2 + z^2 - y * z` instead?
    have : (x^3 + y^3 + z^3) ^ 2 /
        (x * (y^2 + z^2) + y * (z^2 + x^2) + z * (x^2 + y^2) - 3 * x * y * z) ≤
        x^5 / (y^2 + z^2 - y * z) + y^5 / (z^2 + x^2 - z * x) + z^5 / (x^2 + y^2 - x * y) := by
      convert this using 1
      · ring
      · simp [pow_succ' _ 5, g, mul_assoc, ← mul_sub, ← mul_add,
          mul_div_mul_left, hx.ne', hy.ne', hz.ne']

    calc _
    _ ≤ 3 * √((x ^ 2 + y ^ 2 + z ^ 2) / 3) ^ 3 := by sorry
    _ ≤ x ^ 3 + y ^ 3 + z ^ 3 := by
      -- Put in form to match the power mean inequality.
      rw [← le_div_iff₀' three_pos, ← rpow_natCast _ 3]
      refine (le_rpow_inv_iff_of_pos (sqrt_nonneg _) ?_ three_pos).mp ?_
      · refine (div_pos (add_pos (add_pos ?_ ?_) ?_) three_pos).le <;> simp [hx, hy, hz]
      convert pow_mean_le_pow_mean_of_pos_of_lt Finset.univ 2 3 two_pos (by norm_num) ![x, y, z] ?_
        using 1
      · simp [Fin.sum_univ_three, sqrt_eq_rpow]
      · simp [Fin.sum_univ_three, ← rpow_natCast]
      · simp [Fin.forall_fin_succ, hx.le, hy.le, hz.le]

    _ ≤ _ := by sorry
