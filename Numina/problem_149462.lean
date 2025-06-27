-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9y000uueax6m2kl24j

import Mathlib

/- Let $x_{1}, \ldots, x_{n} > 0$ with $x_{1} \dots x_{n} = 1$. Show that
$$
x_{1}^{n-1} + x_{2}^{n-1} + \cdots + x_{n}^{n-1} \geqslant \frac{1}{x_{1}} + \ldots \frac{1}{x_{n}}
$$
-/

theorem inequalities_149462 (n : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hx_prod : ∏ i, x i = 1) :
    ∑ i, (x i)⁻¹ ≤ ∑ i, (x i) ^ (n - 1) := by
  -- The case where `n = 0` (both sums empty) is trivial.
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_one_sub_one]
    -- The case where `n = 1` is particular. The product constraint means `x 0 = 1`.
    cases n with
    | zero =>
      refine le_of_eq ?_
      simpa using hx_prod
    | succ n =>
      -- Multiply left side by `∏ i, x i = 1`.
      suffices ∑ i, (x i)⁻¹ * ∏ j, x j ≤ ∑ i, x i ^ (n + 1) by simpa [hx_prod]
      suffices ∑ i, ∏ j ∈ {i}ᶜ, x j ≤ ∑ i, x i ^ (n + 1) by
        convert this with i hi
        rw [inv_mul_eq_iff_eq_mul₀ (hx i).ne']
        exact Fintype.prod_eq_mul_prod_compl i x
      -- It can be observed that this holds using Muirhead's inequality, by
      -- taking symmetric sums and observing that (n, 0, ⋯, 0) majorizes (1, ⋯, 1, 0).
      -- We will show this by applying the weighted AM-GM inequality to a convex combination.
      -- Observe that `1/n * (x₁ ^ n + ⋯ + xₙ ^ n) = x₁ * x₂ * ⋯ * xₙ` for all subsets of size `n`
      -- from `n + 1` elements. Obtain this using theorem for weighted AM-GM inequality.
      have h_gm_le_am (k : Fin (n + 2)) := Real.geom_mean_le_arith_mean_weighted {k}ᶜ
        (fun _ ↦ (n + 1)⁻¹) (fun i ↦ x i ^ (n + 1)) (by simp [add_nonneg])
        (by simp [Finset.card_compl, Nat.cast_add_one_ne_zero n])
        (fun i _ ↦ pow_nonneg (hx i).le (n + 1))
      -- Take the sum of these inequalities for all `i`.
      convert Finset.univ.sum_le_sum fun i _ ↦ h_gm_le_am i using 1
      · -- Show that powers of `n + 1` and `(n + 1)⁻¹` cancel.
        simp [← Real.rpow_natCast, Real.rpow_rpow_inv (hx _).le (Nat.cast_add_one_ne_zero n)]
      · -- Move the factor of `(n + 1)` to the left.
        suffices (n + 1) * ∑ i, x i ^ (n + 1) = ∑ i : Fin (n + 2), ∑ j ∈ {i}ᶜ, x j ^ (n + 1) by
          rw [← eq_inv_mul_iff_mul_eq₀ (Nat.cast_add_one_ne_zero n)] at this
          simpa [Finset.mul_sum] using this
        -- Show that the excluded element accounts for the factor of `n + 2` rather than `n + 1`.
        calc _
        _ = (n + 2) * ∑ j, x j ^ (n + 1) - ∑ i, x i ^ (n + 1) := by ring
        _ = ∑ i : Fin (n + 2), ∑ j ∈ {i}ᶜ, x j ^ (n + 1) := by simp [Finset.compl_eq_univ_sdiff]
