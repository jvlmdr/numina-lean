-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9y000uueax6m2kl24j

import Mathlib

open Real
open scoped List Nat

/- Let $x_{1}, \ldots, x_{n} > 0$ with $x_{1} \dots x_{n} = 1$. Show that
$$
x_{1}^{n-1} + x_{2}^{n-1} + \cdots + x_{n}^{n-1} \geqslant \frac{1}{x_{1}} + \ldots \frac{1}{x_{n}}
$$
-/

theorem inequalities_149462 (n : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hx_prod : ∏ i, x i = 1) :
    ∑ i, (x i)⁻¹ ≤ ∑ i, (x i) ^ (n - 1) := by
  suffices ∑ i, (x i)⁻¹ * ∏ j, x j ≤ ∑ i, x i ^ (n - 1) by simpa [hx_prod]

  suffices ∑ i, ∏ j ∈ {i}ᶜ, x j ≤ ∑ i, x i ^ (n - 1) by
    convert this with i hi
    sorry

  -- suffices ∑ σ : Sym (n - 1) (Fin n), x
  suffices ∑ i, ∏ j ∈ {i}ᶜ, x j ≤ ∑ i, x i ^ (n - 1) by
    sorry

  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp [(Finset.compl_eq_empty_iff _).mpr]
    | succ n =>
      have h_gm_le_am (k) := geom_mean_le_arith_mean_weighted (ι := Fin (n + 2)) {k}ᶜ
        (fun _ ↦ (n + 1)⁻¹)
        (fun i ↦ x i ^ (n + 1))
        (by simp [add_nonneg])
        (by simp [Finset.card_compl, Nat.cast_add_one_ne_zero n])
        (fun i _ ↦ pow_nonneg (hx i).le (n + 1))
      simp only at h_gm_le_am
      have := Finset.univ.sum_le_sum fun i _ ↦ h_gm_le_am i
      convert this using 1
      · congr
        funext i
        congr
        funext j
        symm
        calc _
        _ = (x j ^ (n + 1 : ℝ)) ^ (n + 1 : ℝ)⁻¹ := by simp [← Real.rpow_natCast]  -- TODO: forward?
        _ = _ := rpow_rpow_inv (hx j).le (Nat.cast_add_one_ne_zero n)
      · -- Move the factor of `(n + 1)` to the left.
        suffices (n + 1) * ∑ i, x i ^ (n + 1) = ∑ i : Fin (n + 2), ∑ j ∈ {i}ᶜ, x j ^ (n + 1) by
          rw [← eq_inv_mul_iff_mul_eq₀ (Nat.cast_add_one_ne_zero n)] at this
          simpa [Finset.mul_sum] using this
        calc _
        _ = (n + 2) * ∑ j, x j ^ (n + 1) - ∑ i, x i ^ (n + 1) := by ring
        _ = ∑ i : Fin (n + 2), ∑ j ∈ {i}ᶜ, x j ^ (n + 1) := by simp [Finset.compl_eq_univ_sdiff]
