-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi3002e4nay1zivp4av

import Mathlib

open Polynomial

/- If both solutions of the equations $x^2 + p x + q = 0$ and $x^2 + p x - q = 0$ are integers,
prove that there exist integers $a$ and $b$ such that $p^2 = a^2 + b^2$. -/

theorem algebra_221516 {p q : ℝ}
    (h₁ : ∃ x₁ x₂ : ℤ, (X ^ 2 + C p * X + C q : ℝ[X]).roots = {↑x₁, ↑x₂})
    (h₂ : ∃ y₁ y₂ : ℤ, (X ^ 2 + C p * X - C q : ℝ[X]).roots = {↑y₁, ↑y₂}) :
    ∃ a b : ℤ, p ^ 2 = a ^ 2 + b ^ 2 := by
  simp only [sub_eq_add_neg] at h₂
  rcases h₁ with ⟨x₁, x₂, hx₁⟩
  rcases h₂ with ⟨y₁, y₂, hy₂⟩

  -- Rewrite the quadratics as a product of linear factors.
  have h₁ : X ^ 2 + C p * X + C q = (X - (x₁ : ℝ[X])) * (X - (x₂ : ℝ[X])) := by
    calc _
    _ = C 1 * X ^ 2 + C p * X + C q := by simp
    _ = Multiset.prod (.map (fun x ↦ X - C x) (C 1 * X ^ 2 + C p * X + C q).roots) := by
      symm
      refine prod_multiset_X_sub_C_of_monic_of_roots_card_eq ?_ ?_
      · exact leadingCoeff_quadratic one_ne_zero
      · rw [natDegree_quadratic one_ne_zero]
        simp [hx₁]
    _ = _ := by simp [hx₁]
  have h₂ : X ^ 2 + C p * X - C q = (X - (y₁ : ℝ[X])) * (X - (y₂ : ℝ[X])) := by
    calc _
    _ = C 1 * X ^ 2 + C p * X + C (-q) := by simp [sub_eq_add_neg]
    _ = Multiset.prod (.map (fun x ↦ X - C x) (C 1 * X ^ 2 + C p * X + C (-q)).roots) := by
      symm
      refine prod_multiset_X_sub_C_of_monic_of_roots_card_eq ?_ ?_
      · exact leadingCoeff_quadratic one_ne_zero
      · rw [natDegree_quadratic one_ne_zero]
        simp [hy₂]
    _ = _ := by simp [hy₂]

  -- Use extensionality of polynomial to relate `p` and `q` to roots.
  have ⟨hp₁, hq₁⟩ : p = ↑(-(x₁ + x₂)) ∧ q = ↑(x₁ * x₂) := by
    suffices X ^ 2 + C p * X + C q = X ^ 2 + C (-(x₁ + x₂ : ℝ)) * X + C (x₁ * x₂ : ℝ) by
      refine ⟨?_, ?_⟩
      · simpa [-map_intCast] using ext_iff.mp this 1
      · simpa [-map_intCast] using ext_iff.mp this 0
    rw [h₁]
    simp only [map_add, map_neg, map_intCast, map_mul]
    ring
  have ⟨hp₂, hq₂⟩ : p = ↑(-(y₁ + y₂)) ∧ q = ↑(-(y₁ * y₂)) := by
    suffices X ^ 2 + C p * X - C q = X ^ 2 + C (-(y₁ + y₂ : ℝ)) * X + C (y₁ * y₂ : ℝ) by
      refine ⟨?_, ?_⟩
      · simpa [-map_intCast] using ext_iff.mp this 1
      · rw [← neg_inj]
        simpa [-map_intCast] using ext_iff.mp this 0
    rw [h₂]
    simp only [map_add, map_neg, map_intCast, map_mul]
    ring
  -- Observe that both p and q are integers: introduce p' and q'.
  obtain ⟨p', hp'⟩ : ∃ p' : ℤ, p = p' := ⟨_, hp₁⟩
  obtain ⟨q', hq'⟩ : ∃ q' : ℤ, q = q' := ⟨_, hq₁⟩
  have hp₁ : p' = -(x₁ + x₂) := Int.cast_inj.mp (hp' ▸ hp₁)
  have hp₂ : p' = -(y₁ + y₂) := Int.cast_inj.mp (hp' ▸ hp₂)
  have hq₁ : q' = x₁ * x₂ := Int.cast_inj.mp (hq' ▸ hq₁)
  have hq₂ : q' = -(y₁ * y₂) := Int.cast_inj.mp (hq' ▸ hq₂)

  -- Observe that `p ^ 2 = (x₁ + x₂) ^ 2 = (x₁ - x₂) ^ 2 + 4 x₁ x₂` and
  -- therefore `p ^ 2 = m ^ 2 + 4 * q` with `m = x₁ - x₂`.
  have hpm : p' ^ 2 - 4 * q' = (x₁ - x₂) ^ 2 := by
    rw [hp₁, hq₁]
    ring
  have hpn : p' ^ 2 + 4 * q' = (y₁ - y₂) ^ 2 := by
    rw [hp₂, hq₂]
    ring
  generalize hm : x₁ - x₂ = m at hpm
  generalize hn : y₁ - y₂ = n at hpn

  -- Since `2 ∣ 4 q`, the parities of `m`, `p` and `n` are the same.
  -- It follows that both `m + n` and `m - n` are divisible by 2.
  -- This enables us to use `p^2 = 1/2 (m^2 + n^2) = (1/4) (m + n)^2 + (1/4) (m - n)^2`.
  have hm_even : Even m ↔ Even p' := by
    suffices Even (m ^ 2) ↔ Even (p' ^ 2) by simpa [Int.even_pow' two_ne_zero] using this
    rw [← hpm, Int.even_sub]
    refine iff_true_right ?_
    simpa [← mul_assoc] using even_two_mul (2 * q')
  have hn_even : Even n ↔ Even p' := by
    suffices Even (n ^ 2) ↔ Even (p' ^ 2) by simpa [Int.even_pow' two_ne_zero] using this
    rw [← hpn, Int.even_add]
    refine iff_true_right ?_
    simpa [← mul_assoc] using even_two_mul (2 * q')
  have h_even_add : Even (m + n) := Int.even_add.mpr (hm_even.trans hn_even.symm)
  have h_even_sub : Even (m - n) := Int.even_sub.mpr (hm_even.trans hn_even.symm)

  use (m + n) / 2, (m - n) / 2
  symm
  calc _
  _ = (↑(m + n) / 2 : ℝ) ^ 2 + (↑(m - n) / 2 : ℝ) ^ 2 := by
    congr
    · simpa using congrArg (fun x : ℤ ↦ (x : ℝ) / 2) (Int.ediv_two_mul_two_of_even h_even_add)
    · simpa using congrArg (fun x : ℤ ↦ (x : ℝ) / 2) (Int.ediv_two_mul_two_of_even h_even_sub)
  _ = ((m + n) ^ 2 + (m - n) ^ 2) / 2 ^ 2 := by simpa [div_pow] using div_add_div_same _ _ _
  _ = 2 * (m ^ 2 + n ^ 2) / 2 ^ 2 := by
    congr
    simp only [add_sq, sub_sq]
    ring
  _ = (m ^ 2 + n ^ 2) / 2 := by
    rw [sq 2]
    exact mul_div_mul_left _ 2 two_ne_zero
  _ = ↑(m ^ 2 + n ^ 2) / 2 := by simp
  _ = _ := by simp [← hpm, ← hpn, hp']
