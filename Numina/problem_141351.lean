-- https://cloud.kili-technology.com/label/projects/label/cmcboufzi00imueax7a210z7z

import Mathlib

open Real

/- Let $x_i > 0$ ($i = 1, 2, \cdots, n$), $a \in \mathbf{R}^{+}$ and
$\sum_{i=1}^{n} x_i = s \leqslant a$. Prove that:
$\prod_{i=1}^{n} \frac{a + x_i}{a - x_i} \geqslant \left(\frac{n a + s}{n a - s}\right)^n$. -/

theorem inequalities_141351 {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (a : ℝ) (ha : 0 < a) (s : ℝ) (hs : s = ∑ i, x i) (hsa : s ≤ a) :
    ((n * a + s) / (n * a - s)) ^ n ≤ ∏ i, (a + x i) / (a - x i) := by
  -- For `2 ≤ n`, we have `x i < ∑ j, x j = s ≤ a` and hence the denominator `a - x i ≠ 0`.
  -- First handle the cases where the sum is trivial.
  cases lt_or_le n 2 with
  | inl hn =>
    rcases hs with rfl
    interval_cases n <;> simp
  | inr hn =>
    -- Show that the denominator in the product is positive.
    have hxs (i) : x i < s := by
      suffices 0 < ∑ i ∈ Finset.univ.erase i, x i by simpa [hs]
      refine Finset.sum_pos (fun j _ ↦ hx j) ?_
      rw [Finset.erase_nonempty (Finset.mem_univ i)]
      rw [← Finset.one_lt_card_iff_nontrivial]
      simpa
    -- Use this to show that all factors in the product are positive.
    have h_elem_pos (i) : 0 < (a + x i) / (a - x i) :=
      div_pos (add_pos ha (hx i)) (by simpa using (hxs i).trans_le hsa)

    -- Take the log of both sides using strict monotonicity of `log x` on `0 < x`.
    refine (log_le_log_iff ?_ ?_).mp ?_
    · refine pow_pos ?_ n
      refine div_pos ?_ ?_
      · refine add_pos (mul_pos ?_ ha) ?_
        · simpa using Nat.zero_lt_of_lt hn
        · rw [hs]
          refine Finset.sum_pos (fun i _ ↦ hx i) ?_
          rw [← Finset.card_ne_zero]
          simpa using Nat.not_eq_zero_of_lt hn
      · rw [sub_pos]
        refine lt_of_le_of_lt hsa ?_
        exact lt_mul_of_one_lt_left ha (by simpa using hn)
    · exact Finset.prod_pos fun i _ ↦ h_elem_pos i

    -- Take log of power and product.
    rw [log_pow, log_prod _ _ fun i _ ↦ (h_elem_pos i).ne']
    -- Divide both sides by `n` to obtain a mean on the right.
    have hn_coe : 0 < (n : ℝ) := by simpa using Nat.zero_lt_of_lt hn
    rw [← le_inv_mul_iff₀ hn_coe]

    -- It will now suffice to show that `x ↦ log ((a + x) / (a - x))` is convex on `0 < x < a`.
    suffices ConvexOn ℝ (Set.Ioo 0 a) fun x ↦ log ((a + x) / (a - x)) by
      -- The result will be obtain using Jensen's inequality.
      have := this.map_sum_le (p := x) (t := Finset.univ) (w := fun _ ↦ (↑n)⁻¹)
        (fun i _ ↦ by simp) (by simp [hn_coe.ne']) (fun i _ ↦ ⟨hx i, lt_of_lt_of_le (hxs i) hsa⟩)
      calc _
      -- Divide top and bottom of fraction by `n` to obtain mean on the left.
      _ = log ((a + (↑n)⁻¹ * s) / (a - (↑n)⁻¹ * s)) := by
        congr 1
        calc _
        _ = (↑n)⁻¹ * (n * a + s) / ((↑n)⁻¹ *  (n * a - s)) := by
          rw [mul_div_mul_left]
          simpa using hn_coe.ne'
        _ = _ := by simp [mul_add, mul_sub, hn_coe.ne']
      -- Apply Jensen's inequality.
      _ ≤ _ := by simpa [hs, Finset.mul_sum] using this

    -- Separate the log into a difference before taking derivatives to show convexity.
    suffices ConvexOn ℝ (Set.Ioo 0 a) fun x ↦ log (a + x) - log (a - x) by
      refine this.congr fun x hx ↦ ?_
      simp only [Set.mem_Ioo] at hx
      refine (log_div ?_ ?_).symm <;> linarith

    -- Obtain the first derivative.
    have h_deriv (x : ℝ) (hx : x ∈ Set.Ioo 0 a) :
        HasDerivAt (fun x ↦ log (a + x) - log (a - x)) ((a + x)⁻¹ + (a - x)⁻¹) x := by
      suffices HasDerivAt (fun x ↦ log (a + x) - log (a - x)) (1 / (a + x) - -1 / (a - x)) x by
        simpa [neg_div]
      simp only [Set.mem_Ioo] at hx
      refine .sub ?_ ?_
      · refine .log ?_ (by linarith)
        exact (hasDerivAt_id x).const_add a
      · refine .log ?_ (by linarith)
        exact (hasDerivAt_id x).const_sub a

    -- Prove convexity using the second derivative test.
    refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo 0 a) ?_ ?_ ?_ ?_
      (f' := fun x ↦ (a + x)⁻¹ + (a - x)⁻¹) (f'' := fun x ↦ -1 / (a + x) ^ 2 + -(-1) / (a - x) ^ 2)
    · exact HasDerivAt.continuousOn h_deriv
    · intro x hx
      refine HasDerivAt.hasDerivWithinAt ?_
      exact h_deriv x (by simpa using hx)
    · -- Prove the form of the second derivative.
      simp only [interior_Ioo, Set.mem_Ioo]
      intro x hx
      refine HasDerivAt.hasDerivWithinAt ?_
      refine .add ?_ ?_
      · refine .inv ?_ (by linarith)
        exact (hasDerivAt_id x).const_add a
      · refine .inv ?_ (by linarith)
        exact (hasDerivAt_id x).const_sub a
    · -- Show that the second derivative is non-negative on `0 < x < a`.
      simp only [interior_Ioo, Set.mem_Ioo]
      intro x hx
      suffices ((a + x) ^ 2)⁻¹ ≤ ((a - x) ^ 2)⁻¹ by simpa [neg_div]
      refine inv_anti₀ ?_ ?_
      · rw [sq_pos_iff]
        linarith
      · rw [sq_le_sq₀] <;> linarith
