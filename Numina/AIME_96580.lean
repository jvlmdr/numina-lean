-- https://cloud.kili-technology.com/label/projects/label/cm7vmsof10001syay3fny2a4x
-- https://artofproblemsolving.com/wiki/index.php/1996_AIME_Problems/Problem_11

import Mathlib

open Complex
open scoped Real

/- Let P be the product of the roots of
z^6 + z^4 + z^3 + z^2 + 1 = 0
that have a positive imaginary part, and suppose that
P = r(cos θ ∘ + i sin θ ∘), where 0 < r and 0 ≤ θ < 360. Find θ. -/

theorem algebra_96580 :
    ∃ (h : Set.Finite {z : ℂ | z ^ 6 + z ^ 4 + z ^ 3 + z ^ 2 + 1 = 0 ∧ 0 < z.im}),
      toIcoMod Real.two_pi_pos 0 (∏ z in h.toFinset, z).arg = 2 * π * (276 / 360) := by

  -- First show that we can factor the polynomial.
  -- We can safely assume that `z ≠ 1` since `0 < z.im`.
  have h_factor {z : ℂ} (hz : z ≠ 1) : z ^ 6 + z ^ 4 + z ^ 3 + z ^ 2 + 1 =
      (z ^ 2 - z + 1) * (z ^ 5 - 1) / (z - 1) :=
    calc
    _ = z ^ 6 - z + (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) := by ring
    _ = z * (z ^ 5 - 1) + (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) * (z - 1) / (z - 1) := by
      congr
      · ring
      · rw [mul_div_cancel_right₀ _ (sub_ne_zero_of_ne hz)]
    _ = z * (z ^ 5 - 1) + (z ^ 5 - 1) / (z - 1) := by ring
    _ = (z * (z ^ 5 - 1) * (z - 1) + (z ^ 5 - 1)) / (z - 1) := by
      rw [add_div]
      rw [mul_div_cancel_right₀ _ (sub_ne_zero_of_ne hz)]
    _ = _ := by ring

  -- Therefore the roots will satisfy either `z ^ 5 = 1` or `z ^ 2 - z + 1 = 0`.
  -- Of these, the roots with positive imaginary part are
  -- `z = (1 + √3 * I) / 2 = exp (2πI / 6)`
  -- `z = exp (2πI / 5) ^ {1, 2}`
  -- The arg of the product is the sum of the args:
  -- `1/6 + 1/5 + 2/5 = 23 / 30 = 276 / 360`

  -- First, consider the solutions to the quadratic.
  have h_quad (z : ℂ) : z ^ 2 - z + 1 = 0 ∧ 0 < z.im ↔ z = (1 + √3 * I) / 2 := by
    -- Pull out `0 < z.im` as a common assumption via `and_congr_left`.
    suffices 0 < z.im → (z ^ 2 - z + 1 = 0 ↔ z = (1 + √3 * I) / 2) by
      rw [and_congr_left this]
      exact and_iff_left_of_imp fun hz ↦ by simp [hz]
    intro hz_im
    -- Factor the quadratic.
    have h_discrim : discrim 1 (-1) 1 = (√3 * I) * (√3 * I) := by
      rw [discrim, ← pow_two, mul_pow, ← ofReal_pow]
      norm_num
    have h_solve : z ^ 2 - z + 1 = 0 ↔ z = (1 + √3 * I) / 2 ∨ z = (1 - √3 * I) / 2 := by
      simpa [pow_two] using quadratic_eq_zero_iff one_ne_zero h_discrim z
    rw [h_solve]
    -- Eliminate the invalid solution.
    refine or_iff_left ?_
    refine mt (fun hz ↦ not_lt.mp ?_) (not_le.mpr hz_im)
    simp [hz]

  -- Next, consider the roots of unity.
  -- Obtain all of the roots of `z ^ n = 1` in `ℂ` rather than `ℂˣ`.
  -- Take this opportunity to write the complex exponential as `ofReal _ * I`.
  have h_rootsOfUnity (n : ℕ) [NeZero n] {z : ℂ} :
      z ^ n = 1 ↔ ∃ i < n, exp (↑(2 * π * (i / n)) * I) = z := by
    suffices z ≠ 0 → (z ^ n = 1 ↔ ∃ k < n, cexp (↑(2 * π * (k / n)) * I) = z) by
      -- Show that the conditions on both sides encompass `z ≠ 0`.
      refine (iff_congr ?_ ?_).mp (and_congr_left this)
      · simp only [and_iff_left_iff_imp]
        intro h hz
        simp [hz, NeZero.ne n] at h
      · simp only [and_iff_left_iff_imp, forall_exists_index, and_imp]
        intro k hk hz
        simp [← hz]
    -- Use the condition that `z ≠ 0` to construct a member of `ℂˣ`.
    intro hz
    have := (mem_rootsOfUnity' n (Units.mk0 z hz)).symm
    simp only [Complex.mem_rootsOfUnity, Units.val_mk0] at this
    refine .trans this ?_
    -- Change the form inside the complex exponential.
    suffices ∀ k : ℕ, 2 * π * I * (k / n) = ↑(2 * π * (k / n)) * I by simp_rw [this]
    intro k
    simp only [ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_natCast]
    ring

  -- Obtain the condition for `0 < sin x` with `x = 2 * π * (i / n)`.
  have h_sin_pos {n : ℕ} (hn_pos : 0 < n) (i : ℕ) (hin : i < n) :
      0 < Real.sin (2 * π * (i / n)) ↔ 0 < i ∧ 2 * i < n := by
    -- We have `Real.sin_pos_of_pos_of_lt_pi` and `Real.sin_nonpos_of_nonnpos_of_neg_pi_le`.
    -- However, they consider `Real.sin x` for `x ∈ [-π, 0]` and we have `x ∈ [0, 2π)`.
    -- Split into cases for `[0, π)` and `[π, 2π)`.
    cases lt_or_le (2 * i) n with
    | inl hi =>
      simp only [hi, and_true]
      cases i.eq_zero_or_pos with
      | inl hi => simp [hi]
      | inr hi_pos =>
        simp only [hi_pos, iff_true]
        -- Change the form to make proving the bounds easier.
        suffices 0 < Real.sin ((2 * i) / n * π) by
          convert this using 2
          ring
        refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
        · simpa [Real.pi_pos, Nat.cast_pos.mpr hn_pos] using hi_pos
        · refine mul_lt_of_lt_one_left Real.pi_pos ?_
          rw [div_lt_one (Nat.cast_pos.mpr hn_pos)]
          simpa using (Nat.cast_lt (α := ℝ)).mpr hi
    | inr hi =>
      simp only [not_lt_of_le hi, and_false, iff_false, not_lt]
      -- Subtract 2π to ensure `θ ∈ Set.Ico (-π) π`.
      rw [← Real.sin_periodic.sub_eq]
      -- TODO: Change form to make this easier to prove?
      -- e.g. `2 * (i / n - 1) * π ∈ Set.Icc (-π) 0`
      refine Real.sin_nonpos_of_nonnpos_of_neg_pi_le ?_ ?_
      · rw [sub_nonpos]
        refine mul_le_of_le_one_right Real.two_pi_pos.le ?_
        rw [div_le_one₀ (Nat.cast_pos.mpr hn_pos)]
        simpa using hin.le
      · rw [le_sub_iff_add_le']
        rw [two_mul, add_neg_cancel_right, ← two_mul]
        rw [← mul_rotate]
        refine le_mul_of_one_le_left Real.pi_nonneg ?_
        rw [div_mul_eq_mul_div, mul_comm _ 2]
        rw [one_le_div₀ (Nat.cast_pos.mpr hn_pos)]
        simpa using (Nat.cast_le (α := ℝ)).mpr hi

  -- Put these together to obtain a subset of the roots of unity.
  have h_rootsOfUnity_im_pos (z : ℂ) : z ^ 5 = 1 ∧ 0 < z.im ↔
      z = cexp (↑(2 * π * (1 / 5)) * I) ∨ z = cexp (↑(2 * π * (2 / 5)) * I) := by
    calc _
    _ ↔ ∃ k : ℕ, k < 5 ∧ cexp (↑(2 * π * (k / 5)) * I) = z ∧ 0 < z.im := by
      rw [h_rootsOfUnity]
      simp only [← and_assoc, exists_and_right, Nat.cast_ofNat]
    -- Move the definition of `z` to the right; use to obtain expression for `z.im`.
    _ ↔ ∃ k : ℕ, k < 5 ∧ 0 < z.im ∧ cexp (↑(2 * π * (k / 5)) * I) = z := by simp only [and_comm]
    _ ↔ ∃ k : ℕ, k < 5 ∧ 0 < Real.sin (2 * π * (k / 5)) ∧ cexp (↑(2 * π * (k / 5)) * I) = z := by
      refine exists_congr fun k ↦ ?_
      simp only [and_congr_right_iff, and_congr_left_iff]
      intro hk hz
      rw [← hz, exp_ofReal_mul_I_im]
    -- Use the condition for `0 < sin(x)`.
    _ ↔ ∃ k : ℕ, k ∈ Set.Icc 1 2 ∧ cexp (↑(2 * π * (k / 5)) * I) = z := by
      refine exists_congr fun k ↦ ?_
      simp only [← and_assoc, and_congr_left_iff]
      intro hz
      suffices k < 5 → (0 < Real.sin (2 * π * (↑k / 5)) ↔ k ∈ Set.Icc 1 2) by
        rw [and_congr_right this, Set.mem_Icc]
        refine and_iff_right_of_imp fun h ↦ ?_
        linarith
      intro hk
      convert h_sin_pos (by norm_num) k hk
      -- Use linarith in both directions.
      rw [Set.mem_Icc]
      constructor
      · refine fun _ ↦ ⟨?_, ?_⟩ <;> linarith
      · refine fun _ ↦ ⟨?_, ?_⟩ <;> linarith
    -- Enumerate `Icc 1 2` to obtain the two solutions.
    _ ↔ z = cexp (↑(2 * π * (1 / 5)) * I) ∨ z = cexp (↑(2 * π * (2 / 5)) * I) := by
      simp [Nat.le_and_le_add_one_iff, eq_comm (b := z)]

  -- Put these results together to obtain the finite set of solutions explicitly.
  have h_finset : {z : ℂ | z ^ 6 + z ^ 4 + z ^ 3 + z ^ 2 + 1 = 0 ∧ 0 < z.im} =
      Finset.image (fun x : ℝ ↦ exp (↑(2 * π * x) * I)) {1 / 6, 1 / 5, 2 / 5} := by
    calc _
    _ = {z : ℂ | (z ^ 2 - z + 1 = 0 ∨ z ^ 5 = 1) ∧ 0 < z.im} := by
      ext z
      simp only [Set.mem_setOf, and_congr_left_iff]
      intro hz
      have hz1 : z ≠ 1 := mt (fun h ↦ by simp [h]) hz.ne
      rw [h_factor hz1, div_eq_zero_iff]
      simp [sub_ne_zero_of_ne hz1, sub_eq_zero]
    _ = {z : ℂ | z ^ 2 - z + 1 = 0 ∧ 0 < z.im} ∪ {z : ℂ | z ^ 5 = 1 ∧ 0 < z.im} := by
      simp only [or_and_right]
      rfl
    -- Give the explicit form of the two solutions.
    _ = ↑(Finset.image (fun x ↦ cexp (↑(2 * π * x) * I)) ({1 / 6} ∪ {1 / 5, 2 / 5})) := by
      rw [Finset.image_union, Finset.coe_union]
      congr
      · simp only [Finset.image_singleton, Finset.coe_singleton]
        ext z
        simp only [Set.mem_setOf, Set.mem_singleton_iff]
        -- Use the solutions to `z ^ 2 - z + 1 = 0`.
        convert h_quad z using 2
        refine ext ?_ ?_
        · rw [exp_ofReal_mul_I_re]
          convert Real.cos_pi_div_three using 2
          · ring
          · simp
        · rw [exp_ofReal_mul_I_im]
          convert Real.sin_pi_div_three using 2
          · ring
          · simp
      · simp only [Finset.image_insert, Finset.image_singleton, Finset.coe_pair]
        ext z
        simp only [Set.mem_setOf, Set.mem_insert_iff, Set.mem_singleton_iff]
        -- Use the solutions to `z ^ 5 = 1`.
        exact h_rootsOfUnity_im_pos z
    _ = _ := by rfl

  rw [h_finset]
  refine ⟨Finset.finite_toSet _, ?_⟩
  rw [Finset.finite_toSet_toFinset]

  -- Prove that `x ↦ exp (2 * π * x * I)` is an injection on [0, π].
  rw [Finset.prod_image]
  swap
  · intro x hx y hy h
    suffices ↑(2 * π * x) * I = ↑(2 * π * y) * I by simpa [Real.pi_ne_zero] using this
    have h_neg_pi_lt : ∀ x ∈ ({1 / 6, 1 / 5, 2 / 5} : Finset ℝ), -π < 2 * π * x := fun x hx ↦ by
      suffices -1 < 2 * x by simpa [mul_assoc, mul_comm π] using
        (mul_lt_mul_right Real.pi_pos).mpr this
      revert x
      norm_num
    have h_lt_pi : ∀ x ∈ ({1 / 6, 1 / 5, 2 / 5} : Finset ℝ), 2 * π * x ≤ π := fun x hx ↦ by
      suffices 2 * x ≤ 1 by simpa [mul_assoc, mul_comm π] using
        (mul_le_mul_right Real.pi_pos).mpr this
      revert x
      norm_num
    refine exp_inj_of_neg_pi_lt_of_le_pi ?_ ?_ ?_ ?_ h
    · simpa using h_neg_pi_lt x hx
    · simpa using h_lt_pi x hx
    · simpa using h_neg_pi_lt y hy
    · simpa using h_lt_pi y hy

  have h_prod_exp_mul_I (s : Finset ℝ) :
      ∏ a in s, cexp (↑(2 * π * a) * I) = cexp (↑(2 * π * ∑ a in s, a) * I) := by
    induction s using Finset.induction with
    | empty => simp
    | @insert a s ha IH =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, IH, ← exp_add]
      congr
      simp only [ofReal_mul, ofReal_add]
      ring

  rw [h_prod_exp_mul_I, arg_exp_mul_I, toIcoMod_toIocMod]
  have h_sum : ∑ a ∈ {1 / 6, 1 / 5, 2 / 5}, a = (276 / 360 : ℝ) := by norm_num
  rw [h_sum]
  refine (toIcoMod_eq_self Real.two_pi_pos).mpr ⟨?_, ?_⟩
  · simp [Real.pi_nonneg]
  · simp only [zero_add]
    exact mul_lt_of_lt_one_right Real.two_pi_pos (by norm_num)
