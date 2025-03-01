-- https://cloud.kili-technology.com/label/projects/label/cm7enil0200sizz8767l4ygty?userID=cm7ln00x0cbs001at7mnncm9v

import Mathlib

open Complex

/- How many complex numbers satisfy the equation z^5 = z'
where z' is the conjugate of the complex number z?
(A) 2
(B) 3
(C) 5
(D) 6
(E) 7 -/

theorem algebra_95577 : {z : ℂ | z ^ 5 = starRingEnd ℂ z}.ncard = 7 := by
  -- Either z = 0 or z ≠ 0.
  -- If z ≠ 0, then |z ^ 5| = |z|, hence z^5 * z = z' * z = 1.
  -- Therefore, we have z = 0 or the 6th roots of unity.
  have h_iff (z : ℂ) : z ^ 5 = starRingEnd ℂ z ↔ z ^ 6 = 1 ∨ z = 0 := by
    cases eq_or_ne z 0 with
    | inl h => simp [h]
    | inr h =>
      simp only [h, or_false]
      -- Have abs z = 1 on both sides and it will help with proof.
      -- Rather than proving it in both directions,
      -- introduce it as a clause on both sides to simplify the proof.
      calc _
      _ ↔ ‖z‖₊ = 1 ∧ z ^ 5 = (starRingEnd ℂ) z := by
        -- Use nnnorm to take advantage of `pow_eq_one_iff` (needs `MulLeftMono`).
        -- (Can't use `abs_pow_eq_one` because it needs `LinearOrderedRing`.)
        refine iff_and_self.mpr fun hz ↦ ?_
        replace hz : ‖z‖₊ ^ 5 = ‖z‖₊ := by simpa using congrArg nnnorm hz
        replace hz : ‖z‖₊ ^ 4 = 1 := by
          rw [pow_succ, mul_left_eq_self₀] at hz
          simpa [h] using hz
        exact (pow_eq_one_iff (by norm_num)).mp hz
      _ ↔ ‖z‖₊ = 1 ∧ z ^ 6 = 1 := by
        refine and_congr_right_iff.mpr ?_
        intro hz
        calc _
        _ ↔ z ^ 5 * z = (starRingEnd ℂ) z * z := by
          rw [mul_eq_mul_right_iff]
          simp [h]
        _ ↔ _ := by
          refine Eq.congr_right ?_
          rw [NNReal.eq_iff, coe_nnnorm] at hz
          rw [conj_mul', hz]
          simp
      _ ↔ _ := by
        refine and_iff_right_iff_imp.mpr ?_
        intro hz
        exact nnnorm_eq_one_of_pow_eq_one hz (by norm_num)

  simp_rw [h_iff]
  rw [Set.setOf_or, Set.setOf_eq_eq_singleton]
  -- Since the sets are disjoint, we have 1 + 6 = 7 roots.
  suffices {z : ℂ | z ^ 6 = 1}.ncard = 6 by
    rw [Set.ncard_union_eq ?_ ?_ ?_]
    · rw [this]
      norm_num
    · simp
    · refine Set.finite_of_ncard_ne_zero ?_
      rw [this]
      norm_num
    · simp

  -- Now we need to use the cardinality of the roots of unity.
  -- We have `Complex.card_rootsOfUnity : Fintype.card ↥(rootsOfUnity n ℂ)`.
  -- However, thise uses `Fintype.card`.
  -- Therefore, express in terms of `Polynomial.nthRoots 6 1` to get a `Finset`.
  calc _
  _ = Set.ncard ((Polynomial.nthRoots 6 (1 : ℂ)).toFinset : Set ℂ) := by
    refine congrArg _ ?_
    ext z
    simp
  _ = (Polynomial.nthRoots 6 (1 : ℂ)).toFinset.card := Set.ncard_coe_Finset _
  _ = Fintype.card { x // x ∈ (Polynomial.nthRoots 6 (1 : ℂ)).toFinset } := by simp
  _ = Fintype.card { x // x ∈ Polynomial.nthRoots 6 (1 : ℂ) } := by
    refine Fintype.card_congr ?_
    simp only [Multiset.mem_toFinset]
    rfl
  _ = Fintype.card (rootsOfUnity 6 ℂ) := by
    let e := rootsOfUnityEquivNthRoots ℂ 6
    exact (Fintype.card_congr e).symm
  _ = 6 := Complex.card_rootsOfUnity 6
