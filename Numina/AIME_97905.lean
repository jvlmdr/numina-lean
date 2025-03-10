-- https://cloud.kili-technology.com/label/projects/label/cm7eni5b9001gzz87f0nwli2u
-- https://artofproblemsolving.com/wiki/index.php/2002_AIME_II_Problems/Problem_1

import Mathlib

open Pointwise

/- Given that
\begin{eqnarray*}
&(1)& x\text{ and }y\text{ are both integers between 100 and 999, inclusive;} \\
&(2)& y\text{ is the number formed by reversing the digits of }x\text{; and} \\
&(3)& z=|x-y|.
\end{eqnarray*}
How many distinct values of z are possible? -/
theorem number_theory_97905 :
    Set.ncard {z : ℤ | ∃ x y : ℕ, x ∈ Set.Ico 100 1000 ∧ y ∈ Set.Ico 100 1000 ∧
      Nat.digits 10 y = (Nat.digits 10 x).reverse ∧ z = |(x - y : ℤ)|} = 9 := by

  have h_sub_ofDigits (a b c : ℕ) :
      Nat.ofDigits (10 : ℕ) [c, b, a] - Nat.ofDigits (10 : ℕ) [a, b, c] = 99 * (a - c : ℤ) := by
    simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, Nat.cast_add, Nat.cast_mul]
    ring

  -- First re-parameterize in the digits `a` and `c`, where `x = abc` and `y = cba`.
  have h_param (z : ℤ) : (∃ x y : ℕ, x ∈ Set.Ico 100 1000 ∧ y ∈ Set.Ico 100 1000 ∧
        Nat.digits 10 y = (Nat.digits 10 x).reverse ∧ z = |(x - y : ℤ)|) ↔
      ∃ c a : ℕ, c ∈ Set.Ico 1 10 ∧ a ∈ Set.Ico 1 10 ∧ z = 99 * |(a - c : ℤ)| := by
    calc _
    -- Use `ofDigits 10 (digits 10 x) = x` to put everything in terms of digits.
    -- Re-parameterize `x = Nat.ofDigits 10 l` where `l = Nat.digits 10 x`.
    -- TODO: Use `List.enum` here?
    _ ↔ ∃ lx ly : List ℕ,
        lx ∈ {l | (∀ u ∈ l, u < 10) ∧ ∃ h : l.length = 3, l[2] ≠ 0} ∧
        ly ∈ {l | (∀ u ∈ l, u < 10) ∧ ∃ h : l.length = 3, l[2] ≠ 0} ∧
        ly = lx.reverse ∧ z = |(Nat.ofDigits (10 : ℕ) lx - Nat.ofDigits (10 : ℕ) ly : ℤ)| := by
      simp only [exists_and_left]
      -- Use `Set.BijOn.exists` to prove equivalence of different parameterizations.
      suffices Set.BijOn (Nat.digits 10) (Set.Ico 100 1000)
          {l | (∀ u ∈ l, u < 10) ∧ ∃ h : l.length = 3, l[2] ≠ 0} by
        rw [this.exists]
        refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
        rw [this.exists]
        refine exists_congr fun y ↦ and_congr_right fun hy ↦ ?_
        simp only [Nat.ofDigits_digits]
      -- TODO: Might be easier to use...
      -- LeftInvOn.surjOn (requires MapsTo)
      -- InvOn.bijOn (requires both inverses, both mapstos)
      -- Will need to make use of...
      -- `Nat.ofDigits_digits`, `Nat.digits.injective`, and then...
      -- `Nat.digits_ofDigits`? `Nat.ofDigits_inj_of_len_eq`?

      refine ⟨?_, (Nat.digits.injective 10).injOn, ?_⟩
      · -- Set.MapsTo (Nat.digits 10) (Set.Ico 100 1000)
        --   {l | (∀ u ∈ l, u < 10) ∧ ∃ (h : l.length = 3), l[2] ≠ 0}
        sorry
      · -- Set.SurjOn (Nat.digits 10) (Set.Ico 100 1000)
        --   {l | (∀ u ∈ l, u < 10) ∧ ∃ (h : l.length = 3), l[2] ≠ 0}
        intro l
        simp
        sorry

    -- The following form is easier for the next step.
    -- (The length constraint is extricated from the `getLast` constraint.)
    _ = ∃ lx ly : List ℕ,
        lx.length = 3 ∧ (∀ i u, (i, u) ∈ lx.enum → u < 10 ∧ (i + 1 = lx.length → u ≠ 0)) ∧
        ly.length = 3 ∧ (∀ i u, (i, u) ∈ ly.enum → u < 10 ∧ (i + 1 = lx.length → u ≠ 0)) ∧
        z = |(Nat.ofDigits (10 : ℕ) lx - Nat.ofDigits (10 : ℕ) ly : ℤ)| ∧ ly = lx.reverse := by
      -- Proof depends on final form of previous step.
      sorry

    -- Re-parameterize again using `Fin 3 → ℕ` rather than `List ℕ`.
    _ ↔ ∃ u v : Fin 3 → ℕ, ((∀ i, u i < 10) ∧ u 2 ≠ 0) ∧ ((∀ i, v i < 10) ∧ v 2 ≠ 0) ∧
        z = |(Nat.ofDigits (10 : ℕ) [u 0, u 1, u 2] - Nat.ofDigits (10 : ℕ) [v 0, v 1, v 2] : ℤ)| ∧
        v = u ∘ Fin.rev := by
      -- Use `List.equivSigmaTuple`: equivalence between `List ℕ` and `(n : ℕ) × (Fin n → ℕ)`.
      -- Then combine this with the condition that `l.length = 3` to obtain `Fin 3 → ℕ`.
      simp only [exists_and_left, List.equivSigmaTuple.exists_congr_left, Sigma.exists,
        List.equivSigmaTuple_symm_apply, List.length_ofFn, exists_eq_left]
      -- We need this condition for both variables.
      have h_iff (n : ℕ) (u : Fin n.succ → ℕ) (p q : ℕ → Prop) :
          (∀ i xi, (i, xi) ∈ (List.ofFn u).enum → p xi ∧ (i = n → q xi)) ↔
          (∀ i : Fin n.succ, p (u i)) ∧ q (u (Fin.last n)) := by
        -- Separate the two conditions.
        simp only [forall₂_and, forall_and]
        refine and_congr ?_ ?_
        · simp only [List.mk_mem_enum_iff_getElem?, Fin.forall_iff]
          simp [-List.ofFn_succ]
        · simp only [List.mk_mem_enum_iff_getElem?, Fin.last, Nat.reduceEqDiff]
          -- Re-order conditions to substitute `i = n`.
          rw [forall_comm]
          conv => lhs; intro u i; rw [forall_comm (β := i = n)]
          simp [-List.ofFn_succ]
      refine exists_congr fun u ↦ and_congr ?_ ?_
      · simpa only [Nat.reduceEqDiff] using h_iff 2 u (· < 10) (· ≠ 0)
      refine exists_congr fun v ↦ and_congr ?_ ?_
      · simpa only [Nat.reduceEqDiff] using h_iff 2 v (· < 10) (· ≠ 0)
      refine and_congr ?_ ?_
      · simp
      · simp [funext_iff, Fin.forall_fin_succ, Fin.rev_eq]

    -- Reduce to a single set of digits using the reverse constraint.
    _ ↔ ∃ u : Fin 3 → ℕ, (∀ i, u i < 10) ∧ u 2 ≠ 0 ∧ u 0 ≠ 0 ∧ z = |99 * (u 2 - u 0 : ℤ)| := by
      refine exists_congr fun u ↦ ?_
      -- Extract common conditions.
      simp only [exists_and_left, and_assoc]
      refine and_congr_right fun h_lt ↦ and_congr_right fun h2_ne ↦ ?_
      -- Re-arrange and use `exists_eq_right` to make substitution.
      simp only [← and_assoc]
      rw [exists_eq_right]
      simp only [Function.comp_apply, h_lt, implies_true, true_and]
      refine and_congr_right fun h0_ne ↦ Eq.congr_right ?_
      congr
      exact h_sub_ofDigits _ _ _
    -- Pull the factor of 99 out of the absolute value.
    _ ↔ ∃ u : Fin 3 → ℕ, (∀ i, u i < 10) ∧ u 2 ≠ 0 ∧ u 0 ≠ 0 ∧ z = 99 * |(u 2 - u 0 : ℤ)| := by
      simp only [abs_mul, Nat.abs_ofNat]
    -- Separate into three variables.
    _ ↔ ∃ c b a : ℕ, c ∈ Set.Ico 1 10 ∧ b < 10 ∧ a ∈ Set.Ico 1 10 ∧ z = 99 * |(a - c : ℤ)| := by
      -- Remove the first element.
      simp only [Fin.exists_fin_succ_pi (n := 2), Fin.forall_fin_succ (n := 2), Fin.cons_zero,
        ← Fin.succ_one_eq_two, Fin.cons_succ]
      refine exists_congr fun c ↦ ?_
      simp only [Fin.exists_fin_succ_pi (n := 1), Fin.forall_fin_succ (n := 1), Fin.cons_zero,
        ← Fin.succ_zero_eq_one, Fin.cons_succ]
      refine exists_congr fun b ↦ ?_
      simp only [Fin.exists_fin_succ_pi, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
      refine exists_congr fun a ↦ ?_
      simp only [Fin.exists_fin_zero_pi, IsEmpty.forall_iff, and_true]
      -- Just need to reorder the elements.
      simp only [← Nat.pos_iff_ne_zero]
      refine ⟨?_, ?_⟩
      · intro ⟨⟨hc_lt, hb_lt, ha_lt⟩, ha_pos, hc_pos, hz⟩
        exact ⟨⟨hc_pos, hc_lt⟩, hb_lt, ⟨ha_pos, ha_lt⟩, hz⟩
      · intro ⟨⟨hc_pos, hc_lt⟩, hb_lt, ⟨ha_pos, ha_lt⟩, hz⟩
        exact ⟨⟨hc_lt, hb_lt, ha_lt⟩, ha_pos, hc_pos, hz⟩
    -- Eliminate `b`.
    _ ↔ ∃ c a : ℕ, c ∈ Set.Ico 1 10 ∧ a ∈ Set.Ico 1 10 ∧ z = 99 * |(a - c : ℤ)| := by
      have hb : ∃ b, b < 10 := ⟨0, Nat.zero_lt_succ 9⟩
      simp [hb]

  -- Now we can reduce the problem to the size of `{|a - c| | c, a ∈ [1, 10]}`.
  calc _
  _ = Set.ncard {z : ℤ | ∃ c a : ℕ, c ∈ Set.Ico 1 10 ∧ a ∈ Set.Ico 1 10 ∧
      z = 99 * |(a - c : ℤ)|} := by
    rw [Set.ext h_param]
  -- Switch to `Icc` (easier for pointwise subtraction).
  _ = Set.ncard {z : ℤ | ∃ c a : ℕ, c ∈ Set.Icc 1 9 ∧ a ∈ Set.Icc 1 9 ∧
      z = 99 * |(a - c : ℤ)|} := by
    simp only [← Order.Ico_succ_right 1 9]
    rfl

  -- TODO: Remove ncards...

  -- Rewrite as image of product.
  _ = Set.ncard ((fun x : ℕ × ℕ ↦ 99 * |(x.2 - x.1 : ℤ)|) '' Set.Icc 1 9 ×ˢ Set.Icc 1 9) := by
    congr
    ext z
    simp only [Set.mem_setOf, Prod.exists, Set.mem_image, Set.mem_prod]
    simp [and_assoc, eq_comm]
  -- Switch to integers.
  _ = Set.ncard (((fun x : ℤ × ℤ ↦ 99 * |x.2 - x.1|) ∘ (Prod.map (↑) (↑))) ''
      Set.Icc 1 9 ×ˢ Set.Icc 1 9) := by rfl
  -- Rewrite as image of product.
  _ = Set.ncard ((fun x : ℤ × ℤ ↦ 99 * |x.2 - x.1|) ''
      (Nat.cast '' Set.Icc 1 9) ×ˢ (Nat.cast '' Set.Icc 1 9)) := by
    rw [Set.image_comp]
    refine congrArg Set.ncard <| congrArg _ ?_
    -- Our version of Mathlib does not have `Set.prodMap_image_prod`.
    ext x
    rcases x with ⟨c, a⟩
    simp only [Set.mem_prod, Set.mem_image, Prod.exists]
    simp only [Prod.map_apply, Prod.mk.injEq, and_and_and_comm]
    simp
  _ = Set.ncard ((fun x : ℤ × ℤ ↦ 99 * |x.2 - x.1|) '' Set.Icc 1 9 ×ˢ Set.Icc 1 9) := by
    suffices Nat.cast '' Set.Icc 1 9 = (Set.Icc 1 9 : Set ℤ) by rw [this]
    simpa using Nat.image_cast_int_Icc 1 9
  -- Eliminate the factor of 99 to reduce clutter.
  _ = Set.ncard (((99 * · ) ∘ fun x : ℤ × ℤ ↦ |x.2 - x.1|) '' Set.Icc 1 9 ×ˢ Set.Icc 1 9) := rfl
  _ = Set.ncard ((fun x : ℤ × ℤ ↦ |x.2 - x.1|) '' Set.Icc 1 9 ×ˢ Set.Icc 1 9) := by
    rw [Set.image_comp]
    refine Set.ncard_image_of_injective _ ?_
    exact mul_right_injective₀ (by norm_num)
  _ = Set.ncard (Set.Icc (0 : ℤ) 8) := by
    -- Find the range of absolute differences for a, c ∈ [1, 9].
    refine congrArg _ ?_
    calc _
    _ = (abs ∘ fun x : ℤ × ℤ ↦ x.2 - x.1) '' Set.Icc 1 9 ×ˢ Set.Icc 1 9 := by simp
    _ = (abs ∘ fun x : ℤ × ℤ ↦ x.1 - x.2) '' Set.Icc 1 9 ×ˢ Set.Icc 1 9 := by
      simp only [Set.image_comp]
      -- Need to swap...
      sorry
    _ = abs '' (Set.Icc 1 9 - Set.Icc 1 9) := by
      rw [Set.image_comp, Set.sub_image_prod]
    _ = abs '' (Set.Icc 1 9 + Set.Icc (-9) (-1)) := by
      refine congrArg _ ?_
      rw [sub_eq_add_neg]
      congr
      exact Set.neg_Icc 1 9
    _ = abs '' (Set.Icc (-8) 8) := by rw [Set.Icc_add_Icc] <;> norm_num
    _ = Set.Icc 0 8 := by
      suffices ∀ b : ℕ, abs '' (Set.Icc (-b : ℤ) b) = Set.Icc (0 : ℤ) b from this 8
      intro b
      ext x
      constructor
      · simp only [Set.mem_image, forall_exists_index, and_imp]
        simp only [Set.mem_Icc]
        refine fun u hu ↦ ?_
        revert x
        simp only [forall_eq', abs_nonneg, true_and]
        exact abs_le.mpr hu
      · simp only [Set.mem_image]
        refine fun hx ↦ ⟨x, ?_, ?_⟩
        · refine Set.Icc_subset_Icc ?_ ?_ hx <;> simp
        · exact abs_eq_self.mpr (hx.1)
  -- Now it just remains to count the elements of [0, 8].
  _ = Set.ncard (Finset.Icc (0 : ℤ) 8).toSet := by simp
  _ = _ := by
    rw [Set.ncard_coe_Finset]
    simp
