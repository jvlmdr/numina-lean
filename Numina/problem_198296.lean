-- https://cloud.kili-technology.com/label/projects/label/cm8ct0a8402do5kayleleob89

import Mathlib

open Polynomial

/- The reduced quadratic trinomial $f(x)$ has two distinct roots.
Can it happen that the equation $f(f(x)) = 0$ has three distinct roots,
and the equation $f(f(f(x))) = 0$ has seven distinct roots? -/

theorem algebra_198296 {f : ℝ → ℝ} (hf : ∃ b c, f = fun x ↦ x ^ 2 + b * x + c)
    (h1_card : {x | f x = 0}.encard = 2) :
    ¬({x | f (f x) = 0}.encard = 3 ∧ {x | f (f (f x)) = 0}.encard = 7) := by
  -- Since the problem specifies a *reduced* quadratic trinomial, we can assume `a = 1`.
  rcases hf with ⟨b, c, hf⟩
  rw [not_and]
  intro h2_card

  -- Each root `x` of `f (f (f x)) = 0` corresponds to a root `y = f x` of `f (f y) = 0`.
  -- We will show that there are at most two `x` for each `y`, hence at most 6 solutions.
  refine ne_of_lt ?_
  -- We have exactly two roots for `f x = 0`, and at most two roots for `f x - y = 0`.
  -- Use `Polynomial` to demonstrate this.
  have h1_sub_card (y) : {x | f x = y}.encard ≤ 2 := by
    calc _
    _ = {x | f x - y = 0}.encard := by simp [sub_eq_zero]
    _ = ((C 1 * X ^ 2 + C b * X + C (c - y)).roots.toFinset : Set ℝ).encard := by
      congr
      ext x
      simp only [hf, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset]
      rw [mem_roots (ne_zero_of_coe_le_degree (degree_quadratic one_ne_zero).ge)]
      simp [add_sub_assoc]
    _ = (C 1 * X ^ 2 + C b * X + C (c - y)).roots.toFinset.card :=
      Set.encard_coe_eq_coe_finsetCard _
    _ ≤ 2 := by
      -- We can now operate in `Nat` rather than `ENat`.
      rw [Nat.cast_le_ofNat]
      calc _
      _ ≤ (C 1 * X ^ 2 + C b * X + C (c - y)).roots.card := Multiset.toFinset_card_le _
      _ ≤ natDegree (C 1 * X ^ 2 + C b * X + C (c - y)) := card_roots' _
      _ = 2 := natDegree_quadratic one_ne_zero

  -- Establish finiteness of sets for use with `Set.Finite.toFinset`.
  have h2_fin : {x | f (f x) = 0}.Finite := Set.finite_of_encard_eq_coe h2_card
  have h1_fin (y) : {x | f x = y}.Finite := Set.finite_of_encard_le_coe (h1_sub_card y)

  calc _
  _ = Set.encard (⋃ y ∈ {y | f (f y) = 0}, {x | f x = y}) := by
    congr 1
    ext x
    simp
  -- Convert to `Finset` in order to take finite union of sets.
  _ = Set.encard (h2_fin.toFinset.biUnion (fun y ↦ (h1_fin y).toFinset) : Set ℝ) := by simp
  _ = Finset.card (h2_fin.toFinset.biUnion (fun y ↦ (h1_fin y).toFinset)) :=
    Set.encard_coe_eq_coe_finsetCard _
  -- There are at most 2 unique solutions per `y`.
  _ ≤ (h2_fin.toFinset.card * 2 : ℕ) := by
    rw [Nat.cast_le]
    refine Finset.card_biUnion_le_card_mul _ _ 2 fun y _ ↦ ?_
    rw [← ENat.coe_le_coe]
    rw [← (h1_fin y).encard_eq_coe_toFinset_card]
    exact h1_sub_card y
  -- There are at most 3 unique roots `y`.
  _ = (3 * 2 : ℕ) := by
    simp
    rw [← h2_fin.encard_eq_coe_toFinset_card]
    rw [h2_card]
    norm_num
  _ < 7 := by norm_num
