-- https://cloud.kili-technology.com/label/projects/label/cm84mpwv601wiiev5wp9ihnmc
-- https://artofproblemsolving.com/wiki/index.php/2018_AIME_I_Problems/Problem_1

import Mathlib

open Polynomial

/- Let $S$ be the number of ordered pairs of integers $(a,b)$ with $1 \leq a \leq 100$ and
$b \geq 0$ such that the polynomial $x^2 + a x + b$ can be factored into the product of two
(not necessarily distinct) linear factors with integer coefficients.
Find the remainder when $S$ is divided by $1000$. -/

theorem algebra_67739 : Set.ncard {(a, b) : ℤ × ℤ | a ∈ Finset.Icc 1 100 ∧ 0 ≤ b ∧
    ∃ u v : ℤ, X ^ 2 + C a * X + C b = (X + C u) * (X + C v)} % 1000 = 600 := by

  suffices Set.ncard {(a, b) : ℤ × ℤ | a ∈ Finset.Icc 1 100 ∧ 0 ≤ b ∧
      ∃ u v : ℤ, X ^ 2 + C a * X + C b = (X + C u) * (X + C v)} = 2600 by
    rw [this]

  -- TODO: Put in `calc`?
  have (a b u v : ℤ) : X ^ 2 + C a * X + C b = (X + C u) * (X + C v) ↔ a = u + v ∧ b = u * v :=
    calc _
    -- Group the coefficients of the polynomial.
    _ ↔ X ^ 2 + C a * X + C b = X ^ 2 + C (u + v) * X + C (u * v) := by
      refine Eq.congr_right ?_
      simp only [map_add, map_mul]
      ring
    _ ↔ _ := by
      -- Reverse direction is trivial by substitution.
      refine ⟨?_, fun ⟨ha, hb⟩ ↦ by rw [ha, hb]⟩
      -- Use extensionality of polynomials to obtain the forward direction.
      rw [Polynomial.ext_iff]
      intro h
      exact ⟨by simpa [-eq_intCast] using h 1, by simpa [-eq_intCast] using h 0⟩
  simp only [this]

  calc {(a, b) : ℤ × ℤ | a ∈ Finset.Icc 1 100 ∧ 0 ≤ b ∧ ∃ u v, a = u + v ∧ b = u * v}.ncard

  -- We now need to count, for each `1 ≤ a ≤ 100`, the number of
  -- unique products `u v ≥ 0` such that `u + v = a`.
  -- Both `u` and `v` must be non-negative since their product is non-negative
  -- and their sum is positive. We can set `v = a - u`.

  -- `0 ≤ u * (a - u)` gives us `0 ≤ u` and `0 ≤ a - u`, equivalent to `0 ≤ u ≤ a`.
  -- (We cannot have `u ≤ 0` and `a - u ≤ 0`.)
  -- The unique elements of the set of `u * (a - u)` for `u ∈ [0, a]` are
  -- those where `u ≤ a - u`; that is, `2 * u ≤ a`.

  -- Split into even and odd cases, `a = 2 k` and `a = 2 k + 1`.

  _ = Set.ncard (⋃ a ∈ Finset.Icc 1 100, (a, ·) ''
      {b : ℤ | 0 ≤ b ∧ ∃ u v, a = u + v ∧ b = u * v}) := by
    congr
    ext ⟨a, b⟩
    simp only [Set.mem_iUnion, exists_prop]
    simp

  _ = Set.ncard (⋃ a ∈ (.Icc 1 100 : Finset ℤ),
      (a, ·) '' ((fun u ↦ u * (a - u)) '' Set.Icc 0 a)) := by
    congr
    refine Set.iUnion₂_congr ?_
    intro a ha
    refine congrArg _ ?_
    calc _
    _ = {b | 0 ≤ b ∧ ∃ u v, a - u = v ∧ b = u * v} := by simp only [sub_eq_iff_eq_add']
    _ = {b | 0 ≤ b ∧ ∃ u, b = u * (a - u)} := by simp
    _ = {b | ∃ u, 0 ≤ b ∧ b = u * (a - u)} := by simp
    _ = (fun u ↦ u * (a - u)) '' {u : ℤ | 0 ≤ u * (a - u)} := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_image]
      refine exists_congr fun u ↦ ?_
      rw [eq_comm (b := b)]
      refine and_congr_left fun hb ↦ ?_
      rw [hb]
    _ = (fun u ↦ u * (a - u)) '' {u : ℤ | 0 ≤ u ∧ u ≤ a} := by
      suffices ∀ u : ℤ, 0 ≤ u * (a - u) ↔ 0 ≤ u ∧ u ≤ a by simp only [this]
      intro u
      rw [mul_nonneg_iff]
      simp only [sub_nonneg, sub_nonpos]
      -- Eliminate the case where both factors are non-positive.
      refine or_iff_left_of_imp fun h ↦ ?_
      -- Contradiction since `a ≤ u ≤ 0` and `1 ≤ a`.
      exfalso
      simp only [Finset.mem_Icc] at ha
      linarith

  _ = ∑ a ∈ (.Icc 1 100 : Finset ℤ), ((fun u ↦ u * (a - u)) '' Set.Icc 0 a).ncard := by
    calc _
    _ = Finset.card (.biUnion (.Icc 1 100 : Finset ℤ) fun a ↦
        .map (.sectR a ℤ) (.image (fun u ↦ u * (a - u)) (.Icc 0 a))) := by
      rw [← Set.ncard_coe_Finset]
      simp
    _ = ∑ a ∈ (.Icc 1 100 : Finset ℤ),
        Finset.card (.map (.sectR a ℤ) (.image (fun u ↦ u * (a - u)) (.Icc 0 a))) := by
      refine Finset.card_biUnion ?_
      intro a₁ _ a₂ _ ha
      rw [Finset.disjoint_right]
      simp only [Finset.mem_map, Function.Embedding.sectR_apply, not_exists, not_and,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Prod.mk.injEq]
      intro m₁ _ m₂ _ hm
      contradiction
    _ = _ := by
      refine congrArg _ <| funext fun a ↦ ?_
      simp only [Finset.card_map]
      rw [← Set.ncard_coe_Finset]
      simp

  _ = ∑ a ∈ (.Icc 1 100 : Finset ℤ),
      ((fun u ↦ u * (a - u)) '' {u : ℤ | 0 ≤ u ∧ u ≤ a - u}).ncard := by
    refine congrArg _ <| funext fun a ↦ ?_
    congr
    ext b
    simp only [Set.mem_image, Set.mem_Icc, Set.mem_setOf_eq]
    refine ⟨?_, Exists.imp fun u ⟨⟨hu, hua⟩, hb⟩ ↦ ⟨⟨hu, le_trans hua (sub_le_self a hu)⟩, hb⟩⟩
    intro ⟨u, ⟨⟨hu, hua⟩, hb⟩⟩
    cases le_or_lt u (a - u) with
    | inl h => exact ⟨u, ⟨hu, h⟩, hb⟩
    | inr h =>
      refine ⟨a - u, ⟨?_, ?_⟩, ?_⟩
      · simpa using hua
      · simpa using h.le
      · simpa [mul_comm] using hb

  _ = ∑ a ∈ (.Icc 1 100 : Finset ℤ),
      ((fun u ↦ u * (a - u)) '' {u : ℤ | 0 ≤ u ∧ 2 * u ≤ a}).ncard := by
    -- TODO: Nest above.
    suffices ∀ a u : ℤ, u ≤ a - u ↔ 2 * u ≤ a by simp only [this]
    intro a u
    rw [two_mul]
    exact le_sub_iff_add_le'

  _ = ∑ a ∈ (.Icc 1 100 : Finset ℤ), {u : ℤ | 0 ≤ u ∧ 2 * u ≤ a}.ncard := by
    refine congrArg _ <| funext fun a ↦ ?_
    refine Set.ncard_image_of_injOn ?_
    refine StrictMonoOn.injOn ?_
    intro u₁ hu₁ u₂ hu₂ h
    simp only [Set.mem_setOf_eq] at hu₁ hu₂
    refine lt_of_sub_pos ?_
    calc u₂ * (a - u₂) - u₁ * (a - u₁)
    _ = (u₂ - u₁) * (a - (u₁ + u₂)) := by ring
    _ > 0 := mul_pos (sub_pos_of_lt h) (by omega)

  -- Switch from `Finset.Icc` in `ℤ` to `Finset.range` in `ℕ`.
  -- First change the outer sum.
  _ = ∑ a ∈ (.Icc 1 100 : Finset ℕ), {u : ℤ | 0 ≤ u ∧ 2 * u ≤ a}.ncard := by
    suffices (.Icc 1 100 : Finset ℤ) = .map Nat.castEmbedding (.Icc 1 100) by simp [this]
    ext n
    cases n with
    | ofNat n => simp
    | negSucc n => simp [Order.one_le_iff_pos]
  -- Now change the set inside the sum.
  _ = ∑ a ∈ .Icc 1 100, (Nat.castEmbedding '' {u | 2 * u ≤ a}).ncard := by
    refine congrArg _ <| funext fun a ↦ congrArg _ <| Set.ext fun u ↦ ?_
    cases u with
    | ofNat u => simp [← Nat.cast_le (α := ℤ)]
    | negSucc u => simp
  _ = ∑ a ∈ .Icc 1 100, {u | 2 * u ≤ a}.ncard := by
    simp_rw [Set.ncard_map Nat.castEmbedding]
  -- Now swap the `Icc` for `range`.
  _ = ∑ a ∈ .map (addRightEmbedding 1) (.Ico 0 100), {u | 2 * u ≤ a}.ncard := by
    rw [Finset.map_add_right_Ico, Nat.Ico_succ_right]
  _ = ∑ a ∈ .range 100, {u | 2 * u ≤ a + 1}.ncard := by simp

  -- Split `a` into even and odd cases.
  _ = ∑ m ∈ Finset.range 50 ×ˢ Finset.range 2, {u | 2 * u ≤ 2 * m.1 + m.2 + 1}.ncard := rfl
  _ = ∑ k ∈ .range 50, {u | 2 * u ≤ 2 * k + 1}.ncard +
      ∑ k ∈ .range 50, {u | 2 * u ≤ 2 * (k + 1)}.ncard := by
    rw [Finset.sum_product, Finset.sum_comm, Finset.sum_range, Fin.sum_univ_two]
    simp [mul_add]
  -- We have `2 u ≤ 2 k + 1` iff `u ≤ k`; and `2 u ≤ 2 (k + 1)` iff `u ≤ k + 1`.
  _ = ∑ k ∈ .range 50, {u | u ≤ k}.ncard + ∑ k ∈ .range 50, {u | u ≤ k + 1}.ncard := by
    congr
    · funext k
      suffices ∀ u, 2 * u ≤ 2 * k + 1 ↔ u ≤ k by simp [this]
      omega
    · simp
  -- Switch from `Set.ncard` to `Finset.card` for counts.
  _ = ∑ k ∈ .range 50, (Finset.Iic k).toSet.ncard +
      ∑ k ∈ .range 50, (Finset.Iic (k + 1)).toSet.ncard := by
    simp only [Finset.coe_Iic]
    rfl
  _ = ∑ k ∈ .range 50, (k + 1) + ∑ k ∈ .range 50, (k + 2) := by
    simp only [Set.ncard_coe_Finset]
    simp
  -- Use expressions for arithmetic series.
  _ = _ := by simp [Finset.sum_add_distrib, Finset.sum_range_id]
