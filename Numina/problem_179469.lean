-- https://cloud.kili-technology.com/label/projects/label/cma3ygf2a0082ahay8i6cuqfo

import Mathlib

open scoped Finset

/- Determine the number of all pairs $(a, b)$ of single-digit natural numbers $a$ and $b$ for which
$a < \overline{a, b} < b$ holds! Here, 0 is considered a single-digit number, and $\overline{a, b}$
denotes the decimal number that has the digit $a$ before the decimal point and the digit $b$ after
the decimal point. -/

-- Any pair `(a, b)` satisfies `a < a.b < b` so long as `0 < b` and `a < b`.
-- Therefore it will suffice to count pairs of integers.
lemma add_div_between_iff {a b n : ℕ} (hn : 0 < n) (ha : a < n) (hb : b < n) :
    a < (a + b / n : ℚ) ∧ (a + b / n : ℚ) < b ↔ 0 < b ∧ a < b := by
  simp only [lt_add_iff_pos_right _]
  simp only [Nat.cast_pos, hn, div_pos_iff_of_pos_right]
  rw [and_congr_right_iff]
  intro hb_pos
  constructor
  · intro h
    suffices (a : ℚ) < (b : ℚ) from Nat.cast_lt.mp this
    refine lt_of_le_of_lt ?_ h
    simp [Rat.div_nonneg]
  · intro hab
    have hb : (b / n : ℚ) < 1 := by simp [div_lt_one, hn, hb]
    refine lt_of_lt_of_le (add_lt_add_left hb _) ?_
    suffices ↑(a + 1) ≤ (b : ℚ) by simpa
    exact Nat.cast_le.mpr hab

-- Taking the elements that satisfy `· < b` from `Finset.range` gives another `Finset.range`.
lemma range_filter_lt (n b : ℕ) :
    Finset.filter (· < b) (Finset.range n) = Finset.range (n ⊓ b) := by
  ext x
  simp

-- The number of pairs `(a, b)` with `a, b ∈ range n` and `a < b` is equal to `n * (n - 1) / 2`.
lemma card_prod_range_filter_lt (n : ℕ) :
    #{p ∈ Finset.range n ×ˢ Finset.range n | p.1 < p.2} = n * (n - 1) / 2 := by
  calc _
  _ = ∑ b ∈ Finset.range n, #(Finset.image (·, b) (Finset.filter (· < b) (Finset.range n))) := by
    rw [Finset.product_eq_biUnion_right, Finset.filter_biUnion]
    simp only [Finset.filter_image]
    apply Finset.card_biUnion
    intro x _ y _ hxy
    rw [Finset.disjoint_iff_ne]
    simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro p _ q _
    simp [hxy]
  _ = ∑ b in Finset.range n, b := by
    refine Finset.sum_congr rfl fun b hb ↦ ?_
    rw [Finset.mem_range] at hb
    rw [range_filter_lt, min_eq_right_of_lt hb]
    -- Since the construction of a product is injective, the cardinality is preserved.
    rw [Finset.card_image_of_injective _ (Prod.mk.inj_right b)]
    simp
  _ = _ := Finset.sum_range_id n

theorem number_theory_179469 :
    {(a, b) : ℕ × ℕ | a < 10 ∧ b < 10 ∧
      a < a + (b / 10 : ℚ) ∧ a + (b / 10 : ℚ) < b}.ncard = 45 := by
  calc _
  _ = {(a, b) : ℕ × ℕ | a < 10 ∧ b < 10 ∧ 0 < b ∧ a < b}.ncard := by
    congr 1
    ext ⟨a, b⟩
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    exact add_div_between_iff (by norm_num)
  -- Switch to finset to use the cardinality lemma.
  _ = (Finset.toSet {p ∈ Finset.range 10 ×ˢ Finset.range 10 | 0 < p.2 ∧ p.1 < p.2}).ncard := by
    simp [and_assoc]
  _ = #{p ∈ Finset.range 10 ×ˢ Finset.range 10 | 0 < p.2 ∧ p.1 < p.2} := Set.ncard_coe_Finset _
  -- Eliminate the condition `0 < b` since this contributes nothing to the sum.
  -- In fact, it can be eliminated by definitional equality.
  _ = #{p ∈ Finset.range 10 ×ˢ Finset.range 10 | p.1 < p.2} := rfl
  _ = 10 * 9 / 2 := card_prod_range_filter_lt 10
  _ = _ := by norm_num
