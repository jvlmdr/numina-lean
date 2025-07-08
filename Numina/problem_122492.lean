-- https://cloud.kili-technology.com/label/projects/label/cmcbovi8e00u4ueaxje65xtg4

import Mathlib

/- Let $b \geqslant 2$ be an integer. Prove, using a generating series, that every
natural number has a unique decomposition in base $b$. -/

theorem number_theory_122492 (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    ∃! l : List ℕ, (∀ x ∈ l, x < b) ∧ (∀ (h : l ≠ []), l.getLast h ≠ 0) ∧
      Nat.ofDigits b l = n := by
  -- The sole solution is the digits.
  refine ⟨Nat.digits b n, ?_, ?_⟩
  -- Show that all properties of the digits hold.
  · split_ands
    · exact fun x hx ↦ Nat.digits_lt_base hb hx
    · refine fun h ↦ Nat.getLast_digit_ne_zero b ?_
      exact Nat.digits_ne_nil_iff_ne_zero.mp h
    · exact Nat.ofDigits_digits b n
  -- Any `l` which is a valid list of digits will be recovered using `Nat.digits`.
  · rintro l ⟨h_elem, h_last, rfl⟩
    exact (Nat.digits_ofDigits b hb l h_elem h_last).symm
