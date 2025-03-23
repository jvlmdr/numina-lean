-- https://cloud.kili-technology.com/label/projects/label/cm8cszy9501pe5kaysud7jjoa

import Mathlib

open scoped List

/- For any integers $x$ and $y$, the algebraic expression
$x^5 + 3 x^4 y - 5 x^3 y^2 - 15 x^2 y^3 + 4 x y^4 + 12 y^5$ cannot equal 33. -/
theorem algebra_138682 : ∀ x y : ℤ,
    x^5 + 3 * x^4 * y - 5 * x^3 * y^2 - 15 * x^2 * y^3 + 4 * x * y^4 + 12 * y^5 ≠ 33 := by
  intro x y
  -- Identify common factor of `x + 3 y` from the coefficients `(1, 3), (-5, -15), (4, 12)`:
  -- `(x^4 - 5 x^2 y^2 + 4 y^4) (x + 3 y)`
  -- Factor the quadratic in x^2 and y^2 (a b = 4, a + b = -5 → {a, b} = {-1, -4}:
  -- `(x^2 - y^2) (x^2 - 4 y^2) (x + 3 y)`
  -- `(x + y) (x - y) (x + 2 y) (x - 2 y) (x + 3 y)`
  have h_factor : x^5 + 3 * x^4 * y - 5 * x^3 * y^2 - 15 * x^2 * y^3 + 4 * x * y^4 + 12 * y^5 =
      (x + y) * (x - y) * (x + 2 * y) * (x - 2 * y) * (x + 3 * y) := by ring

  -- Since `(x + ·)` and `(· * y)` are injective, the factors are distinct.
  have h_nodup (hy : y ≠ 0) : [x + y, x - y, x + 2 * y, x - 2 * y, x + 3 * y].Nodup := by
    simp only [sub_eq_add_neg]
    suffices [y, -y, 2 * y, -2 * y, 3 * y].Nodup by simpa using this.map (add_right_injective x)
    suffices [1, -1, 2, -2, 3].Nodup by simpa using this.map (mul_left_injective₀ hy)
    norm_num

  -- We will be able to exclude the case `y = 0` since it implies that `x ^ 5 = 33`.
  have h_pow : x ^ 5 ≠ 33 := fun hx ↦ by
    -- Infeasible since 2 ^ 5 < x ^ 5 < 3 ^ 5 implies 2 < x < 3.
    have h5_odd : Odd 5 := ⟨2, rfl⟩
    have h2 : 2 < x := h5_odd.strictMono_pow.lt_iff_lt.mp <| by simp [hx]
    have h3 : x < 3 := h5_odd.strictMono_pow.lt_iff_lt.mp <| by simp [hx]
    linarith

  -- If there does exist some `(x, y)`, then we can construct a `Finset`
  -- These must all be divisors of 33, and thus a subset of {±1, ±3, ±11, ±33}.
  -- We will prove that all subsets of this set have an absolute product greater than 33.
  have h_imp_exists_finset (hy : y ≠ 0)
      (h : (x + y) * (x - y) * (x + 2 * y) * (x - 2 * y) * (x + 3 * y) = 33) :
      ∃ s : Finset ℤ, s.card = 5 ∧ (∀ z ∈ s, z ∣ 33) ∧ |∏ z in s, z| = 33 := by
    -- Since the factors are distinct, the product can be written using `List.toFinset`.
    have h_toFinset : ∏ z in [x + y, x - y, x + 2 * y, x - 2 * y, x + 3 * y].toFinset, z =
        (x + y) * (x - y) * (x + 2 * y) * (x - 2 * y) * (x + 3 * y) := by
      rw [List.prod_toFinset _ (h_nodup hy)]
      simp [mul_assoc]
    -- Use this finset to demonstrate existence.
    use [x + y, x - y, x + 2 * y, x - 2 * y, x + 3 * y].toFinset
    refine ⟨?_, ?_, ?_⟩
    · rw [List.toFinset_card_of_nodup (h_nodup hy)]
      norm_num
    · intro z hz
      rw [← h_toFinset.trans h]
      exact Finset.dvd_prod_of_mem _ hz
    · rw [h_toFinset.trans h]
      norm_num

  -- Define in analogy to `Nat.divisors`.
  have h_int_divisors (z : ℤ) : z ∣ 33 ↔ z ∈ ({-33, -11, -3, -1, 1, 3, 11, 33} : Finset ℤ) :=
    calc
    _ ↔ z ∈ (Finset.Icc (-33) 33).filter (· ∣ 33) := by
      rw [Finset.mem_filter, iff_and_self]
      intro hz
      rw [Finset.mem_Icc, ← abs_le]
      suffices (z.natAbs : ℤ) ≤ Int.natAbs 33 by simpa using this
      rw [Nat.cast_le]
      exact Int.natAbs_le_of_dvd_ne_zero hz (by norm_num)
    _ ↔ _ := .rfl

  -- Eliminate the case where `y = 0`.
  cases eq_or_ne y 0 with
  | inl hy => simpa [hy] using h_pow
  | inr hy =>
    rw [h_factor]
    refine mt (h_imp_exists_finset hy) ?_
    simp only [not_exists, not_and]
    intro s hs_card hs_dvd
    replace hs_dvd : s ⊆ {-33, -11, -3, -1, 1, 3, 11, 33} :=
      fun z hz ↦ (h_int_divisors z).mp (hs_dvd z hz)
    -- We will prove that the absolute product is greater than 33.
    refine ne_of_gt ?_
    rw [Finset.abs_prod]
    simp only [Int.abs_eq_natAbs]
    rw [← Finset.prod_natCast, Nat.ofNat_lt_cast]
    -- Switch to `Multiset` when taking the absolute value to permit duplicates.
    rw [Finset.prod_eq_multiset_prod]

    have h_le_multiset : s.val.map Int.natAbs ≤ Multiset.ofList [1, 1, 3, 3, 11, 11, 33, 33] :=
      calc
      _ ≤ (Finset.val {-33, -11, -3, -1, 1, 3, 11, 33}).map Int.natAbs := by
        refine Multiset.map_mono _ ?_
        exact Finset.val_le_iff.mpr hs_dvd
      _ = {33, 11, 3, 1, 1, 3, 11, 33} := rfl
      _ = Multiset.ofList [33, 11, 3, 1, 1, 3, 11, 33] := rfl
      _ = Multiset.ofList (.insertionSort (· ≤ ·) [33, 11, 3, 1, 1, 3, 11, 33]) := by
        rw [Multiset.coe_eq_coe]
        exact (List.perm_insertionSort _ _).symm
      _ = _ := by simp

    -- It suffices to show that the product of any subset is bounded below by
    -- the product of the first elements in a sorted list.
    suffices ∀ (s : Multiset ℕ) (l : List ℕ), l.Sorted (· ≤ ·) → s ≤ l →
        (l.take s.card).prod ≤ s.prod by
      refine lt_of_lt_of_le ?_ (this _ _ ?_ h_le_multiset)
      · simp only [Multiset.card_map, Finset.card_val, hs_card]
        norm_num
      · norm_num

    -- We can assume the elements of `s` to be ordered and a sublist of `l`.
    suffices ∀ (s l : List ℕ), l.Sorted (· ≤ ·) → s <+ l → (l.take s.length).prod ≤ s.prod by
      intro s l hl
      refine Quotient.inductionOn s fun s ↦ ?_
      simp only [Multiset.quot_mk_to_coe, Multiset.coe_le, Multiset.coe_card, Multiset.prod_coe]
      intro hsl
      convert this (s.insertionSort (· ≤ ·)) l hl ?_ using 1
      · rw [List.length_insertionSort]
      · exact (List.perm_insertionSort _ s).prod_eq.symm
      · refine List.sublist_of_subperm_of_sorted ?_ (List.sorted_insertionSort _ s) hl
        exact .trans (List.perm_insertionSort _ s).subperm hsl

    -- Now use induction to obtain a lower bound on the sublist product.
    intro s t ht hst
    induction hst with
    | slnil => simp
    | @cons₂ s t x hst IH =>
      -- The element `x` occurs in both lists. Apply induction to tail of both.
      rw [List.sorted_cons] at ht
      cases s with
      | nil => simp
      | cons a s => simpa using Nat.mul_le_mul_left x (IH ht.2)
    | @cons s t x hst IH =>
      -- The element `x` occurs in `t` but not in `s`.
      -- Show that first `n` elements of `x :: t` are less than those of `t`.
      have hxt_chain := ht.chain
      rw [List.sorted_cons] at ht
      refine le_trans (List.Forall₂.prod_le_prod' ?_) (IH ht.2)
      -- Use `List.Chain` (from `List.Pairwise`) to prove that `x[i] ≤ x[i + 1]`.
      have h_chain_take (n : ℕ) : List.Chain (· ≤ ·) x (t.take n) :=
        List.Chain'.take (l := x :: t) hxt_chain (n + 1)
      have := h_chain_take s.length
      cases s with
      | nil => simp
      | cons a s =>
        simp only [List.length_cons, List.take_succ_cons] at this ⊢
        cases List.chain_iff_forall₂.mp this with
        | inl ht =>
          have ht : t = [] := by simpa using ht
          -- Contradiction since `a :: s <+ t`.
          simp [ht] at hst
        | inr ht =>
          convert ht using 2
          rw [List.take_add, List.dropLast_append_of_ne_nil _ (by simpa using hst.length_le)]
          rw [List.self_eq_append_right]
          refine List.eq_nil_of_length_eq_zero ?_
          simp
