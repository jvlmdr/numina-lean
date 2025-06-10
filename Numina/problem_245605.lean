-- https://cloud.kili-technology.com/label/projects/review/cmbj2mmny000nv7ayeaimuiqo

import Mathlib

open Nat
open scoped Finset List

/- Represent the number 100 as the sum of the maximum possible number of pairwise coprime natural
numbers. Explanation: the condition means that the greatest common divisor of any two numbers used
in the sum is 1. -/

-- Trivial but useful lemma for obtaining `nth` from `count` for `DecidablePred p`.
-- Note that `count` can be rewritten as the cardinality of a finset.
lemma nth_eq_of_count_eq {p : ℕ → Prop} [DecidablePred p]
    {n x : ℕ} (h_count : count p x = n) (hpx : p x) : nth p n = x :=
  h_count ▸ nth_count hpx

-- Obtain `n` such that `nth p n = x`.
lemma exists_nth_of_infinite {p : ℕ → Prop} (hp : (setOf p).Infinite) {x : ℕ} (hx : p x) :
    ∃ n, nth p n = x := by
  change x ∈ Set.range (nth p)
  rw [range_nth_of_infinite hp]
  exact hx

-- The image of `range n` under `nth p` can be rewritten as `filter` of `range (nth p n)`.
lemma image_nth_range_of_infinite {p : ℕ → Prop} [DecidablePred p] (hp : (setOf p).Infinite)
    (n : ℕ) :
    Finset.image (nth p) (Finset.range n) = {x ∈ Finset.range (nth p n) | p x} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter]
  constructor
  · rintro ⟨y, hyn, rfl⟩
    refine ⟨?_, ?_⟩
    · exact (nth_lt_nth hp).mpr hyn
    · refine nth_mem _ ?_
      intro hp'
      exfalso
      exact hp hp'
  · intro ⟨hx, hpx⟩
    obtain ⟨i, rfl⟩ : ∃ i, nth p i = x := exists_nth_of_infinite hp hpx
    refine ⟨i, ?_, rfl⟩
    exact (nth_lt_nth hp).mp hx

-- If `s` is pairwise coprime and contains 0, then it cannot contain anything else besides 1.
-- This follows from `gcd 0 x = x`.
lemma subset_of_coprime_of_zero_mem {s : Finset ℕ} (hs : Set.Pairwise s Coprime)
    (h : 0 ∈ s) : s ⊆ {0, 1} := by
  intro y hy
  specialize @hs y hy 0 h
  contrapose! hs
  simpa using hs

-- The `minFac` function is injective if all numbers are pairwise coprime.
lemma injOn_minFac_of_coprime {s : Set ℕ} (hs : Set.Pairwise s Coprime) :
    Set.InjOn minFac s := by
  intro x hx y hy h_minFac
  specialize hs hx hy
  contrapose! h_minFac with h_ne
  -- TODO: avoid doing specialize / contrapose! this twice?
  specialize hs h_ne
  contrapose! h_ne with h_minFac
  suffices x = 1 ∧ y = 1 by simp [this]
  suffices x.minFac = 1 ∧ y.minFac = 1 by simpa
  suffices x.minFac = 1 by simpa [← h_minFac]
  have h_dvd : ∀ (c : ℕ), c ∣ x → c ∣ y → c = 1 := by
    simpa [coprime_iff_gcd_eq_one, gcd_eq_iff] using hs
  exact h_dvd x.minFac (minFac_dvd x) (h_minFac ▸ minFac_dvd y)

-- If `nth p n < x` then `nth p (n + 1) ≤ x`.
-- Defined in analogy to `le_nth_of_lt_nth_succ`.
lemma nth_succ_le_of_nth_lt {p : ℕ → Prop} (hp : (setOf p).Infinite) {x : ℕ} (hpx : p x)
    (n : ℕ) (hn : nth p n < x) : nth p (n + 1) ≤ x := by
  obtain ⟨i, rfl⟩ : ∃ i, nth p i = x := exists_nth_of_infinite hp hpx
  rw [nth_lt_nth hp] at hn
  rw [nth_le_nth hp]
  exact hn

-- If `l` is sorted, all of its elements satisfy `p` and all of its elements are at least `nth p i`,
-- then it is elementwise bounded below by the `nth p` elements starting at `i`.
lemma forall₂_nth_range'_le_of_sorted_lt {p : ℕ → Prop} (hp : (setOf p).Infinite)
    {l : List ℕ} (hl_lt : l.Sorted (· < ·)) (hpl : ∀ a ∈ l, p a)
    (i : ℕ) (hil : ∀ a ∈ l, nth p i ≤ a) :
    List.Forall₂ (nth p · ≤ ·) (.range' i l.length) l := by
  induction hl_lt generalizing i with
  | nil => simp
  | @cons y l hyl hl_lt IH =>
    -- TODO: cleanup?
    change l.Sorted (· < ·) at hl_lt
    simp only [List.mem_cons, forall_eq_or_imp] at hpl
    rcases hpl with ⟨hpy, hpl⟩
    simp only [List.mem_cons, forall_eq_or_imp] at hil
    rcases hil with ⟨hiy, hil⟩
    simp only [List.length_cons, List.range'_succ, List.forall₂_cons]
    refine ⟨hiy, ?_⟩
    refine IH hpl (i + 1) ?_
    -- It remains to show that all elements of `l` are at least `nth p (i + 1)`.
    intro x hx
    refine nth_succ_le_of_nth_lt hp (hpl x hx) i ?_
    exact lt_of_le_of_lt hiy (hyl x hx)

-- If `x` satisfies `p`, then `nth p 0 ≤ x`.
lemma nth_zero_le {p : ℕ → Prop} (x : ℕ) (hx : p x) : nth p 0 ≤ x := by
  simpa [nth_zero] using Nat.sInf_le hx

-- If `l` is sorted and all of its elements satisfy `p`, then it is elementwise bounded below by
-- the first `l.length` elements that satisfy `p`.
lemma forall₂_nth_range_le_of_sorted_lt {p : ℕ → Prop} (hp : (setOf p).Infinite)
    {l : List ℕ} (hl_lt : l.Sorted (· < ·)) (hl : ∀ x ∈ l, p x) :
    List.Forall₂ (nth p · ≤ ·) (.range l.length) l := by
  rw [List.range_eq_range']
  exact forall₂_nth_range'_le_of_sorted_lt hp hl_lt hl 0 fun x hx ↦ nth_zero_le x (hl x hx)

theorem number_theory_245605 :
    {2, 3, 5, 7, 11, 13, 17, 19, 23} ∈ {s : Finset ℕ | Set.Pairwise s Coprime ∧ ∑ x ∈ s, x = 100} ∧
    IsMaxOn Finset.card {s : Finset ℕ | Set.Pairwise s Coprime ∧ ∑ x ∈ s, x = 100}
      {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
  constructor
  · rw [Set.mem_setOf_eq]
    constructor
    · -- To show coprime, it suffices to show that the numbers are prime (and distinct).
      suffices ∀ s : Set ℕ, (∀ x ∈ s, x.Prime) → Set.Pairwise s Coprime by
        refine this _ ?_
        simp only [Finset.mem_coe]
        simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
        norm_num
      intro s hs x hx y hy
      exact (coprime_primes (hs x hx) (hs y hy)).mpr
    · -- Evaluate the sum.
      rfl

  -- Show that the existence of such a set with more than 9 elements results in a contradiciton.
  suffices ∀ s : Finset ℕ, Set.Pairwise s Coprime → ∑ x ∈ s, x = 100 → ¬9 < #s by
    simpa [isMaxOn_iff]
  intro s hs_coprime hs_sum hs_card

  -- First, establish that the set cannot contain a zero.
  -- If it did, the only other element it could contain is 1.
  -- However, a subset of {0, 1} cannot have a sum of 100.
  have h_zero : 0 ∉ s := by
    contrapose! hs_sum with hs_zero
    refine _root_.ne_of_lt ?_
    calc _
    _ ≤ ∑ x ∈ {0, 1}, x :=
      Finset.sum_le_sum_of_subset (subset_of_coprime_of_zero_mem hs_coprime hs_zero)
    _ < 100 := by simp

  -- Every element of `s` must be either 1 or prime.
  -- Otherwise, we could take `s` and form a set `t` with sum ≤ 100 and cardinality ≥ 10.
  -- However, we observe that the sum of the first 10 such numbers (the first 9 primes plus 1)
  -- exceeds 100. This will provide our contradiction.
  -- Let `t` be the minimum factor of each number in `s`.
  let t := s.image minFac
  -- All elements of this set are either 1 or prime.
  have hpt : ∀ x ∈ t, x = 1 ∨ x.Prime := by
    unfold t
    simpa using fun x _ ↦ (eq_or_ne x 1).imp_right minFac_prime
  -- The set `t` has the same cardinality as `s`.
  have ht_card : #t = #s :=
    Finset.card_image_of_injOn (injOn_minFac_of_coprime hs_coprime)
  -- The elements of `t` have a sum which is less than or equal to that of `s.`
  have ht_sum : ∑ x ∈ t, x ≤ ∑ x ∈ s, x := by
    rw [Finset.sum_image (injOn_minFac_of_coprime hs_coprime)]
    refine Finset.sum_le_sum fun i hi ↦ minFac_le ?_
    suffices i ≠ 0 from zero_lt_of_ne_zero this
    exact ne_of_mem_of_not_mem hi h_zero

  -- For convenience when working with `nth`, establish that there are infinite such numbers.
  have hp : (setOf fun x ↦ x = 1 ∨ x.Prime).Infinite :=
    Set.infinite_union.mpr (.inr infinite_setOf_prime)

  suffices 101 ≤ ∑ x ∈ t, x by linarith
  calc 101
  -- First rewrite 101 as the sum of the first 10 numbers.
  _ = ∑ x ∈ {a ∈ Finset.range 29 | a = 1 ∨ a.Prime}, x := rfl
  _ = ∑ x ∈ (Finset.range 10).image (nth fun a ↦ a = 1 ∨ a.Prime), x := by
    congr
    rw [image_nth_range_of_infinite hp]
    suffices nth (fun x ↦ x = 1 ∨ Nat.Prime x) 10 = 29 by simp [this]
    exact nth_eq_of_count_eq rfl (by norm_num)
  _ = ∑ i ∈ Finset.range 10, nth (fun a ↦ a = 1 ∨ a.Prime) i :=
    Finset.sum_image fun x _ y _ h ↦ nth_injective hp h
  -- Since `9 < #s = #t`, it suffices to bound the first `#t` elements.
  _ ≤ ∑ i ∈ Finset.range #t, nth (fun a ↦ a = 1 ∨ a.Prime) i :=
    Finset.sum_le_sum_of_subset (by simpa [ht_card])
  -- Write as the sum of a sorted list in order to use pairwise inequality.
  _ = List.sum ((Finset.range #t).toList.map (nth fun x ↦ x = 1 ∨ Nat.Prime x)) :=
    (Finset.sum_to_list (Finset.range #t) (nth fun x ↦ x = 1 ∨ Nat.Prime x)).symm
  _ = List.sum ((List.range #t).map (nth fun x ↦ x = 1 ∨ Nat.Prime x)) := by
    rw [← Finset.sort_range]
    refine List.Perm.sum_eq (.map _ ?_)
    exact (Finset.sort_perm_toList _ _).symm
  -- The first `#t` elements that satisfy `p` must be less than `#t` distinct elements.
  _ ≤ List.sum (t.sort (· ≤ ·)) := by
    refine List.Forall₂.sum_le_sum ?_
    simpa using forall₂_nth_range_le_of_sorted_lt hp t.sort_sorted_lt (by simpa using hpt)
  -- Return to finset notation.
  _ = List.sum t.toList := (t.sort_perm_toList _).sum_eq
  _ = ∑ x ∈ t, x := by simpa using t.sum_to_list id
