-- https://cloud.kili-technology.com/label/projects/review/cmbj2mmny000nv7ayeaimuiqo

import Mathlib

open Nat
open scoped Finset

/- Represent the number 100 as the sum of the maximum possible number of pairwise coprime natural
numbers. Explanation: the condition means that the greatest common divisor of any two numbers used
in the sum is 1. -/

lemma nth_eq_of_count_eq {p : ℕ → Prop} [DecidablePred p]
    {n x : ℕ} (h_count : count p x = n) (hpx : p x) : nth p n = x :=
  h_count ▸ nth_count hpx

-- How to show that the product of a set of `n` distinct prime numbers is at least the product of
-- the first `n` primes?

lemma exists_nth_of_infinite {p : ℕ → Prop} (hp : (setOf p).Infinite) {n : ℕ} (hn : p n) :
    ∃ i, nth p i = n := by
  rw [← Set.mem_range, range_nth_of_infinite hp]
  exact hn

lemma exists_map_nth_eq {p : ℕ → Prop} (hp : (setOf p).Infinite) (l : List ℕ) (hs : ∀ x ∈ l, p x) :
    ∃ t : List ℕ, t.map (nth p) = l := by
  induction l with
  | nil => simp
  | cons x l IH =>
    simp only [List.mem_cons, forall_eq_or_imp] at hs
    obtain ⟨t', ht'⟩ := IH hs.2
    obtain ⟨x', hx'⟩ := exists_nth_of_infinite hp hs.1
    use x' :: t'
    simpa using ⟨hx', ht'⟩

-- Imported from more recent version of Mathlib.
lemma Finset.prod_map_toList {α β : Type*} [CommMonoid β] (s : Finset α) (f : α → β) :
    (s.toList.map f).prod = s.prod f := by
  rw [Finset.prod, ← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]

-- Imported from more recent version of Mathlib.
lemma Finset.prod_toList {α : Type*} [CommMonoid α] (s : Finset α) :
    s.toList.prod = ∏ x ∈ s, x := by
  simpa using s.prod_map_toList id

-- The product of a set of elements can be rewritten as a product of `nth` elements.
lemma exists_image_nth_eq {p : ℕ → Prop} (hp : (setOf p).Infinite) (s : Finset ℕ)
    (hs : ∀ x ∈ s, p x) :
    ∃ t : Finset ℕ, #t = #s ∧ t.image (nth p) = s := by
  obtain ⟨l, hl⟩ := exists_map_nth_eq hp s.toList (by simpa)
  use l.toFinset
  refine ⟨?_, ?_⟩
  · suffices l.Nodup by
      calc _
      _ = (l.map (nth p)).length := by simpa using List.toFinset_card_of_nodup this
      _ = _ := by simp [hl]
    suffices (l.map (nth p)).Nodup from this.of_map (nth p)
    simpa [hl] using s.nodup_toList
  · -- TODO: Better to prove for Multiset above rather than List?
    calc _
    _ = Finset.image (nth p) (Multiset.toFinset l) := by simp
    _ = (Multiset.map (nth p) l).toFinset := Finset.image_toFinset
    _ = _ := by simp [hl]

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

-- TODO: Is there not an easier way to implement this?!

lemma forall₂_range'_le_sorted_lt (a : ℕ) (l : List ℕ) (ha : ∀ x ∈ l, a ≤ x)
    (hl : l.Sorted (· < ·)) :
    List.Forall₂ (· ≤ ·) (List.range' a l.length) l := by
  induction hl generalizing a with
  | nil => simp
  | @cons x l hx hl IH =>
    simp only [List.length_cons, List.range'_succ, List.forall₂_cons]
    -- obtain ⟨hax, hal⟩ : a < x ∧ ∀ b ∈ l, a < b := by simpa using ha
    simp at ha
    rcases ha with ⟨hax, hal⟩
    refine ⟨hax, ?_⟩
    refine IH (a + 1) fun b hb ↦ ?_
    -- Obtain `a + 1 < b` from `a < x < b`.
    exact lt_of_le_of_lt hax (hx b hb)

-- TODO: seems like this could be done with `List.Sublist`? except the list would be infinite?

-- Any list of strictly increasing natural numbers is pairwise at least as large as the list
-- of consecutive natural numbers.
lemma forall₂_range_le_sorted_lt (l : List ℕ) (hl : l.Sorted (· < ·)) :
    List.Forall₂ (· ≤ ·) (List.range l.length) l := by
  cases l with
  | nil => simp
  | cons x l =>
    have ⟨hx, hl⟩ : (∀ b ∈ l, x < b) ∧ l.Sorted (· < ·) := by simpa using hl
    simpa [List.range_eq_range', List.range'_succ] using
      forall₂_range'_le_sorted_lt 1 l (fun b hb ↦ one_le_of_lt (hx b hb)) hl

-- The sum of a finite set of elements satisfying `p` is bounded below by the first `#s` elements.
lemma sum_range_card_nth_le_sum {p : ℕ → Prop} (hp : (setOf p).Infinite)
    (s : Finset ℕ) (hs : ∀ x ∈ s, p x) :
    ∑ i ∈ Finset.range #s, nth p i ≤ ∑ x ∈ s, x := by
  obtain ⟨t, h_card, ht⟩ : ∃ t : Finset ℕ, #t = #s ∧ t.image (nth p) = s :=
    exists_image_nth_eq hp s hs
  calc _
  _ = List.sum ((List.range #s).map (nth p)) := rfl
  _ ≤ List.sum ((t.sort (· ≤ ·)).map (nth p)) := by
    refine List.Forall₂.sum_le_sum ?_
    suffices List.Forall₂ (· ≤ ·) (List.range #s) (t.sort (· ≤ ·)) by
      simpa using this.imp fun a b h ↦ nth_monotone hp h
    simpa [h_card] using forall₂_range_le_sorted_lt _ t.sort_sorted_lt
  _ = (t.toList.map (nth p)).sum := by
    refine List.Perm.sum_eq ?_
    refine List.Perm.map (nth p) ?_
    exact t.sort_perm_toList _
  _ = ∑ i ∈ t, nth p i := t.sum_to_list (nth p)
  _ = ∑ x ∈ s, x := by
    rw [← ht]
    symm
    exact Finset.sum_image fun x hx y hy h ↦ nth_injective hp h


-- TODO: comment
lemma subset_of_coprime_of_zero_mem {s : Finset ℕ} (hs : Set.Pairwise s Coprime)
    (h : 0 ∈ s) : s ⊆ {0, 1} := by
  intro y hy
  specialize @hs y hy 0 h
  contrapose! hs
  simpa using hs

-- TODO: comment
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

theorem number_theory_245605 :
    IsMaxOn Finset.card {s | Set.Pairwise s Coprime ∧ ∑ x ∈ s, x = 100}
      {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
  -- TODO: use `10 ≤` here?
  suffices ∀ (s : Finset ℕ), Set.Pairwise s Coprime → ∑ x ∈ s, x = 100 → ¬9 < #s by
    simpa [isMaxOn_iff]
  intro s hs_coprime hs_sum hs_card

  -- The set cannot contain a zero.
  -- If so, the only other element it could contain is 1, since `Nat.gcd 0 x = x`.
  -- However, a subset of {0, 1} cannot have a sum of 100.
  have h_zero : 0 ∉ s := by
    contrapose! hs_sum with hs_zero
    refine _root_.ne_of_lt ?_
    calc _
    _ ≤ ∑ x ∈ {0, 1}, x :=
      Finset.sum_le_sum_of_subset (subset_of_coprime_of_zero_mem hs_coprime hs_zero)
    _ < 100 := by simp

  change 10 ≤ #s at hs_card

  -- We know that every element of `s` is either 1 or prime.
  -- Otherwise, we could take `s` and form such a set `t` with sum ≤ 100 and cardinality ≥ 10.
  -- This contradicts the observation that the sum of the first 10 such numbers exceeds 100.

  -- Construct a set containing only 1 or prime.
  let t := s.image minFac

  have ht_card : #t = #s :=
    Finset.card_image_of_injOn (injOn_minFac_of_coprime hs_coprime)
  have ht_sum : ∑ x ∈ t, x ≤ ∑ x ∈ s, x := by
    rw [Finset.sum_image (injOn_minFac_of_coprime hs_coprime)]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    refine minFac_le ?_
    suffices i ≠ 0 from zero_lt_of_ne_zero this
    exact ne_of_mem_of_not_mem hi h_zero

  have h_inf : (setOf fun x ↦ x = 1 ∨ x.Prime).Infinite :=
    Set.infinite_union.mpr (.inr infinite_setOf_prime)

  suffices 101 ≤ ∑ x ∈ s, x by linarith

  calc 101
  -- TODO: do we really need to use 29, 10, etc here?
  _ = ∑ x ∈ {a ∈ Finset.range 29 | a = 1 ∨ a.Prime}, x := rfl
  _ = ∑ x ∈ (Finset.range 10).image (nth fun a ↦ a = 1 ∨ a.Prime), x := by
    congr
    rw [image_nth_range_of_infinite h_inf]
    suffices nth (fun x ↦ x = 1 ∨ Nat.Prime x) 10 = 29 by simp [this]
    exact nth_eq_of_count_eq rfl (by norm_num)
  _ = ∑ i ∈ Finset.range 10, nth (fun a ↦ a = 1 ∨ a.Prime) i :=
    Finset.sum_image fun x _ y _ h ↦ nth_injective h_inf h
  _ ≤ ∑ i ∈ Finset.range #t, nth (fun a ↦ a = 1 ∨ a.Prime) i := by
    refine Finset.sum_le_sum_of_subset ?_
    -- TODO: move `ht_card` here?
    simpa [ht_card] using hs_card
  _ ≤ ∑ x ∈ t, x := by
    refine sum_range_card_nth_le_sum h_inf _ ?_
    unfold t
    simpa using fun x hx ↦ Or.imp_right minFac_prime (eq_or_ne x 1)
  _ ≤ ∑ x ∈ s, x := ht_sum  -- TODO: move here?
