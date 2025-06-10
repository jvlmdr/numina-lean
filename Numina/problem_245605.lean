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


lemma forall₂_dropLast_tail_of_sorted {l : List ℕ} (hl : l.Sorted (· ≤ ·)) :
    List.Forall₂ (· ≤ ·) l.dropLast l.tail := by
  induction hl with
  | nil => simp
  | @cons x l hx hl IH =>
    cases l with
    | nil => simp
    | cons a l =>
      rw [List.tail_cons, List.dropLast_cons₂, List.forall₂_cons]
      exact ⟨hx a (l.mem_cons_self a), by simpa using IH⟩

-- lemma exists_concat_of_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) :
--     ∃ (x : α) (l' : List α), l = l' ++ [x] := by
--   obtain ⟨x, l', h⟩ := List.exists_cons_of_ne_nil (List.reverse_ne_nil_iff.mpr hl)
--   exact ⟨x, l'.reverse, List.reverse_eq_cons_iff.mp h⟩

-- lemma nil_or_exists_concat {α : Type*} (l : List α) :
--     l = [] ∨ ∃ (x : α) (l' : List α), l = l' ++ [x] := by
--   cases l with
--   | nil => left; rfl
--   | cons x l => right; exact exists_concat_of_ne_nil (List.cons_ne_nil x l)

lemma dropLast_take_succ {α : Type*} {l : List α} {n : ℕ} (hn : n < l.length) :
    (l.take (n + 1)).dropLast = l.take n := by
  simpa [List.length_take_of_le hn, List.take_take] using (l.take (n + 1)).dropLast_eq_take

-- lemma tail_take_succ {α : Type*} (l : List α) (n : ℕ) :
--     (l.take (n + 1)).tail = l.tail.take n := by
--   cases l <;> simp

lemma forall₂_take_tail_of_sorted {l : List ℕ} (hl : l.Sorted (· ≤ ·)) {n : ℕ}
    (hn : n < l.length) :
    List.Forall₂ (· ≤ ·) (l.take n) (l.tail.take n) := by
  suffices List.Forall₂ (· ≤ ·) (l.take (n + 1)).dropLast (l.take (n + 1)).tail by
    convert this using 1
    · rw [dropLast_take_succ hn]
    · cases l <;> simp
  exact forall₂_dropLast_tail_of_sorted hl.take

-- For `s` a sublist of a larger sorted list `l`, its sum is at least that of the first elements.
lemma sum_take_length_le_of_sublist_of_sorted {l : List ℕ} (hl : l.Sorted (· ≤ ·)) {s : List ℕ}
    (hs : s <+ l) :
    (l.take s.length).sum ≤ s.sum := by
  induction hs with
  | slnil => simp
  | @cons₂ s l x hs IH =>
    -- The element `x` is in both `s` and `l`.
    -- Apply induction to the remaining elements.
    rw [List.sorted_cons] at hl
    simpa using IH hl.2
  | @cons s l x hs IH =>
    -- The element `x` is in `l` but not in `s`.
    calc _
    -- Use the fact that `x :: l` is elementwise less than or equal to `l`.
    _ ≤ (l.take s.length).sum := by
      refine List.Forall₂.sum_le_sum ?_
      refine forall₂_take_tail_of_sorted hl ?_
      simpa using Nat.lt_add_one_of_le hs.length_le
    -- Then apply induction.
    _ ≤ _ := by
      rw [List.sorted_cons] at hl
      exact IH hl.2

lemma sublist_filter_range_of_sorted {p : ℕ → Prop} [hp : DecidablePred p]
    {l : List ℕ} (hpl : ∀ x ∈ l, p x) (hl : l.Sorted (· ≤ ·)) (n : ℕ) (hn : ∀ x ∈ l, x < n) :
    l <+ List.filter p (List.range n) := by
  induction hl with
  | nil => simp
  | @cons x l hx hl IH =>
    simp at *
    specialize IH hpl.2 hn.2

    -- Split `range n` into elements `≤ x` and those after.
    have h_range : List.range (x + 1) ++ List.Ico (x + 1) n = List.range n := by
      simp [← List.Ico.zero_bot, List.Ico.append_consecutive _ hn.1]
    suffices [x] ++ l <+ List.filter p (List.range (x + 1) ++ List.Ico (x + 1) n) by
      simpa [h_range]
    rw [List.filter_append]
    refine List.Sublist.append ?_ ?_
    · simp only [List.singleton_sublist, List.mem_filter, List.mem_range]
      sorry
    · rw [← h_range, List.filter_append] at IH
      refine List.Sublist.of_sublist_append_right ?_ IH
      intro y hy
      suffices y < x + 1 → ¬p y by simpa
      suffices ¬y < x + 1 by simp [this]
      simp

      sorry


lemma sum_range_card_nth_le_sum' {p : ℕ → Prop} [DecidablePred p] (hp : (setOf p).Infinite)
    (s : Finset ℕ) (hs : ∀ x ∈ s, p x) :
    ∑ i ∈ Finset.range #s, nth p i ≤ ∑ x ∈ s, x := by
  cases s.eq_empty_or_nonempty with
  | inl hs => simp [hs]
  | inr hs =>
    calc _
    -- _ = (List.sum <| List.map (nth p) <| List.range #s) := by sorry
    _ = (List.sum <| List.take #s <| List.filter p <| List.range (s.max' hs)) := by
      sorry
    _ = (List.sum <| List.take (s.sort (· ≤ ·)).length <| List.filter p <| List.range (s.max' hs)) := by
      simp
    _ ≤ (s.sort (· ≤ ·)).sum := by
      refine sum_take_le_of_sorted ?_ ?_
      · sorry
      ·
        sorry
    _ ≤ ∑ x ∈ s, x := by sorry





lemma exists_nth_of_infinite {p : ℕ → Prop} (hp : (setOf p).Infinite) {n : ℕ} (hn : p n) :
    ∃ i, nth p i = n := by
  change n ∈ Set.range (nth p)
  rw [range_nth_of_infinite hp]
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

-- lemma forall₂_map_nth_le_of_sorted_lt {p : ℕ → Prop} [DecidablePred p] (hp : (setOf p).Infinite)
--     {x : ℕ} {l : List ℕ} (hpx : p x) (hpl : ∀ a ∈ l, p a)
--     (hxl : ∀ a ∈ l, x < a) (hl_lt : l.Sorted (· < ·)) {i : ℕ} (hi : nth p i = x) :
--     List.Forall₂ (· ≤ ·) (.map (nth p) (.range' i l.length)) l := by

--   sorry


-- Given a list of ordered natural numbers that satisfy `p` and an index `i` such that
-- all elements of the list are at least `nth p i`, we can guarantee

lemma nth_succ_le_of_nth_lt {p : ℕ → Prop} (hp : (setOf p).Infinite) {x : ℕ} (hpx : p x)
    (n : ℕ) (hn : nth p n < x) :
    nth p (n + 1) ≤ x := by
  obtain ⟨i, rfl⟩ : ∃ i, nth p i = x := exists_nth_of_infinite hp hpx
  rw [nth_lt_nth hp] at hn
  rw [nth_le_nth hp]
  exact hn

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

lemma nth_zero_le {p : ℕ → Prop} (x : ℕ) (hx : p x) : nth p 0 ≤ x := by
  simpa [nth_zero] using Nat.sInf_le hx

lemma forall₂_nth_range_le_of_sorted_lt {p : ℕ → Prop} (hp : (setOf p).Infinite)
    {l : List ℕ} (hl_lt : l.Sorted (· < ·)) (hl : ∀ x ∈ l, p x) :
    List.Forall₂ (nth p · ≤ ·) (.range l.length) l := by
  rw [List.range_eq_range']
  exact forall₂_nth_range'_le_of_sorted_lt hp hl_lt hl 0 fun x hx ↦ nth_zero_le x (hl x hx)


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

  have hpt : ∀ x ∈ t, x = 1 ∨ x.Prime := by
    unfold t
    simpa using fun x _ ↦ (eq_or_ne x 1).imp_right minFac_prime


  suffices 101 ≤ ∑ x ∈ s, x by linarith

  calc 101
  _ = ∑ x ∈ {a ∈ Finset.range 29 | a = 1 ∨ a.Prime}, x := rfl

  -- TODO: How much do we still require for `image_nth_range_of_infinite`?
  _ = ∑ x ∈ (Finset.range 10).image (nth fun a ↦ a = 1 ∨ a.Prime), x := by
    congr
    rw [image_nth_range_of_infinite h_inf]
    suffices nth (fun x ↦ x = 1 ∨ Nat.Prime x) 10 = 29 by simp [this]
    exact nth_eq_of_count_eq rfl (by norm_num)

  _ = ∑ i ∈ Finset.range 10, nth (fun a ↦ a = 1 ∨ a.Prime) i :=
    Finset.sum_image fun x _ y _ h ↦ nth_injective h_inf h

  _ ≤ ∑ i ∈ Finset.range #t, nth (fun a ↦ a = 1 ∨ a.Prime) i :=
    Finset.sum_le_sum_of_subset (by simpa [ht_card])

  -- Write as the sum of a sorted list to use monotonicity.
  _ = List.sum ((Finset.range #t).toList.map (nth fun x ↦ x = 1 ∨ Nat.Prime x)) :=
    (Finset.sum_to_list (Finset.range #t) (nth fun x ↦ x = 1 ∨ Nat.Prime x)).symm

  _ = List.sum ((List.range #t).map (nth fun x ↦ x = 1 ∨ Nat.Prime x)) := by
    rw [← Finset.sort_range]
    refine List.Perm.sum_eq (.map _ ?_)
    exact (Finset.sort_perm_toList _ _).symm

  _ ≤ List.sum (t.sort (· ≤ ·)) := by
    refine List.Forall₂.sum_le_sum ?_
    simpa using forall₂_nth_range_le_of_sorted_lt h_inf t.sort_sorted_lt (by simpa using hpt)
  _ = List.sum t.toList := (t.sort_perm_toList _).sum_eq
  _ = ∑ x ∈ t, x := by simpa using t.sum_to_list id
  _ ≤ ∑ x ∈ s, x := ht_sum  -- TODO: move here?
