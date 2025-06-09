-- https://cloud.kili-technology.com/label/projects/review/cmbj2mmny000nv7ayeaimuiqo

import Mathlib

open Nat
open scoped Finset

/- Represent the number 100 as the sum of the maximum possible number of pairwise coprime natural
numbers. Explanation: the condition means that the greatest common divisor of any two numbers used
in the sum is 1. -/

lemma filter_prime_range_29 :
    {p ∈ Finset.range 29 | p.Prime} = {2, 3, 5, 7, 11, 13, 17, 19, 23} := rfl

lemma sum_filter_one_or_prime_range_29 :
    ∑ x ∈ {p ∈ Finset.range 29 | p = 1 ∨ p.Prime}, x = 101 := rfl

lemma nth_eq_of_count_eq {p : ℕ → Prop} [DecidablePred p]
    {n x : ℕ} (h_count : count p x = n) (hpx : p x) : nth p n = x :=
  h_count ▸ nth_count hpx

-- TODO: do we need these?

lemma nth_prime_eight : nth Nat.Prime 8 = 23 := by
  refine nth_eq_of_count_eq ?_ (by norm_num)
  exact count_eq_card_filter_range _ _

lemma nth_prime_nine : nth Nat.Prime 9 = 29 := by
  refine nth_eq_of_count_eq ?_ (by norm_num)
  exact count_eq_card_filter_range _ _

lemma nth_one_or_prime_nine : nth (fun x ↦ x = 1 ∨ x.Prime) 9 = 23 := by
  refine nth_eq_of_count_eq ?_ (by norm_num)
  exact count_eq_card_filter_range _ _

lemma nth_one_or_prime_ten : nth (fun x ↦ x = 1 ∨ x.Prime) 10 = 29 := by
  refine nth_eq_of_count_eq ?_ (by norm_num)
  exact count_eq_card_filter_range _ _


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


-- lemma map_nth_range {p : ℕ → Prop} [DecidablePred p] (hp : (setOf p).Infinite) (n : ℕ) :
--     List.map (nth p) (List.range n) = List.filter p (List.range (nth p n)) := by
--   sorry

-- lemma nth_eq_iff_count_eq {p : ℕ → Prop} [DecidablePred p]
--     (hp : ∀ (hf : (setOf p).Finite), n < #hf.toFinset))
--     (n x : ℕ) (hpx : p x) :
--     nth p n = x ↔ count p x = n := by
--   constructor
--   · intro h
--     rw [← h]
--     sorry
--   sorry

-- lemma set_image_nth_Ico_of_infinite {p : ℕ → Prop} (hp : (setOf p).Infinite)
--     (n : ℕ) :
--     nth p '' Set.Iio n = {x ∈ Set.Iio (nth p n) | p x} := by
--   ext x
--   simp only [Set.mem_image, Set.mem_Iio, Set.mem_setOf_eq]
--   constructor
--   · rintro ⟨y, hyn, rfl⟩
--     refine ⟨?_, ?_⟩
--     · exact (nth_lt_nth hp).mpr hyn
--     · refine nth_mem _ ?_
--       intro hp'
--       exfalso
--       exact hp hp'
--   · intro ⟨hx, hpx⟩
--     obtain ⟨i, rfl⟩ : ∃ i, nth p i = x := exists_nth_of_infinite hp hpx
--     refine ⟨i, ?_, rfl⟩
--     exact (nth_lt_nth hp).mp hx

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


-- TODO: remove?
lemma list_range_one : List.range 1 = [0] := rfl

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

-- A sum of prime powers is bounded below by the sum of primes.
lemma sum_primes_le_sum_prime_pows {s : Finset ℕ} (h_mem : ∀ x ∈ s, IsPrimePow x) :
    ∑ x ∈ s, x.minFac ≤ ∑ x ∈ s, x :=
  Finset.sum_le_sum fun x hx ↦ minFac_le (h_mem x hx).pos

-- TODO: still need to encode the fact that the prime powers are coprime to each other?
-- Maybe easiest to use `Nat.factorization` of the product? Otherwise need (p, k) pairs?


lemma setOf_one_or_prime_infinite : (setOf fun x ↦ x = 1 ∨ x.Prime).Infinite :=
  Set.infinite_union.mpr (.inr infinite_setOf_prime)

-- The sum of 10 or more numbers that are either 1 or prime is at greater than 100.
lemma sum_of_prime_or_one {s : Finset ℕ} (h_card : 10 ≤ #s)
    (h_mem : ∀ x ∈ s, x = 1 ∨ x.Prime) :
    100 < ∑ x ∈ s, x := by
  calc _
  _ < 101 := by norm_num
  -- Write as the sum up to (not including) the prime after 23.
  _ = ∑ x ∈ {p ∈ Finset.range 29 | p = 1 ∨ p.Prime}, x := rfl
  _ = ∑ x ∈ (Finset.range 10).image (nth fun a ↦ a = 1 ∨ a.Prime), x := by
    congr
    rw [image_nth_range_of_infinite setOf_one_or_prime_infinite]
    suffices nth (fun x ↦ x = 1 ∨ x.Prime) 10 = 29 by simp [this]
    exact nth_eq_of_count_eq rfl (by norm_num)
  _ = ∑ i ∈ Finset.range 10, nth (fun a ↦ a = 1 ∨ a.Prime) i :=
    Finset.sum_image fun x _ y _ h ↦ nth_injective setOf_one_or_prime_infinite h
  _ ≤ ∑ i ∈ Finset.range #s, nth (fun a ↦ a = 1 ∨ a.Prime) i :=
    Finset.sum_le_sum_of_subset <| by simpa using h_card
  _ ≤ _ := sum_range_card_nth_le_sum setOf_one_or_prime_infinite s h_mem


lemma subset_of_coprime_of_zero_mem {s : Finset ℕ} (hs : Set.Pairwise s Coprime)
    (h : 0 ∈ s) : s ⊆ {0, 1} := by
  intro y hy
  specialize @hs y hy 0 h
  contrapose! hs
  simpa using hs

-- Inductive application of `add_le_mul` to sum and product.
lemma sum_le_prod {s : Finset ℕ} {f : ℕ → ℕ} (hf : ∀ x ∈ s, 2 ≤ f x) :
    ∑ x ∈ s, f x ≤ ∏ x ∈ s, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx IH =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at hf
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    -- Eliminate the case where `s` is empty.
    -- When `s` is not empty, we can bound the product below by 2.
    cases s.eq_empty_or_nonempty with
    | inl hs => simp [hs]
    | inr hs =>
      have h_prod : 2 ≤ ∏ x ∈ s, f x := by
        calc _
        _ ≤ 2 ^ #s := Nat.le_self_pow (Finset.card_ne_zero.mpr hs) 2
        _ = ∏ x ∈ s, 2 := by simp
        _ ≤ ∏ x ∈ s, f x := Finset.prod_le_prod' hf.2
      calc _
      _ ≤ f x + ∏ x ∈ s, f x := by simpa using IH hf.2
      _ ≤ _ := add_le_mul hf.1 h_prod

-- If two numbers are coprime, they cannot be equal unless both are 1.
lemma eq_iff_of_coprime {a b : ℕ} (h : a.Coprime b) : a = b ↔ a = 1 ∧ b = 1 := by
  constructor
  · rintro rfl
    simpa using h
  · rintro ⟨rfl, rfl⟩
    simp

lemma ne_iff_of_coprime {a b : ℕ} (h : a.Coprime b) : a ≠ b ↔ a ≠ 1 ∨ b ≠ 1 := by
  simp only [ne_eq, eq_iff_of_coprime h]
  exact Decidable.not_and_iff_or_not

-- If two numbers are coprime, they cannot be equal unless both are 1.
lemma ne_of_coprime {a b : ℕ} (h_one : a ≠ 1 ∨ b ≠ 1) (h : a.Coprime b) : a ≠ b :=
  (ne_iff_of_coprime h).mpr h_one


-- If some element `n ∈ s` has multiple prime factors, it can be split to obtain a set with more
-- elements and lesser or equal sum.
lemma exists_lt_card_and_sum_le (s : Finset ℕ) (h_coprime : Set.Pairwise s Coprime)
    (h_zero : 0 ∉ s) {n : ℕ} (hns : n ∈ s) (hn : 1 < n.primeFactors.card) :
    ∃ t : Finset ℕ, Set.Pairwise t Coprime ∧ #s < t.card ∧ ∑ x ∈ t, x ≤ ∑ x ∈ s, x := by
  use s.erase n ∪ n.primeFactors.image (fun p ↦ p ^ n.factorization p)

  -- TODO: extract as lemma?
  have h_disj : Disjoint (s.erase n) (n.primeFactors.image fun p ↦ p ^ n.factorization p) := by
    -- Since `x` is coprime to all other elements, so are its factors.
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [Finset.mem_erase] at ha
    simp only [Finset.mem_image] at hb
    specialize @h_coprime a ha.2 n hns ha.1

    -- have hn_gt : 1 < x := by simpa using Nat.zero_lt_of_lt hn
    -- Rewrite `b` as a power of prime `p`.
    rcases hb with ⟨p, hp, hb⟩
    have hb_pow : IsPrimePow b := by
      refine ⟨p, n.factorization p, ?_, ?_, hb⟩
      · rw [← Nat.prime_iff]
        exact prime_of_mem_primeFactors hp
      · refine Nat.pos_of_ne_zero ?_
        exact Finsupp.mem_support_iff.mp hp

    refine ne_of_coprime (.inr hb_pow.ne_one) ?_
    suffices b ∣ n from h_coprime.coprime_dvd_right this
    convert Nat.dvd_mul_right b (∏ q ∈ n.primeFactors.erase p, q ^ n.factorization q)
    rw [← hb]
    symm
    calc _
    _ = ∏ q ∈ n.primeFactors, q ^ n.factorization q :=
      Finset.mul_prod_erase n.primeFactors (fun q ↦ q ^ n.factorization q) hp
    _ = _ := by
      refine Nat.factorization_prod_pow_eq_self ?_
      exact ne_of_mem_of_not_mem hns h_zero

  -- TODO: extract as lemma?
  have h_injOn : Set.InjOn (fun p ↦ p ^ n.factorization p) n.primeFactors := by
    intro p hp q hq h
    -- If (non-zero) powers of two primes are equal, then the primes must be equal.
    suffices p.primeFactors = q.primeFactors by
      simpa [prime_of_mem_primeFactors hp, prime_of_mem_primeFactors hq]
    convert congrArg primeFactors h using 1
    · exact (Nat.primeFactors_pow _ (Finsupp.mem_support_iff.mp hp)).symm
    · exact (Nat.primeFactors_pow _ (Finsupp.mem_support_iff.mp hq)).symm

  refine ⟨?_, ?_, ?_⟩
  · -- TODO!
    sorry
  · calc _
    _ = (s.erase n).card + 1 := (Finset.card_erase_add_one hns).symm
    _ < (s.erase n).card + n.primeFactors.card := by simpa
    _ = _ := by simpa [h_disj] using (Finset.card_image_of_injOn h_injOn).symm

  · -- Extract and cancel the sum of the other terms from both sides.
    rw [Finset.sum_union h_disj, ← s.sum_erase_add _ hns]
    rw [add_le_add_iff_left]
    calc _
    _ = ∑ x ∈ n.primeFactors, x ^ n.factorization x := Finset.sum_image h_injOn
    _ ≤ ∏ p ∈ n.primeFactors, p ^ (n.factorization p) := by
      refine sum_le_prod fun p hp ↦ ?_
      calc _
      _ ≤ p := (prime_of_mem_primeFactors hp).two_le
      _ ≤ _ := Nat.le_self_pow (Finsupp.mem_support_iff.mp hp) p
    _ = _ := factorization_prod_pow_eq_self (ne_of_mem_of_not_mem hns h_zero)


theorem number_theory_245605 :
    IsMaxOn Finset.card {s | Set.Pairwise s Coprime ∧ ∑ x ∈ s, x = 100}
      {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
  -- Replace the numbers with the first nine primes; the primes up to 23.
  -- rw [← filter_prime_range_29]
  -- rw [← nth_prime_nine]

  suffices ∀ (s : Finset ℕ), Set.Pairwise s Coprime → ¬(∑ x ∈ s, x = 100 ∧ 9 < #s) by
    simpa [isMaxOn_iff]
  intro s hs_coprime ⟨hs_sum, hs_card⟩
  -- rw [and_comm]

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

  have h_sum_nth_one_or_prime :
      ∑ i ∈ Finset.range 10, nth (fun x ↦ x = 1 ∨ x.Prime) i = 101 := by
    sorry

  have h_injOn {s : Finset ℕ} (hs : Set.Pairwise s Coprime) : Set.InjOn minFac s := by
    -- rw [Set.injOn_iff_pairwise_ne]
    -- refine hs_coprime.imp fun x y h ↦ ?_
    intro x hx y hy h_minFac
    -- TODO: extract as lemma? `minFac_injOn_of_pairwise_coprime`?
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

  have : ∀ x ∈ s, x = 1 ∨ x.Prime := by
    let t := s.image minFac
    have ht_card : #t = #s := Finset.card_image_of_injOn (h_injOn hs_coprime)
    have ht_sum : ∑ x ∈ t, x ≤ ∑ x ∈ s, x := by
      rw [Finset.sum_image (h_injOn hs_coprime)]
      refine Finset.sum_le_sum fun i hi ↦ ?_
      refine minFac_le ?_
      suffices i ≠ 0 from zero_lt_of_ne_zero this
      exact ne_of_mem_of_not_mem hi h_zero

    sorry


  suffices ∀ x ∈ s, x = 1 ∨ x.Prime by

    sorry





  -- That is, it results in a contradiction? Contradiction of what?



  -- The elements of the set must have at most one prime factor.
  -- If one element had two distinct prime factors, it could be split to obtain a set with more
  -- elements and lesser or equal sum.

  have : ∀ x ∈ s, #x.primeFactors ≤ 1 := by
    suffices ¬∃ x ∈ s, #x.primeFactors > 1 by simpa
    intro ⟨n, hns, hn⟩
    -- TODO: suffices ∀ t?
    have := exists_lt_card_and_sum_le s hs_coprime h_zero hns hn
    rcases this with ⟨t, ht_coprime, ht_card, ht_sum⟩
    refine ht_sum.not_lt ?_
    sorry

  -- Any set of ten coprime numbers must have sum greater than 100.

  -- Any set of more than 9 numbers that are either 1 or a prime power has sum greater than 100.
  have (h_card : 9 < #s) (h_mem : ∀ x ∈ s, x = 1 ∨ IsPrimePow x) : 100 < ∑ x ∈ s, x := by
    cases em (1 ∈ s) with
    | inl h_one =>
      sorry
    | inr h_one =>
      sorry

  sorry
