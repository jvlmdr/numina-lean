-- https://cloud.kili-technology.com/label/projects/review/cma3ygf29006tahayw92dzene

import Mathlib

open Finset Nat

/- For any positive integer $n  >1$, let $P(n)$ denote the largest prime not exceeding $n$.
Let $N(n)$ denote the next prime larger than $P(n)$. (For example $P(10) = 7$ and $N(10) = 11$,
while $P(11) = 11$ and $N(11) = 13$.) If $n+1$ is a prime number, prove that the value of the sum
$$
\frac{1}{P(2) N(2)} + \frac{1}{P(3) N(3)} + \frac{1}{P(4) N(4)} + \cdots + \frac{1}{P(n) N(n)} =
\frac{n - 1}{2 n + 2}
$$
-/

lemma Ioc_sub_one_sub_one_eq_Ico (a b : ℕ) (ha : a ≠ 0) :
    Set.Ioc (a - 1) (b - 1) = Set.Ico a b := by
  by_cases hab : a < b
  · ext x
    simp only [Set.mem_Ioc, Set.mem_Ico]
    refine and_congr ?_ ?_
    · refine Order.sub_one_lt_iff_of_not_isMin ?_
      exact not_isMin_iff_ne_bot.mpr ha
    · refine Nat.le_sub_one_iff_lt ?_
      exact zero_lt_of_lt hab
  · rw [Set.Ico_eq_empty hab, Set.Ioc_eq_empty]
    simp only [not_lt] at hab ⊢
    exact Nat.sub_le_sub_right hab 1

lemma Ico_eq_union (k : ℕ) :
    Ico 2 (nth Nat.Prime k) =
      (range k).biUnion fun i ↦ Ico (nth Nat.Prime i) (nth Nat.Prime (i + 1)) := by
  -- Coerce from `Finset` to `Set` to use `Monotone.biUnion_Ico_Ioc_map_succ`.
  refine Finset.coe_injective ?_
  simp only [coe_Ico, coe_biUnion, coe_range]
  symm
  -- Unfortunately, this lemma only exists for `Ioc`.
  -- Therefore we must subtract one to obtain `Ico`.
  convert Monotone.biUnion_Ico_Ioc_map_succ (f := (nth Nat.Prime · - 1)) ?_ 0 k using 1
  · have (a b) := Ioc_sub_one_sub_one_eq_Ico (nth Nat.Prime a) (nth Nat.Prime b)
      (prime_nth_prime a).ne_zero
    simp [this]
  · rw [Ioc_sub_one_sub_one_eq_Ico _ _ (by simp)]
    simp
  · intro a b h
    refine Nat.sub_le_sub_right ?_ 1
    exact nth_monotone infinite_setOf_prime h

-- lemma sum_Ico_eq_sum_sum (k : ℕ) (g : ℕ → ℚ) :
--     ∑ i in Ico 2 (nth Nat.Prime k), g i =
--       (∑ i in range k, ∑ j in Ico (nth Nat.Prime i) (nth Nat.Prime (i + 1)), g j) := by
--   rw [Ico_eq_union k]
--   simp only [Finset.biUnion, Finset.coe_union, Finset.coe_Ico, Finset.coe_range,
--     Finset.sum_biUnion]
--   rfl

lemma csSup_le_eq_of_mem_Ico_nth {p : ℕ → Prop}
    {n k : ℕ} (hn : n ∈ Ico (nth p k) (nth p (k + 1)))
    (hp : ∀ (hf : (setOf p).Finite), k < #hf.toFinset) :
    sSup {x | p x ∧ x ≤ n} = nth p k := by
  simp only [mem_Ico] at hn
  refine csSup_eq_of_is_forall_le_of_forall_le_imp_ge ?_ ?_ ?_
  · suffices nth p k ∈ {x | p x ∧ x ≤ n} from Set.nonempty_of_mem this
    simpa [Set.mem_setOf_eq] using ⟨nth_mem k hp, hn.1⟩
  · -- All elements in the set are less than or equal to `nth p k`.
    simp only [Set.mem_setOf_eq, and_imp]
    intro a ha han
    refine le_nth_of_lt_nth_succ ?_ ha
    exact lt_of_le_of_lt han hn.2
  · -- Any upper bound in the set is greater than or equal to `nth p k`.
    -- TODO: I do not understand this.
    simp only [Set.mem_setOf_eq, and_imp]
    intro b hb
    exact hb (nth p k) (nth_mem k hp) hn.1

-- Combine `lt_of_nth_lt_nth_of_lt_card` and `nth_strictMono` to handle finite and infinite cases.
lemma lt_of_nth_lt_nth {p : ℕ → Prop} {m n : ℕ} (hp : ∀ (hf : (setOf p).Finite), m < #hf.toFinset)
    (hlt : nth p m < nth p n) :
    m < n := by
  refine (setOf p).finite_or_infinite.elim ?_ ?_
  · exact fun hf ↦ lt_of_nth_lt_nth_of_lt_card hf hlt (hp hf)
  · exact fun hf ↦ (nth_strictMono hf).lt_iff_lt.mp hlt

-- Defined in analogy to `le_nth_of_lt_nth_succ`.
lemma nth_succ_le_of_nth_lt {p : ℕ → Prop} {k a : ℕ}
    (hp : ∀ (hf : (setOf p).Finite), k < #hf.toFinset)
    (h : nth p k < a) (ha : p a) :
    nth p (k + 1) ≤ a := by
  obtain ⟨i, hi, rfl⟩ := exists_lt_card_nth_eq ha
  suffices k < i from nth_le_nth' this hi
  exact lt_of_nth_lt_nth hp h

lemma csInf_lt_eq_of_mem_Ico_nth (p : ℕ → Prop)
    {n k : ℕ} (hn : n ∈ Ico (nth p k) (nth p (k + 1)))
    (hp : ∀ (hf : (setOf p).Finite), k + 1 < #hf.toFinset) :
    sInf {x | p x ∧ n < x} = nth p (k + 1) := by
  simp only [mem_Ico] at hn
  refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt ?_ ?_ ?_
  · suffices nth p (k + 1) ∈ {x | p x ∧ n < x} from Set.nonempty_of_mem this
    simpa [Set.mem_setOf_eq] using ⟨nth_mem (k + 1) hp, hn.2⟩
  · simp only [Set.mem_setOf_eq, and_imp]
    intro a ha hna
    refine nth_succ_le_of_nth_lt (fun hf ↦ k.lt_add_one.trans (hp hf)) ?_ ha
    exact lt_of_le_of_lt hn.1 hna
  · simp only [Set.mem_setOf_eq]
    intro b hb
    exact ⟨_, ⟨nth_mem (k + 1) hp, hn.2⟩, hb⟩

theorem number_theory_122216 {P N : ℕ → ℕ}
    (hP : ∀ n, P n = sSup {p | p.Prime ∧ p ≤ n})
    (hN : ∀ n, N n = sInf {p | p.Prime ∧ n < p})
    (n : ℕ) (hn : 1 < n) (h_prime : (n + 1).Prime) :
    ∑ i ∈ Finset.Icc 2 n, 1 / (P i * N i : ℚ) = (n - 1) / (2 * n + 2) := by

  -- Rewrite in terms of `n + 1`.
  revert n
  suffices ∀ n > 2, n.Prime → ∑ i ∈ Finset.Ico 2 n, (1 / (P i * N i) : ℚ) = (n - 2) / (2 * n) by
    intro n hn h_prime
    convert this _ (add_lt_add_right hn 1) h_prime using 1
    · simp only [cast_add]
      ring
  intro n hn hn_prime

  -- Obtain `i` such that `nth Nat.Prime i = n`.
  have h_not_fin : ¬(setOf Nat.Prime).Finite := infinite_setOf_prime
  obtain ⟨i, hi⟩ : ∃ i, nth Nat.Prime i = n := by
    simpa [h_not_fin] using exists_lt_card_nth_eq hn_prime

  calc _
  -- Rewrite as sum over interval from `nth Nat.Prime 0` to `nth Nat.Prime i`.
  _ = ∑ i ∈ Ico (nth Nat.Prime 0) (nth Nat.Prime i), 1 / (P i * N i : ℚ) := by
    rw [nth_prime_zero_eq_two, hi]
  -- Partition the interval into a union of intervals.
  _ = ∑ i ∈ Ico (nth Nat.Prime 0) (nth Nat.Prime i), 1 / (P i * N i : ℚ) := by
    sorry
  _ = _ := by

    sorry
