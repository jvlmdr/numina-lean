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

-- Since we have `Monotone.biUnion_Ico_Ioc_map_succ` for `Ioc` and no equivalent for `Ico`,
-- define a lemma to convert `Ioc` with preceding elements to `Ico`.
lemma Ioc_sub_one_sub_one_eq_Ico {a : ℕ} (ha : a ≠ 0) (b : ℕ) :
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

-- The supremum below `n` will be constant between `nth p k` and `nth p (k + 1)`.
lemma csSup_le_eq_of_mem_Ico_nth {p : ℕ → Prop} {n k : ℕ} (hn : n ∈ Ico (nth p k) (nth p (k + 1)))
    (hp : ∀ (hf : (setOf p).Finite), k < #hf.toFinset) :
    sSup {x | p x ∧ x ≤ n} = nth p k := by
  simp only [mem_Ico] at hn
  refine csSup_eq_of_is_forall_le_of_forall_le_imp_ge ?_ ?_ ?_
  · suffices nth p k ∈ {x | p x ∧ x ≤ n} from Set.nonempty_of_mem this
    simpa [Set.mem_setOf_eq] using ⟨nth_mem k hp, hn.1⟩
  · simp only [Set.mem_setOf_eq, and_imp]
    intro a ha han
    refine le_nth_of_lt_nth_succ ?_ ha
    exact lt_of_le_of_lt han hn.2
  · simp only [Set.mem_setOf_eq, and_imp]
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

-- The infimum above `n` will be constant between `nth p k` and `nth p (k + 1)`.
lemma csInf_lt_eq_of_mem_Ico_nth {p : ℕ → Prop} {n k : ℕ} (hn : n ∈ Ico (nth p k) (nth p (k + 1)))
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

  -- Obtain `k` such that `n = nth Nat.Prime k`.
  have h_not_fin : ¬(setOf Nat.Prime).Finite := infinite_setOf_prime
  obtain ⟨k, hk⟩ : ∃ k, nth Nat.Prime k = n := by
    simpa [h_not_fin] using exists_lt_card_nth_eq hn_prime

  calc _
  -- Rewrite as sum over interval from `nth Nat.Prime 0` to `nth Nat.Prime i`.
  _ = ∑ i ∈ Ico (nth Nat.Prime 0) (nth Nat.Prime k), 1 / (P i * N i : ℚ) := by
    rw [nth_prime_zero_eq_two, hk]
  -- Partition the interval into a union of intervals.
  _ = ∑ i ∈ (range k).biUnion fun j ↦ Ico (nth Nat.Prime j) (nth Nat.Prime (j + 1)),
      1 / (P i * N i : ℚ) := by
    congr
    -- We want to split the interval into a union of `Finset.Ico` intervals.
    -- We have `Monotone.biUnion_Ico_Ioc_map_succ`, which uses `Set.Ioc`.
    -- Since primes start at 2, we can use `Ioc` and subtract 1.
    refine Finset.coe_injective ?_
    symm
    convert Monotone.biUnion_Ico_Ioc_map_succ (f := fun i ↦ nth Nat.Prime i - 1) ?_ 0 k
    · rw [coe_biUnion]
      refine Set.iUnion_congr fun i ↦ ?_
      simp [Ioc_sub_one_sub_one_eq_Ico (prime_nth_prime i).ne_zero]
    · rw [coe_Ico, Ioc_sub_one_sub_one_eq_Ico]
      simp
    · intro i j hij
      refine Nat.sub_le_sub_right ?_ 1
      exact (nth_le_nth h_not_fin).mpr hij
  -- Use disjointness to sum over indexed union as a nested sum.
  _ = ∑ j ∈ range k, ∑ i ∈ Ico (nth Nat.Prime j) (nth Nat.Prime (j + 1)), 1 / (P i * N i : ℚ) := by
    refine sum_biUnion ?_
    rw [← pairwiseDisjoint_coe]
    intro j hj i hi hij
    simpa using (nth_monotone h_not_fin).pairwise_disjoint_on_Ico_succ hij
  -- Replace `P i` and `N i` with constant within interval.
  _ = ∑ j ∈ range k, ∑ i ∈ Ico (nth Nat.Prime j) (nth Nat.Prime (j + 1)),
      1 / (nth Nat.Prime j * nth Nat.Prime (j + 1) : ℚ) := by
    refine sum_congr rfl fun j _ ↦ ?_
    refine sum_congr rfl fun i hi ↦ ?_
    congr
    · rw [hP]
      refine csSup_le_eq_of_mem_Ico_nth hi ?_
      simp [h_not_fin]
    · rw [hN]
      refine csInf_lt_eq_of_mem_Ico_nth hi ?_
      simp [h_not_fin]
  -- Replace the constant sums with multiplication.
  _ = ∑ j ∈ range k, ↑(nth Nat.Prime (j + 1) - nth Nat.Prime j) /
      (nth Nat.Prime j * nth Nat.Prime (j + 1) : ℚ) := by simp [div_eq_mul_inv]
  -- Rewrite difference over product as difference of reciprocals.
  _ = ∑ j ∈ range k, (1 / nth Nat.Prime j - 1 / nth Nat.Prime (j + 1) : ℚ) := by
    simp only [one_div]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [cast_sub (nth_monotone infinite_setOf_prime (j.le_add_right 1))]
    refine (inv_sub_inv ?_ ?_).symm
    · simpa using (prime_nth_prime j).ne_zero
    · simpa using (prime_nth_prime (j + 1)).ne_zero
  -- Cancel terms in telescoping sum.
  _ = _ := by
    rw [sum_range_sub', hk]
    simp only [nth_prime_zero_eq_two, one_div]
    refine inv_sub_inv two_ne_zero ?_
    simpa using hn_prime.ne_zero
