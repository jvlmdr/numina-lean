-- https://cloud.kili-technology.com/label/projects/label/cma3ygioc00bjahay2hc6qsbe

import Mathlib

/- Let $n$ be a natural number. Prove that the binary representation of the integer
$n (2^{n} - 1)$ contains exactly $n$ occurrences of the digit 1. -/

-- For base 2, the number of 1s is equal to the sum of the digits.
lemma count_one_digits_two_eq_sum (n : ℕ) :
    (Nat.digits 2 n).count 1 = (Nat.digits 2 n).sum := by
  have hl : ∀ x ∈ Nat.digits 2 n, x < 2 := fun x hx ↦ Nat.digits_lt_base' hx
  generalize Nat.digits 2 n = l at hl
  induction l with
  | nil => simp
  | cons x l IH =>
    rw [List.count_cons, List.sum_cons, add_comm]
    congr
    · have hx : x < 2 := by simpa using hl x
      interval_cases x <;> simp
    · exact IH fun i hi ↦ hl i (List.mem_cons_of_mem x hi)

-- We can decompose `2 ^ (n + 1) - 1` in terms of `2 ^ n - 1`.
lemma mersenne_succ (n : ℕ) : mersenne (n + 1) = 2 * mersenne n + 1 := by
  suffices mersenne (n + 1) + 1 = 2 * (mersenne n + 1) by
    simpa only [mul_add, mul_one, add_left_inj] using this
  simp only [succ_mersenne, pow_succ']

-- Defined in analogy to `Nat.digits_add`.
-- For the digit sum, we do not require `x ≠ 0` or `y ≠ 0`.
lemma sum_digits_add {b : ℕ} (hb : 1 < b) {x y : ℕ} (hxb : x < b) :
    (b.digits (x + b * y)).sum = x + (b.digits y).sum := by
  cases y with
  | zero =>
    cases x with
    | zero => simp
    | succ x => simp [hxb]
  | succ y => rw [Nat.digits_add b hb _ _ hxb] <;> simp

-- For the digit sum, we can ignore whether `y` is non-zero, whether zeros must be inserted.
lemma sum_digits_add_base_pow_mul {b : ℕ} (hb : 1 < b) {x k y : ℕ} (hxb : x < b ^ k) :
    (b.digits (x + b ^ k * y)).sum = (b.digits x).sum + (b.digits y).sum := by
  cases y.eq_zero_or_pos with
  | inl hy => simp [hy]
  | inr hy =>
    calc _
    _ = (b.digits x ++ List.replicate (k - (b.digits x).length) 0 ++
        b.digits y).sum := by
      rw [Nat.digits_append_zeroes_append_digits hb hy]
      congr
      suffices (b.digits x).length ≤ k from (Nat.add_sub_of_le this).symm
      cases eq_or_ne x 0 with
      | inl hx => simp [hx]
      | inr hx =>
        rw [Nat.digits_len _ _ hb hx]
        exact Nat.log_lt_of_lt_pow hx hxb
    _ = _ := by simp

-- Given that two numbers sum to `11⋯1` in binary, they will have complementary digits.
-- We cannot have a carry in any place, otherwise a zero would result in `a + b`.
lemma sum_digits_of_add_eq_mersenne (n a b : ℕ) (hab : a + b = mersenne n) :
    (Nat.digits 2 a).sum + (Nat.digits 2 b).sum = n := by
  induction n generalizing a b with
  | zero =>
    obtain ⟨ha, hb⟩ : a = 0 ∧ b = 0 := by simpa using hab
    simp [ha, hb]
  | succ n IH =>
    -- Since `a + b = 2 ^ n - 1`, the sum is odd.
    have h_odd : Odd (a + b) := by simp [hab]
    -- By the symmetry of addition, we can assume wlog that `a` is even and `b` is odd.
    wlog h : Even a ∧ Odd b generalizing a b
    · rw [add_comm]
      refine this b a ?_ ?_ ?_
      · exact add_comm a b ▸ hab
      · exact add_comm a b ▸ h_odd
      · -- It suffices to show that `a` is odd.
        suffices Odd a by simpa [← Nat.odd_add.mp h_odd]
        -- We can obtain this from `¬Even a`.
        simpa [Nat.odd_add'.mp h_odd] using h
    -- Re-parameterize `a` and `b`.
    rcases h with ⟨hu, hv⟩
    obtain ⟨u, rfl⟩ : ∃ u, a = 2 * u := hu.exists_two_nsmul
    obtain ⟨v, rfl⟩ : ∃ v, b = 2 * v + 1 := hv.exists_bit1
    calc _
    -- Express as `x + 2 * y` and apply `sum_digits_add`.
    _ = (Nat.digits 2 (0 + 2 * u)).sum + (Nat.digits 2 (1 + 2 * v)).sum := by congr 3 <;> ring
    _ = (Nat.digits 2 u).sum + (Nat.digits 2 v).sum + 1 := by
      rw [sum_digits_add one_lt_two one_lt_two, sum_digits_add one_lt_two zero_lt_two]
      ring
    -- Show that `u + v = mersenne n` to apply the inductive hypothesis.
    _ = _ := by
      congr
      refine IH u v ?_
      suffices 2 * (u + v) + 1 = mersenne (n + 1) by simpa [mersenne_succ]
      refine .trans ?_ hab
      ring

theorem number_theory_291009 (n : ℕ) :
    (Nat.digits 2 (n * (2 ^ n - 1))).count 1 = n := by
  -- Introduce the assumption that `1 < n`; trivial to show for `n = 0` or `n = 1`.
  wlog hn : 1 < n
  · rw [not_lt] at hn
    interval_cases n <;> simp

  let s := n - 1
  let t := 2 ^ n - n
  -- Show that both `s` and `t` are positive.
  have hs_pos : 0 < s := by simpa [s] using hn
  have ht_pos : 0 < t := by simpa [t] using Nat.lt_two_pow_self
  -- Show that the subtraction in the natural numbers does not result in a truncation.
  -- This will be useful for using the `ring` tactic in `ℤ`.
  have hs_int : (s : ℤ) = n - 1 := by simp [Nat.cast_sub hn.le]
  have ht_int : (t : ℤ) = 2 ^ n - n := by simp [Nat.cast_sub Nat.lt_two_pow_self.le]

  -- Show that we can rewrite `n * (2 ^ n - 1)` as a combination of `t < 2 ^ n` and `2 ^ n * s`.
  have h_eq : n * (2 ^ n - 1) = t + 2 ^ n * s := by
    suffices n * (2 ^ n - 1) = (t + 2 ^ n * s : ℤ) by
      rw [← @Nat.cast_inj ℤ]
      simpa
    rw [hs_int, ht_int]
    ring
  -- Show that the two numbers add to give `2 ^ n - 1`, which is a string of 1s in binary.
  have h_add : t + s = 2 ^ n - 1 := by
    suffices (t + s : ℤ) = 2 ^ n - 1 by
      rw [← @Nat.cast_inj ℤ]
      simpa
    rw [hs_int, ht_int]
    ring

  -- Switch from count of 1s to sum of digits.
  rw [count_one_digits_two_eq_sum]
  -- Substitute expression using `s, t`.
  rw [h_eq]
  -- Separate into sums of digits of each.
  rw [sum_digits_add_base_pow_mul one_lt_two (by simp [t, Nat.zero_lt_of_lt hn])]
  -- Use the result for two natural numbers that add to a Mersenne number.
  exact sum_digits_of_add_eq_mersenne n t s h_add
