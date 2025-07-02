-- https://cloud.kili-technology.com/label/projects/label/cmcbouv7300moueaxaag69l3n

import Mathlib

/- Find all positive integers $N$, such that it equals the sum of the digits of $N^{3}$. -/

-- Upper bound on the `Nat.log` of a power.
-- Use this to bound the number of digits in `N ^ 3`.
lemma log_pow_lt_mul_log_add_one (b n k : ℕ) (hb : 1 < b) (hk : k ≠ 0) :
    Nat.log b (n ^ k) < k * (Nat.log b n + 1) := by
  rw [← Nat.one_le_iff_ne_zero] at hk
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk IH =>
    cases eq_or_ne n 0 with
    | inl hn => simp [hn]
    | inr hn =>
      refine Nat.log_lt_of_lt_pow (by simpa) ?_
      -- Split the product `n ^ (k + 1)` into `n ^ k * n`.
      have h₁ : n ^ k < b ^ (k * (Nat.log b n + 1)) := Nat.lt_pow_of_log_lt hb IH
      have h₂ : n < b ^ (Nat.log b n + 1) := Nat.lt_pow_succ_log_self hb n
      convert Nat.mul_lt_mul'' h₁ h₂ using 1
      ring

-- If `p` is a predicate on `ℕ` with period `c`, it is equivalent to membership in a `Finset`.
lemma periodic_pred_iff_mod_mem_filter_range {p : ℕ → Prop} [DecidablePred p] {c : ℕ}
    (hp : p.Periodic c) (hc : c ≠ 0) (n : ℕ) :
    p n ↔ n % c ∈ (Finset.range c).filter p := by
  calc _
  _ ↔ p (n % c) := by rw [hp.map_mod_nat]
  _ ↔ _ := by
    rw [Finset.mem_filter, Finset.mem_range, iff_and_self]
    intro _
    exact Nat.mod_lt n (Nat.pos_of_ne_zero hc)

-- Obtain the final set of solutions by exhaustively checking the digit sum for the candidates.
lemma lemma_1 (n : ℕ) (hn_sum : n = (Nat.digits 10 (n ^ 3)).sum)
    (hn_zero : n ≠ 0) (hn_le : n ≤ 54) (hn_mod : n % 9 ∈ ({0, 1, 8} : Set ℕ)) :
    n = 1 ∨ n = 8 ∨ n = 17 ∨ n = 18 ∨ n = 26 ∨ n = 27 := by
  -- Write the conditions as membership in a single `Finset`.
  have hn_mem : n ∈ (Finset.Icc 1 54).filter (· % 9 ∈ ({0, 1, 8} : Set ℕ)) := by
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨Nat.pos_of_ne_zero hn_zero, hn_le⟩
    · exact hn_mod
  -- Make the set of candidates explicit.
  suffices ∀ n,
      n ∈ ({1, 8, 9, 10, 17, 18, 19, 26, 27, 28, 35, 36, 37, 44, 45, 46, 53, 54} : Finset ℕ) →
      n = (Nat.digits 10 (n ^ 3)).sum → n = 1 ∨ n = 8 ∨ n = 17 ∨ n = 18 ∨ n = 26 ∨ n = 27 from
    this n hn_mem hn_sum
  -- Check the digit sums of this subset of numbers exhaustively.
  simp

theorem number_theory_295394 (n : ℕ) :
    n ≠ 0 ∧ n = (Nat.digits 10 (n ^ 3)).sum ↔
    n = 1 ∨ n = 8 ∨ n = 17 ∨ n = 18 ∨ n = 26 ∨ n = 27 := by
  -- First confirm that each solution is valid.
  constructor
  swap
  · revert n
    simp

  intro ⟨hn_zero, hn_eq⟩
  -- Let `k` be the number of digits in `n`.
  let k := Nat.log 10 n + 1
  have hn_len : (Nat.digits 10 n).length = k := Nat.digits_len 10 n (by norm_num) hn_zero
  -- The number of digits in `n ^ 3` is at most `3 * k`.
  have hn3_len : (Nat.digits 10 (n ^ 3)).length ≤ 3 * k := by
    rw [Nat.digits_len 10 (n ^ 3) (by norm_num) (pow_ne_zero 3 hn_zero)]
    exact log_pow_lt_mul_log_add_one 10 n 3 (by norm_num) (by norm_num)
  -- The digit sum of `n ^ 3` is at most `9 * (3 * k) = 27 * k`.
  have hn3_sum : (Nat.digits 10 (n ^ 3)).sum ≤ 27 * k :=
    calc _
    _ ≤ (Nat.digits 10 (n ^ 3)).length * 9 := by
      refine List.sum_le_card_nsmul _ _ fun x hx ↦ ?_
      exact Nat.le_of_lt_succ (Nat.digits_lt_base' hx)
    _ ≤ 3 * k * 9 := Nat.mul_le_mul_right 9 hn3_len
    _ = _ := by ring

  -- When `k > 2`, we find that `n` (equal to the digit sum of `n ^ 3`) must exceed `27 * k`.
  cases le_or_lt k 2 with
  | inr hk =>
    exfalso
    suffices 27 * k < n from hn3_sum.not_lt (hn_eq ▸ this)
    calc
    _ < 10 * 9 * (k - 2) := by
      rw [mul_tsub]
      refine lt_tsub_of_add_lt_left ?_
      linarith
    _ < 10 * 10 ^ (k - 2) := by
      simp only [mul_assoc]
      gcongr
      -- Put in the form to match `one_add_mul_sub_le_pow` (Bernoulli's inequality).
      rw [mul_comm 9, ← Nat.one_add_le_iff]
      rw [← Int.ofNat_le]
      simpa using one_add_mul_sub_le_pow (a := (10 : ℤ)) (by simp) (k - 2)
    _ = 10 ^ (k - 2 + 1) := by rw [Nat.pow_succ']
    _ = 10 ^ (k - 1) := by
      -- Re-arrange to show `k - 1 = k - 2 + 1` since `k ≥ 2`.
      congr
      rw [← Nat.sub_add_comm (by linarith)]
      simp
    _ ≤ n := by
      -- Use the fact that `n` is bounded below using the number of digits.
      suffices 10 * 10 ^ (k - 1) ≤ 10 * n from le_of_mul_le_mul_left this (by norm_num)
      convert Nat.base_pow_length_digits_le' _ n hn_zero using 1
      simp only [k, Nat.add_one_sub_one, hn_len]
      ring

  | inl hk =>
    -- Since `n` has at most 2 digits, `n ^ 3` has at most 6 digits, and
    -- its digit sum is at most `6 * 9 = 54`.
    have hn : n ≤ 54 := by
      rw [hn_eq]
      exact le_trans hn3_sum (by linarith)
    -- Since `10 % 9 = 1`, `n ^ 3` is congruent to its digit sum (equal to `n`) modulo 9.
    have hn3_mod : n ^ 3 ≡ n [MOD 9] := by
      calc _
      _ ≡ (Nat.digits 10 (n ^ 3)).sum [MOD 9] := Nat.modEq_digits_sum 9 10 (by norm_num) (n ^ 3)
      _ ≡ n [MOD 9] := by rw [← hn_eq]
    -- Due to periodicity, it suffices to identify the `x = n % 9` such that `x ^ 3 ≡ x [MOD 9]`.
    have hn_mod : n % 9 ∈ (Finset.range 9).filter fun x ↦ x ^ 3 ≡ x [MOD 9] := by
      refine (periodic_pred_iff_mod_mem_filter_range ?_ (by norm_num) n).mp hn3_mod
      -- Use the fact that `n ^ 3 % 9` is equal to `(n % 9) ^ 3 % 9` to show periodicity.
      convert (Nat.periodic_mod 9).comp fun n ↦ n ^ 3 % 9 = n using 2 with n
      simp [Nat.pow_mod, Nat.ModEq]
    -- Make this set explicit.
    change n % 9 ∈ ({0, 1, 8} : Finset ℕ) at hn_mod
    -- Exhaustively check the candidates.
    exact lemma_1 n hn_eq hn_zero hn (by simpa using hn_mod)
