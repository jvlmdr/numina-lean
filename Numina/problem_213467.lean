-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9z0020ueaxjchnxxp7

import Mathlib

/- $n$ is a positive integer. Try to determine how many real numbers $x$ satisfy
$1 \le x < n$ and $x^{3} - [x^{3}] = (x - [x])^{3}$. -/

-- The sum of squares is a product that is divisible by 6.
-- It is easier to simplify expressions with addition only in the natural numbers.
lemma sum_range_succ_sq_mul_six (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), k ^ 2) * 6 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [Finset.sum_range_succ, add_mul, IH]
    ring

-- The expression for the sum of squares using subtraction.
lemma sum_range_sq_mul_six (n : ℕ) :
    (∑ k in Finset.range n, k ^ 2) * 6 = (n - 1) * n * (2 * n - 1) := by
  cases n with
  | zero => simp
  | succ n => simpa using sum_range_succ_sq_mul_six n

lemma sum_range_sq (n : ℕ) :
    ∑ k ∈ Finset.range n, k ^ 2 = (n - 1) * n * (2 * n - 1) / 6 :=
  Nat.eq_div_of_mul_eq_left (by norm_num) (sum_range_sq_mul_six n)

lemma sum_range_succ_mul_two (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), k) * 2 = n * (n + 1) := by
  rw [Finset.sum_range_id_mul_two, add_tsub_cancel_right]
  ring


theorem algebra_213467 (n : ℕ) (hn : 0 < n) :
    {x : ℝ | 1 ≤ x ∧ x < n ∧ x ^ 3 - ⌊x ^ 3⌋ = (x - ⌊x⌋) ^ 3}.ncard = n ^ 3 - n := by
  calc _
  -- _ = ∑ a in Finset.range n, ((a + 1) ^ 3 - 1 - a ^ 3) := by
  --   sorry
  _ = ∑ a in Finset.range n, (3 * a ^ 2 + 3 * a) := by sorry

  -- Introduce factors of 6 and 2 to obtain integer expressions for each sum.
  _ = (∑ a in Finset.range n, (a ^ 2 + a)) * 3 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  _ = (∑ a in Finset.range n, (a ^ 2 + a)) * 6 / 2 := by
    rw [Nat.mul_div_assoc _ (by norm_num)]
  _ = ((∑ a in Finset.range n, a ^ 2) * 6 + (∑ a in Finset.range n, a) * 2 * 3) / 2 := by
    simp [Finset.sum_add_distrib, add_mul, mul_assoc]
  -- Use `ring` in `ℤ` to prove that expressions are equal.
  _ = (n ^ 3 - n) * 2 / 2 := by
    congr 1
    rw [Finset.sum_range_id_mul_two, sum_range_sq_mul_six]
    -- This is easy to prove in `ℤ`.
    have : (n - 1) * n * (2 * n - 1) + n * (n - 1) * 3 = ((n ^ 3 - n) * 2 : ℤ) := by ring
    rw [← @Nat.cast_inj ℤ]
    -- Provide necessary conditions for `Nat.cast_sub`.
    have h₁ : 1 ≤ n := hn
    have h₂ : 1 ≤ 2 * n := by linarith
    have h₃ : n ≤ n ^ 3 := Nat.le_self_pow three_ne_zero n
    simpa [h₁, h₂, h₃] using this
  _ = n ^ 3 - n := by simp
