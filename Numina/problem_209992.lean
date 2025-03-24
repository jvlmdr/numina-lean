-- https://cloud.kili-technology.com/label/projects/label/cm8ct04tl021j5kayw6plycyu

import Mathlib

/- Prove that there are infinitely many natural numbers that cannot be represented
as the sum of the square of an integer and a prime number. -/

theorem number_theory_209992 :
    ∀ a : ℕ, ∃ x > a, ¬∃ n p : ℕ, p.Prime ∧ x = n ^ 2 + p := by
  intro a
  -- If we set `x = m ^ 2` for some `m ≥ n`, then we have `p = (m - n) (m + n)`.
  -- Since `p` is prime and `m - n ≤ m + n`, this implies `m - n = 1` and `m + n = p`.
  -- Putting these together, we have `p = 2 m - 1`.
  -- If we further choose `m = 3 k + 2`, then `p = 6 k + 3` is divisible by 3.
  -- This is a contradiction provided that `k ≠ 0`.
  -- Hence choose `x = (3 k + 2) ^ 2` with `k = a.succ`.
  let k := a.succ
  use (3 * k + 2) ^ 2
  refine ⟨?_, ?_⟩
  · calc (3 * k + 2) ^ 2
    _ > 3 * k + 2 := by refine lt_self_pow₀ ?_ ?_ <;> linarith
    _ > a := by linarith
  simp only [not_exists, not_and]
  intro n p hp_prime
  -- Prove that `p` is not prime as `(3 k + 2)^2 = n^2 + p` implies `p = 3 (2 k + 1)`.
  suffices (3 * k + 2) ^ 2 = n ^ 2 + p → 3 * (2 * k + 1) = p by
    intro hp
    revert hp_prime
    exact Nat.not_prime_mul' (this hp) (by norm_num) (by simp)
  intro hp
  -- Extract a proof that `n ≤ 3 k + 2` from `(3 k + 2)^2 = n^2 + p` before
  -- moving `n^2` to the other side.
  have hn : n ≤ 3 * k + 2 := by
    rw [← (Nat.pow_left_strictMono two_ne_zero).le_iff_le]
    linarith
  rw [← Nat.sub_eq_iff_eq_add' (by linarith)] at hp
  rw [Nat.sq_sub_sq] at hp

  -- If `p = u * v`, then one of `u, v` is 1 and the other is `p`.
  have h_prime_mul {u v : ℕ} (h_mul : p = u * v) : u + v = p + 1 := by
    rw [h_mul] at hp_prime ⊢
    cases Nat.prime_mul_iff.mp hp_prime with
    | inl h => rw [h.2]; ring
    | inr h => rw [h.2]; ring
  replace hp := h_prime_mul hp.symm

  -- Add one on either side to relate to our expression for `p + 1`.
  suffices 3 * (2 * k + 1) + 1 = p + 1 by simpa using this
  convert hp using 1
  -- Show that the `n` terms can be cancelled since `n ≤ 3 k + 2`.
  symm
  calc 3 * k + 2 + n + (3 * k + 2 - n)
  _ = 3 * k + 2 + (n + (3 * k + 2 - n)) := by rw [add_assoc]
  _ = 3 * k + 2 + (n + (3 * k + 2) - n) := by rw [Nat.add_sub_assoc hn _]
  _ = 3 * k + 2 + (3 * k + 2) := by rw [add_tsub_cancel_left]
  _ = 3 * (2 * k + 1) + 1 := by ring
