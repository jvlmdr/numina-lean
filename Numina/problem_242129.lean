-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9z001wueaxr6lrtr7p

import Mathlib

/- Let $f(x) = a_{0} + a_{1} x + a_{2} x^{2} + \ldots + a_{n} x^{n}$, $a_{i} \ge 0$
($i = 0, 1, 2, \ldots n$), and in the interval $[-1, +1]$, $|f(x)| \le 1$.
Show that in this interval $\left|f^{\prime}(x)\right| \le n$;
the equality holds only when $f(x) = x^{n}$. -/

theorem algebra_242129 {n : ℕ} (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : ℝ → ℝ) (hf : ∀ x, f x = ∑ i, a i * x ^ i.val)
    (h : ∀ x ∈ Set.Icc (-1) 1, |f x| ≤ 1) :
    (∀ x ∈ Set.Icc (-1) 1, |deriv f x| ≤ n) ∧
    ((∃ x ∈ Set.Icc (-1) 1, |deriv f x| = n) ↔ f = fun x ↦ x ^ n) := by

  -- From `|f x| ≤ 1`, we can establish a bound on the sum of the coefficients.
  have ha_sum : ∑ i, a i ≤ 1 := by
    calc _
    _ = f 1 := by simp [hf]
    _ ≤ |f 1| := le_abs_self (f 1)
    _ ≤ 1 := h 1 (by simp)

  constructor
  · intro x hx
    rw [funext hf]
    rw [deriv_sum (fun i _ ↦ (differentiable_pow i.val).const_mul (a i) x)]
    simp [← mul_assoc]
    simp [Fin.sum_univ_succ]
    suffices |∑ i : Fin n, a i.succ * (i + 1 : ℕ) * x ^ i.val| ≤ n by simpa

    -- TODO: integrate above into `calc`?
    calc _
    _ = |∑ i : Fin n, a i.succ * (i + 1 : ℕ) * x ^ i.val| := by simp
    _ ≤ ∑ i : Fin n, a i.succ * (i + 1 : ℕ) := by
      -- this could be the hard part?
      sorry
    _ ≤ ∑ i : Fin n, a i.succ * n := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      gcongr
      · exact ha _
      · exact i.isLt
    _ = (∑ i : Fin n, a i.succ) * n := by rw [Finset.sum_mul]
    _ ≤ (n : ℝ) := by
      refine mul_le_of_le_one_left (Nat.cast_nonneg n) ?_
      refine le_trans ?_ ha_sum
      rw [Fin.sum_univ_succ]
      simpa using ha 0

  · -- TODO: confirm condition here
    sorry
