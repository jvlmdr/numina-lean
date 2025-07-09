-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9z001wueaxr6lrtr7p

import Mathlib

open Finset Polynomial

/- Let $f(x) = a_{0} + a_{1} x + a_{2} x^{2} + \ldots + a_{n} x^{n}$, $a_{i} \ge 0$
($i = 0, 1, 2, \ldots n$), and in the interval $[-1, +1]$, $|f(x)| \le 1$.
Show that in this interval $\left|f^{\prime}(x)\right| \le n$;
the equality holds only when $f(x) = x^{n}$. -/

-- For any polynomial with non-negative coefficients, the maximum on `[-1, 1]` is attained at 1.
lemma abs_poly_le_sum_coeff_of_nonneg_of_mem_Icc {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |∑ i : Fin n, a i * x ^ i.val| ≤ ∑ i : Fin n, a i :=
  calc _
  _ ≤ ∑ i, |a i * x ^ i.val| := abs_sum_le_sum_abs _ _
  _ ≤ ∑ i, |a i| := by
    refine sum_le_sum fun i _ ↦ ?_
    rw [abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)
  _ = ∑ i : Fin n, a i := by
    refine sum_congr rfl fun i _ ↦ ?_
    exact abs_of_nonneg (ha i)

-- If the weighted sum `∑ j, w j * f j` is equal to the unique positive maximum `f i`
-- with non-negative weights `∑ j, w j ≤ 1`, then `w i = 1` and all other `w j = 0`.
lemma nonneg_weighted_sum_eq_unique_pos_max_iff {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w f : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hw_sum : ∑ i ∈ s, w i ≤ 1)
    (i : ι) (hi : i ∈ s) (hf_pos : 0 < f i) (hf_lt : ∀ j ∈ s, j ≠ i → f j < f i) :
    ∑ j ∈ s, w j * f j = f i ↔ w i = 1 ∧ ∀ j ∈ s, j ≠ i → w j = 0 := by
  constructor
  · intro h
    -- It is easy to show that `w i = 1` once it is known that all other elements are zero.
    suffices ∀ j ∈ s, j ≠ i → w j = 0 by
      refine ⟨?_, this⟩
      suffices w i * f i = f i from (mul_eq_right₀ hf_pos.ne').mp this
      convert h
      rw [← add_sum_erase s _ hi]
      suffices ∑ x ∈ s.erase i, w x * f x = 0 by simpa
      refine sum_eq_zero fun j hj ↦ ?_
      suffices w j = 0 by simp [this]
      exact this j (mem_of_mem_erase hj) (ne_of_mem_erase hj)
    -- This will follow from contradiction.
    -- If there exists some `j ≠ i` with `w j ≠ 0`, then the sum is strictly less than `f i`.
    contrapose! h
    refine ne_of_lt ?_
    calc _
    _ < ∑ j ∈ s, w j * f i := by
      refine sum_lt_sum ?_ (h.imp ?_)
      · intro j hj
        refine mul_le_mul_of_nonneg_left ?_ (hw j hj)
        refine (eq_or_ne j i).elim ?_ ?_
        · exact fun hji ↦ (congrArg f hji).le
        · exact fun hji ↦ (hf_lt j hj hji).le
      · intro j ⟨hjs, hji, hwj⟩
        refine ⟨hjs, ?_⟩
        have hwj : 0 < w j := lt_of_le_of_ne (hw j hjs) hwj.symm
        exact (mul_lt_mul_left hwj).mpr (hf_lt j hjs hji)
    _ = (∑ j ∈ s, w j) * f i := by simp [sum_mul]
    _ ≤ _ := (mul_le_iff_le_one_left hf_pos).mpr hw_sum
  · -- The reverse direction can be established by substitution.
    intro ⟨ha_one, ha_zero⟩
    calc _
    _ = w i * f i + ∑ j ∈ s.erase i, w j * f j := (add_sum_erase s _ hi).symm
    _ = _ := by
      suffices ∑ j ∈ s.erase i, w j * f j = 0 by simpa [ha_one]
      refine sum_eq_zero fun j hj ↦ ?_
      suffices w j = 0 by simp [this]
      refine ha_zero j ?_ ?_
      · exact mem_of_mem_erase hj
      · exact ne_of_mem_erase hj

-- Convenient version for the case where `s = univ`.
lemma nonneg_weighted_sum_eq_unique_pos_max_iff_univ {ι : Type*} [DecidableEq ι] [Fintype ι]
    (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i ≤ 1)
    (i : ι) (hf_pos : 0 < f i) (hf_lt : ∀ j ≠ i, f j < f i) :
    ∑ j, w j * f j = f i ↔ w i = 1 ∧ ∀ j, j ≠ i → w j = 0 := by
  simpa using nonneg_weighted_sum_eq_unique_pos_max_iff univ w f (fun i _ ↦ hw i) hw_sum
    i (mem_univ i) hf_pos fun j _ ↦ hf_lt j

theorem algebra_242129 (n : ℕ) (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : ℝ[X]) (hf : f = ∑ i, C (a i) * X ^ i.val)
    (hf_abs : ∀ x ∈ Set.Icc (-1) 1, |f.eval x| ≤ 1) :
    (∀ x ∈ Set.Icc (-1) 1, |f.derivative.eval x| ≤ n) ∧
    (0 < n → ((∃ x ∈ Set.Icc (-1) 1, |f.derivative.eval x| = n) ↔ f = X ^ n)) := by
  -- Note that we must exclude the `n = 0` case from the condition for equality.
  -- In this case, $|f'(x)| = 0 ≤ n$ for any $f(x) = a_0$; we cannot infer $f(x) = x^0 = 1$.

  -- From `|f x| ≤ 1`, we can establish a bound on the sum of the coefficients.
  have ha_sum : ∑ i, a i ≤ 1 :=
    calc _
    _ = f.leval 1 := by simp [hf]
    _ ≤ |f.eval 1| := le_abs_self _
    _ ≤ 1 := hf_abs 1 (by simp)
  -- The absolute derivative is also a polynomial with non-negative coefficients.
  -- Use this to bound its absolute value on `[-1, 1]`.
  have hf_abs_deriv_le (x : ℝ) (hx : x ∈ Set.Icc (-1) 1) :
      |f.derivative.eval x| ≤ ∑ i : Fin n, a i.succ * (i + 1 : ℕ) :=
    calc _
    _ = |f.derivative.aeval x| := rfl
    _ = |∑ i : Fin n, a i.succ * (i + 1 : ℕ) * x ^ i.val| := by
      simp [hf, Fin.sum_univ_succ, mul_assoc]
    _ ≤ _ := by
      refine abs_poly_le_sum_coeff_of_nonneg_of_mem_Icc _ ?_ hx
      exact fun i ↦ mul_nonneg (ha i.succ) (Nat.cast_nonneg (i + 1))
  -- The sum of the coefficients of the derivative can be bounded above by `n`.
  have h_sum_deriv_coeffs_le : ∑ i : Fin n, a i.succ * (i + 1 : ℕ) ≤ n := by
    calc _
    _ ≤ ∑ i : Fin n, a i.succ * n := by
      refine sum_le_sum fun i _ ↦ ?_
      gcongr
      · exact ha _
      · exact i.isLt
    _ = (∑ i : Fin n, a i.succ) * n := by rw [sum_mul]
    _ ≤ (n : ℝ) := by
      refine mul_le_of_le_one_left (Nat.cast_nonneg n) ?_
      refine le_trans ?_ ha_sum
      rw [Fin.sum_univ_succ]
      simpa using ha 0

  -- Combine the two inequalities to establish the desired bound.
  refine ⟨fun x hx ↦ (hf_abs_deriv_le x hx).trans h_sum_deriv_coeffs_le, ?_⟩
  -- It remains to establish uniqueness of the polynomial $f(x) = x^n$ for $n > 0$.
  intro hn
  -- Establish the reverse direction first as it is trivial.
  refine ⟨?_, fun hf ↦ ⟨1, by simp, by simp [hf]⟩⟩

  intro ⟨x, hx, hf_abs_deriv⟩
  -- Equality of the polynomials is established by equality of coefficients.
  suffices a (Fin.last n) = 1 ∧ ∀ i ≠ Fin.last n, a i = 0 by
    calc _
    _ = ∑ i : Fin (n + 1), C (a i) * X ^ i.val := by rw [hf]
    _ = C (a (Fin.last n)) * X ^ n + ∑ i : Fin n, C (a i.castSucc) * X ^ i.val := by
      simp [Fin.sum_univ_succAbove _ (Fin.last n)]
    _ = C (a (Fin.last n)) * X ^ n + 0 := by
      congr 1
      refine sum_eq_zero fun i _ ↦ ?_
      simpa using this.2 _ i.castSucc_lt_last.ne
    _ = X ^ n := by simp [this.1]

  -- When the bound is achieved, all elements of the inequality chain are equal.
  -- In particular, this implies that the sum of the coefficients of the derivative
  -- must be equal to `n`.
  suffices ∑ i : Fin (n + 1), a i * i = n by
    refine (nonneg_weighted_sum_eq_unique_pos_max_iff_univ a _ ha ha_sum _ ?_ ?_).mp this
    · simpa using hn
    · intro j hj
      simpa using Fin.val_lt_last hj
  calc _
  _ = ∑ i : Fin n, a i.succ * (i + 1 : ℕ) := by simp [Fin.sum_univ_succ]
  _ = _ := by
    refine le_antisymm ?_ ?_
    · exact h_sum_deriv_coeffs_le
    · calc _
      _ = |f.derivative.eval x| := hf_abs_deriv.symm
      _ ≤ _ := hf_abs_deriv_le x hx
