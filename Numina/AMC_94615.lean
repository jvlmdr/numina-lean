-- https://cloud.kili-technology.com/label/projects/label/cm7eniew000h5zz87966e5kv6

import Mathlib

/- Let $f(x) = a * x^2 + b * x + c$ where $a, b, c$ are integers.
Suppose that $f(1) = 0$, $50 < f(7) < 60$, $70 < f(8) < 80$,
and $5000 k < f(100) < 5000 (k + 1)$ for some integer $k$.
What is $k$?
(A) 1
(B) 2
(C) 3
(D) 4
(E) 5 -/

theorem algebra_94615 (a b c : ℤ) (f : ℤ → ℤ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c)
    (h1 : f 1 = 0) (h2 : f 7 ∈ Set.Ioo 50 60) (h3 : f 8 ∈ Set.Ioo 70 80)
    {k : ℤ} (h4 : f 100 ∈ Set.Ioo (5000 * k) (5000 * (k + 1))) :
    k = 3 := by
  simp only [hf, one_pow, mul_one, Int.reducePow] at h1 h2 h3
  -- If r * x ∈ (a, b), what are the conditions to obtain x = k?
  -- Require k - 1 < x < k + 1 and therefore r * (k - 1) < r * x < r * (k + 1).
  -- This can be obtained from r * (k - 1) ≤ a and b ≤ r * (k + 1).
  have h_eq_of_mem {r x a b k : ℤ} (h : r * x ∈ Set.Ioo a b) (hr : 0 < r)
      (ha : r * (k - 1) ≤ a) (hb : b ≤ r * (k + 1)) : x = k := by
    simp only [Set.mem_Ioo] at h
    suffices k - 1 < x ∧ x < k + 1 by
      symm
      refine Int.le_antisymm_iff.mpr ?_
      simpa [Int.sub_one_lt_iff, Int.lt_add_one_iff] using this
    refine ⟨?_, ?_⟩
    · exact Int.lt_of_mul_lt_mul_left (lt_of_le_of_lt ha h.1) hr.le
    · exact Int.lt_of_mul_lt_mul_left (lt_of_lt_of_le h.2 hb) hr.le
  -- Eliminate c from equations h2, h3.
  -- Obtain equation for c to use later.
  have hc : c = -(a + b) := by simpa [← eq_sub_iff_add_eq'] using h1
  have h1 (u v) : a * u + b * v + c = a * (u - 1) + b * (v - 1) := by rw [hc]; ring
  simp only [h1, Int.reduceSub] at h2 h3
  -- Factor common term and divide on both sides.
  have h2 : a * 8 + b = 9 := by
    have h2 : 6 * (a * 8 + b) ∈ Set.Ioo 50 60 := by convert h2 using 1; ring
    refine h_eq_of_mem h2 ?_ ?_ ?_ <;> norm_num
  -- Factor common term and divide on both sides.
  have h3 : a * 9 + b = 11 := by
    have h3 : 7 * (a * 9 + b) ∈ Set.Ioo 70 80 := by convert h3 using 1; ring
    refine h_eq_of_mem h3 ?_ ?_ ?_ <;> norm_num
  -- Consider h3 - h2 in order to eliminate b.
  have ha : a = 2 := by simpa [← mul_sub] using congrArg₂ (· - ·) h3 h2
  -- Obtain value of b and c.
  have hb : b = -7 := by simpa [ha, ← eq_sub_iff_add_eq'] using h2
  have hc : c = 5 := by simpa [ha, hb] using hc
  simp only [hf, ha, hb, hc, Int.reducePow, Int.reduceMul, Int.reduceNeg, Int.reduceAdd] at h4
  -- 5000 * k < 19305 < 5000 * (k + 1)
  -- k must be 3 since 15000 < 19305 < 20000.
  suffices 2 < k ∧ k < 4 by
    refine Int.eq_iff_le_and_ge.mpr ⟨?_, ?_⟩
    · exact Int.lt_add_one_iff.mp this.2
    · exact Int.sub_one_lt_iff.mp this.1
  rw [Set.mem_Ioo] at h4
  refine ⟨?_, ?_⟩
  · suffices 2 + 1 < k + 1 by simpa only [add_lt_add_iff_right] using this
    refine Int.lt_of_mul_lt_mul_left ?_ (a := 5000) (by norm_num : 0 ≤ (5000 : ℤ))
    refine lt_of_le_of_lt ?_ h4.2
    norm_cast
  · refine Int.lt_of_mul_lt_mul_left ?_ (a := 5000) (by norm_num : 0 ≤ (5000 : ℤ))
    refine lt_of_lt_of_le h4.1 ?_
    norm_num
