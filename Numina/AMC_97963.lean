-- https://cloud.kili-technology.com/label/projects/label/cm7enii3p00mzzz87lxyv2jc1
-- https://artofproblemsolving.com/wiki/index.php/2018_AMC_12A_Problems/Problem_19

import Mathlib

/- Let A be the set of positive integers that have no prime factors other than 2, 3, or 5.
The infinite sum
1/1 + 1/2 + 1/3 + 1/4 + 1/5 + 1/6 + 1/8 + 1/9 + 1/10 + 1/12 + 1/15 + 1/16 + 1/18 + 1/20 + ⋯
of the reciprocals of the elements of A can be expressed as m / n,
where m and n are relatively prime positive integers. What is m + n?
(A) 16
(B) 17
(C) 19
(D) 23
(E) 36 -/

theorem number_theory_97963 : ∃ m n : ℕ,
    ∑' k : Nat.factoredNumbers {2, 3, 5}, (k : ℝ)⁻¹ = m / n ∧
    Nat.Coprime m n ∧ m + n = 19 := by
  use 15, 4
  refine ⟨?_, by norm_num, by norm_num⟩
  simp only [Nat.cast_ofNat]
  refine HasSum.tsum_eq ?_

  -- The set of factored numbers can be parameterized
  -- `{2 ^ a * 3 ^ b * 5 ^ c | a b c : ℕ}`
  -- The sum can be rewritten as a product of sums.
  -- `∑ a, ∑ b, ∑ c, (2 ^ a * 3 ^ b * 5 ^ c)⁻¹`
  -- `(∑ a, (2 ^ a)⁻¹) * (∑ b, (3 ^ b)⁻¹) * (∑ c, (5 ^ c)⁻¹)`
  -- Each of these is a geometric sum.
  -- `1 / (1 - 2⁻¹) * 1 / (1 - 3⁻¹) * 1 / (1 - 5⁻¹)`
  -- `2 * 3 / 2 * 5 / 4`
  -- `15 / 4`
  -- We will use `Nat.equivProdNatFactoredNumbers`, an equivalence between
  -- `factoredNumbers (insert p s)` and `ℕ × factoredNumbers s`,
  -- to factor each element out of the sum.

  -- Establish the sums of each of the geometric series.
  have hs2 : HasSum (fun a : ℕ ↦ (2 ^ a : ℝ)⁻¹) 2 := by
    convert hasSum_geometric_of_abs_lt_one (r := 2⁻¹) ?_ using 1
    · simp
    · norm_num
    · rw [abs_of_nonneg] <;> norm_num
  have hs3 : HasSum (fun a : ℕ ↦ (3 ^ a : ℝ)⁻¹) (3 / 2) := by
    convert hasSum_geometric_of_abs_lt_one (r := 3⁻¹) ?_ using 1
    · simp
    · norm_num
    · rw [abs_of_nonneg] <;> norm_num
  have hs5 : HasSum (fun a : ℕ ↦ (5 ^ a : ℝ)⁻¹) (5 / 4) := by
    convert hasSum_geometric_of_abs_lt_one (r := 5⁻¹) ?_ using 1
    · simp
    · norm_num
    · rw [abs_of_nonneg] <;> norm_num

  -- Factor out the powers of 2.
  suffices HasSum (fun k : Nat.factoredNumbers {2, 3, 5} ↦ (k : ℝ)⁻¹) (2 * (15 / 8)) by
    convert this using 1
    norm_num
  rw [← Equiv.hasSum_iff (Nat.equivProdNatFactoredNumbers Nat.prime_two (by simp))]
  simp only [Function.comp_def, Nat.equivProdNatFactoredNumbers_apply',
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_inv]
  suffices HasSum (fun k : Nat.factoredNumbers {3, 5} ↦ (k : ℝ)⁻¹) (15 / 8) by
    have := HasSum.mul hs2 this (by
      have := hs2.summable.mul_of_nonneg this.summable (fun _ ↦ by simp) fun _ ↦ by simp
      exact this)
    exact this
  -- Factor out the powers of 3.
  suffices HasSum (fun k : Nat.factoredNumbers {3, 5} ↦ (k : ℝ)⁻¹) (3 / 2 * (5 / 4)) by
    convert this using 1
    norm_num
  rw [← Equiv.hasSum_iff (Nat.equivProdNatFactoredNumbers Nat.prime_three (by simp))]
  simp only [Function.comp_def, Nat.equivProdNatFactoredNumbers_apply',
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_inv]
  suffices HasSum (fun k : Nat.factoredNumbers {5} ↦ (k : ℝ)⁻¹) (5 / 4) by
    have := HasSum.mul hs3 this (by
      have := hs3.summable.mul_of_nonneg this.summable (fun _ ↦ by simp) fun _ ↦ by simp
      exact this)
    exact this
  -- Factor out the powers of 5.
  suffices HasSum (fun k : Nat.factoredNumbers {5} ↦ (k : ℝ)⁻¹) (5 / 4 * 1) by
    simpa using this
  rw [← Equiv.hasSum_iff (Nat.equivProdNatFactoredNumbers Nat.prime_five (Finset.not_mem_empty 5))]
  simp only [Function.comp_def, Nat.equivProdNatFactoredNumbers_apply',
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_inv]
  suffices HasSum (fun k : Nat.factoredNumbers {} ↦ (k : ℝ)⁻¹) 1 by
    have := HasSum.mul hs5 this (by
      have := hs5.summable.mul_of_nonneg this.summable (fun _ ↦ by simp) fun _ ↦ by simp
      exact this)
    exact this
  -- Finally, deal with the set {1}.
  rw [Nat.factoredNumbers_empty]
  simpa using hasSum_singleton 1 fun x : ℕ ↦ (x : ℝ)⁻¹
