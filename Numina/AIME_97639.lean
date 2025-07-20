-- https://cloud.kili-technology.com/label/projects/label/cm7eni8oq007ezz87r6pdwqry
-- https://artofproblemsolving.com/wiki/index.php/2018_AIME_II_Problems/Problem_3

import Mathlib

/- Find the sum of all positive integers $b < 1000$ such that the base-$b$ integer $36_b$
is a perfect square and the base-$b$ integer $27_b$ is a perfect cube. -/

theorem number_theory_97639 :
    ∑ᶠ b ∈ {b : ℕ | 0 < b ∧ b < 1000 ∧ (∃ k, Nat.digits b (k ^ 2) = [6, 3]) ∧
      ∃ m, Nat.digits b (m ^ 3) = [7, 2]}, b = 371 := by
  -- Express the set of b's as a projection of a set of constrained triples.
  -- Since 7 is a digit, b must be greater than 7.
  have hs : {b : ℕ | 0 < b ∧ b < 1000 ∧
        (∃ k, Nat.digits b (k ^ 2) = [6, 3]) ∧ ∃ m, Nat.digits b (m ^ 3) = [7, 2]} =
      Prod.fst ''
        {(b, k, m) : ℕ × ℕ × ℕ | 7 < b ∧ b < 1000 ∧ k ^ 2 = 6 + b * 3 ∧ m ^ 3 = 7 + b * 2} :=
    calc _
    _ = Prod.fst '' {(b, k, m) : ℕ × ℕ × ℕ | 0 < b ∧ b < 1000 ∧
        Nat.digits b (k ^ 2) = [6, 3] ∧ Nat.digits b (m ^ 3) = [7, 2]} := by
      ext b
      simp
    -- Since 7 is a digit, b must be greater than 7.
    _ = Prod.fst '' {(b, k, m) : ℕ × ℕ × ℕ | 7 < b ∧ b < 1000 ∧
        Nat.digits b (k ^ 2) = [6, 3] ∧ Nat.digits b (m ^ 3) = [7, 2]} := by
      refine congrArg _ (Set.ext fun (b, k, m) ↦ ?_)
      simp only [Set.mem_setOf_eq, and_congr_left_iff, and_imp]
      intro hb_lt hk hm
      refine ⟨fun hb_gt ↦ ?_, fun hb_gt ↦ Nat.zero_lt_of_lt hb_gt⟩
      refine Nat.digits_lt_base (m := m ^ 3) ?_ (by simp [hm])
      -- Since the list of digits does not start with a 1, b ≠ 1.
      suffices b ≠ 1 from Nat.lt_of_le_of_ne hb_gt this.symm
      intro hb
      rw [hb, Nat.digits_one] at hm
      have {n a b : ℕ} {l : List ℕ} (h : a ≠ b) : List.replicate n a ≠ List.cons b l := by
        cases n with | zero => simp | succ n => simp [List.replicate_succ, h]
      exact this (by norm_num) hm
    -- Replace the digits constraints with an arithmetic expression.
    _ = Prod.fst '' {(b, k, m) : ℕ × ℕ × ℕ | 7 < b ∧ b < 1000 ∧
        k ^ 2 = 6 + b * 3 ∧ m ^ 3 = 7 + b * 2} := by
      refine congrArg _ (Set.ext fun (b, k, m) ↦ ?_)
      simp only [Set.mem_setOf_eq, and_congr_right_iff]
      refine fun hb_gt _ ↦ ?_
      have h_digits_two {x₀ x₁ n} (hx₀ : x₀ < b) (hx₁ : x₁ < b) (hx₁_ne : x₁ ≠ 0) :
          b.digits n = [x₀, x₁] ↔ n = x₀ + b * x₁ := by
        refine ⟨fun hk ↦ ?_, fun hk ↦ ?_⟩
        · rw [← Nat.ofDigits_digits b n, hk]
          rfl
        · rw [hk, Nat.digits_add _ (lt_trans (by norm_num) hb_gt) _ _ hx₀ (.inr hx₁_ne),
            Nat.digits_of_lt _ _ hx₁_ne hx₁]
      refine and_congr ?_ ?_
      · rw [h_digits_two] <;> linarith
      · rw [h_digits_two] <;> linarith

  -- Consider the powers of three since there will be fewer of those.
  -- Establish the range of m's and look for other constraints.
  -- Since `8 ≤ b < 1000`, we have `23 ≤ m ^ 3 < 2007` and therefore `3 ≤ m ≤ 12`.
  -- Since `m ^ 3 = 7 + b * 2`, we know that `m ^ 3` (and hence `m`) is odd.
  -- Since `6 + b * 3 = 3 (2 + b) = k ^ 2`, we have `9 ∣ k`, `3 ∣ b + 2`,
  -- which gives `3 ∣ 2 * (b + 2) + 3 = 2 * b + 7 = m ^ 3`, and thus `3 ∣ m`.
  -- Putting these together leaves only 2 candidate triples, `m = 3` or `m = 9`.
  have h_le : {(b, k, m) : ℕ × ℕ × ℕ | 7 < b ∧ b < 1000 ∧ k ^ 2 = 6 + b * 3 ∧ m ^ 3 = 7 + b * 2} ⊆
      Finset.toSet {(10, 6, 3), (361, 33, 9)} :=
    calc _
    -- Replace the bounds on `b` with bounds on `m`.
    -- Parameterize `b` and `k` in terms of `m` in order to later use `Finset.filter`.
    _ ⊆ {(b, k, m) : ℕ × ℕ × ℕ | 2 < m ∧ m < 13 ∧ Odd m ∧ 3 ∣ m ∧
        Nat.sqrt (6 + b * 3) = k ∧ (m ^ 3 - 7) / 2 = b} := by
      refine fun (b, k, m) ⟨hb_gt, hb_lt, hk, hm⟩ ↦ ?_
      have h_mono : StrictMono (fun b ↦ 7 + b * 2) := fun _ _ h ↦ by simp [h]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine lt_of_pow_lt_pow_left₀ 3 (by norm_num) ?_
        rw [hm]
        exact lt_trans (by norm_num) (h_mono hb_gt)
      · refine lt_of_pow_lt_pow_left₀ 3 (by norm_num) ?_
        rw [hm]
        exact lt_trans (h_mono hb_lt) (by norm_num)
      · suffices Odd (m ^ 3) from Nat.Odd.of_mul_right this
        rw [hm, Nat.odd_add, Nat.odd_iff]
        simp
      · -- Since `3 ∣ k ^ 2`, we have `3 ∣ k`, and therefore `3 ^ 2 ∣ k ^ 2 = (2 + b) * 3`.
        -- This gives `3 ∣ 2 + b`, and therefore `3 ∣ 3 + (2 + b) * 2 = m ^ 3`.
        replace hk : k ^ 2 = (2 + b) * 3 := by rw [hk]; ring
        replace hm : m ^ 3 = 3 + (2 + b) * 2 := by rw [hm]; ring
        suffices 3 ∣ m ^ 3 from Nat.prime_three.dvd_of_dvd_pow this
        rw [hm]
        refine dvd_add dvd_rfl ?_
        rw [Nat.Coprime.dvd_mul_right rfl]
        suffices 3 * 3 ∣ (2 + b) * 3 from (Nat.mul_dvd_mul_iff_right three_pos).mp this
        rw [← hk, ← pow_two]
        rw [Nat.pow_dvd_pow_iff two_ne_zero]
        suffices 3 ∣ k ^ 2 from Nat.prime_three.dvd_of_dvd_pow this
        rw [hk]
        exact dvd_mul_left _ _
      · rw [← hk, Nat.sqrt_eq' k]
      · simp [hm]
    -- Re-write as the image of a set of `m` under the function `m ↦ (b, k, m)`.
    _ ⊆ ((fun bm ↦ (bm.1, Nat.sqrt (6 + bm.1 * 3), bm.2)) ∘ fun m ↦ ((m ^ 3 - 7) / 2, m)) ''
        {m : ℕ | 2 < m ∧ m < 13 ∧ Odd m ∧ 3 ∣ m} := by
      refine fun (b, k, m) ↦ ?_
      simp only [Set.mem_setOf_eq, Function.comp_apply, Set.mem_image, Prod.mk.injEq]
      simp only [← and_assoc, exists_eq_right]
      exact fun ⟨⟨h, hk⟩, hb⟩ ↦ ⟨⟨h, hb⟩, hb ▸ hk⟩
    -- Write as the image of a Finset under the same function.
    _ = Finset.image
        ((fun bm ↦ (bm.1, Nat.sqrt (6 + bm.1 * 3), bm.2)) ∘ fun m ↦ ((m ^ 3 - 7) / 2, m))
        ((Finset.Ioo 2 13).filter fun m ↦ Odd m ∧ 3 ∣ m) := by
      simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_Ioo, and_assoc]
    -- There are only two values of `m` that satisfy the constraints.
    _ = Finset.image
        ((fun bm ↦ (bm.1, Nat.sqrt (6 + bm.1 * 3), bm.2)) ∘ fun m ↦ ((m ^ 3 - 7) / 2, m)) {3, 9} :=
      rfl
    _ = _ := by norm_num

  -- In the other direction, show that both triples satisfy all constraints.
  have h_ge : Finset.toSet {(10, 6, 3), (361, 33, 9)} ⊆
      {(b, k, m) : ℕ × ℕ × ℕ | 7 < b ∧ b < 1000 ∧ k ^ 2 = 6 + b * 3 ∧ m ^ 3 = 7 + b * 2} := by
    rw [Set.subset_def]
    simp

  rw [hs, h_le.antisymm h_ge]
  rw [← Finset.coe_image, finsum_mem_coe_finset]
  simp
