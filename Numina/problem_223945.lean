-- https://cloud.kili-technology.com/label/projects/review/cma3ygf29006kahay88o5hmwg

import Mathlib

/- Prove that for any natural $n \geqslant 2$ the number $2^{4 n+2} + 1$ is
not the product of two prime numbers. -/

theorem number_theory_223945 (n : ℕ) (hn : 2 ≤ n) :
    ¬∃ p q, 2 ^ (4 * n + 2) + 1 = p * q ∧ p.Prime ∧ q.Prime := by
  simp only [not_exists]
  intro p q ⟨hpq, hp, hq⟩

  suffices ∃ a b, a ≠ 1 ∧ b ≠ 1 ∧ a * b = p * q ∧ ∃ c d, c ≠ 1 ∧ d ≠ 1 ∧ c * d = p * q ∧
      ¬[a, b].Perm [c, d] by
    -- TODO: move to outer?
    suffices h_perm : ∀ u v, u ≠ 1 → v ≠ 1 → u * v = p * q → [u, v].Perm [p, q] by
      rcases this with ⟨a, b, ha, hb, hab, c, d, hc, hd, hcd, h⟩
      refine h ?_
      exact .trans (h_perm a b ha hb hab) (h_perm c d hc hd hcd).symm

    intro a b ha hb h
    have ⟨ha_zero, hb_zero⟩ : a ≠ 0 ∧ b ≠ 0 := by
      suffices a * b ≠ 0 by simpa using this
      suffices p ≠ 0 ∧ q ≠ 0 by simpa [h] using this
      exact ⟨hp.ne_zero, hq.ne_zero⟩
    replace ha : 1 < a := (Nat.two_le_iff a).mpr ⟨ha_zero, ha⟩
    replace hb : 1 < b := (Nat.two_le_iff b).mpr ⟨hb_zero, hb⟩

    have hab := Nat.perm_primeFactorsList_mul (Nat.not_eq_zero_of_lt ha) (Nat.not_eq_zero_of_lt hb)
    have hpq := Nat.perm_primeFactorsList_mul hp.ne_zero hq.ne_zero
    rw [Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hq] at hpq
    simp at hpq  -- Was there an easier way to get this?

    have : a.primeFactorsList.length + b.primeFactorsList.length = 2 := by
      calc _
      _ = (a * b).primeFactorsList.length := by simpa using hab.length_eq.symm
      _ = _ := by simpa [h] using hpq.length_eq

    have ha_len_pos : 0 < a.primeFactorsList.length := by
      refine List.length_pos.mpr ?_
      suffices a ≠ 0 ∧ a ≠ 1 by simpa using this
      exact (Nat.two_le_iff a).mp ha
    have hb_len_pos : 0 < b.primeFactorsList.length := by
      refine List.length_pos.mpr ?_
      suffices b ≠ 0 ∧ b ≠ 1 by simpa using this
      exact (Nat.two_le_iff b).mp hb
    -- have ha_len_lt : a.primeFactorsList.length < 2 := by linarith
    have ha_len : a.primeFactorsList.length = 1 := by linarith
    have hb_len : b.primeFactorsList.length = 1 := by linarith

    have h_prime_of_length_eq_one : ∀ x : ℕ, x.primeFactorsList.length = 1 → x.Prime := by
      intro n
      rw [List.length_eq_one, forall_exists_index]
      intro p hnp
      have hn : n ≠ 0 := by
        rintro rfl
        simp at hnp
      have hp : p.Prime := by
        suffices p ∈ n.primeFactorsList from Nat.prime_of_mem_primeFactorsList this
        simp [hnp]
      convert hp
      calc _
      _ = n.primeFactorsList.prod := (Nat.prod_primeFactorsList hn).symm
      _ = _ := by simp [hnp]

    have ha_prime : a.Prime := h_prime_of_length_eq_one a ha_len
    have hb_prime : b.Prime := h_prime_of_length_eq_one b hb_len

    have := Nat.primeFactorsList_unique (l := [a, b]) (n := p * q) (by simpa using h)
      (by simpa using ⟨ha_prime, hb_prime⟩)

    exact this.trans hpq

  let a : ℕ := 2 ^ (2 * n + 1) + 2 ^ (n + 1) + 1
  let b : ℕ := 2 ^ (2 * n + 1) - 2 ^ (n + 1) + 1
  have hab : a * b = 2 ^ (4 * n + 2) + 1 := by
    unfold a b
    -- Switch to `ℤ` to use `ring` without worrying about negatives.
    refine (Nat.cast_inj (R := ℤ)).mp ?_
    simp only [Nat.cast_mul, Nat.cast_add]
    rw [Nat.cast_sub]
    swap
    · refine Nat.pow_le_pow_right two_pos ?_
      linarith
    simp only [Nat.cast_pow]
    ring

  use a, b
  refine ⟨?_, ?_, hab.trans hpq, ?_⟩
  · unfold a
    simp
  · unfold b
    suffices 2 ^ (n + 1) < 2 ^ (2 * n + 1) by simpa [Nat.sub_eq_zero_iff_le] using this
    refine Nat.pow_lt_pow_of_lt one_lt_two ?_
    linarith

  -- Use the series `2^(4 n) - 2^(4 n - 2) + 2^(4 n - 4) - ... + 2^4 - 2^2 + 1`.
  -- Split the sum into positive and negative sums while working in `ℕ`.
  let c := 2 ^ 2 + 1
  let d := ∑ i in Finset.range (n + 1), 2 ^ (4 * i) - ∑ i in Finset.range n, 2 ^ (4 * i + 2)
  have hcd : c * d = 2 ^ (4 * n + 2) + 1 := by
    unfold c d
    calc _
    _ = 2 ^ 2 * ∑ i ∈ Finset.range (n + 1), 2 ^ (4 * i)
        + ∑ i ∈ Finset.range (n + 1), 2 ^ (4 * i)
        - 2 ^ 2 * ∑ i ∈ Finset.range n, 2 ^ (4 * i + 2)
        - ∑ i ∈ Finset.range n, 2 ^ (4 * i + 2) := by
      simp only [mul_tsub, add_mul]
      simp [Nat.sub_add_eq]

    _ = 4 * ∑ i ∈ Finset.range (n + 1), 2 ^ (4 * i)
        + ∑ i ∈ Finset.range (n + 1), 2 ^ (4 * i)
        - ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1))
        - 4 * ∑ i ∈ Finset.range n, 2 ^ (4 * i) := by
      simp only [Finset.mul_sum]
      congr
      · funext i
        ring
      · funext i
        ring

    _ = 4 * (2 ^ (4 * n) + ∑ i ∈ Finset.range n, 2 ^ (4 * i))
        + (1 + ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1)))
        - ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1))
        - 4 * ∑ i ∈ Finset.range n, 2 ^ (4 * i) := by
      congr
      · rw [Finset.sum_range_succ]
        ring
      · rw [Finset.sum_range_succ']
        ring

    _ = 4 * 2 ^ (4 * n) + 1 +
        4 * ∑ i ∈ Finset.range n, 2 ^ (4 * i)
        + ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1))
        - ∑ i ∈ Finset.range n, 2 ^ (4 * (i + 1))
        - 4 * ∑ i ∈ Finset.range n, 2 ^ (4 * i) := by
      congr 2
      ring

    _ = _ := by
      simp only [Nat.add_sub_cancel_right]
      ring

  use c, d
  refine ⟨?_, ?_, hcd.trans hpq, ?_⟩
  · norm_num
  · unfold d
    refine ne_of_gt ?_
    refine Nat.lt_sub_iff_add_lt'.mpr ?_
    rw [Finset.sum_range_succ']
    simp only [mul_zero, pow_zero, add_lt_add_iff_right]
    refine Finset.sum_lt_sum_of_nonempty ?_ ?_
    · suffices n ≠ 0 by simpa using this
      exact Nat.not_eq_zero_of_lt hn
    · intro i _
      refine Nat.pow_lt_pow_of_lt one_lt_two ?_
      simp [mul_add]

  suffices c ∉ [a, b] by
    refine mt (fun h_perm ↦ ?_) this
    refine h_perm.mem_iff.mpr ?_
    simp

  suffices c ≠ a ∧ c ≠ b by simpa using this
  refine ⟨?_, ?_⟩
  · refine ne_of_lt ?_
    calc _
    _ < 2 ^ (2 * 2 + 1) + 2 ^ (2 + 1) + 1 := by norm_num
    _ ≤ _ := by
      suffices Monotone (fun x ↦ 2 ^ (2 * x + 1) + 2 ^ (x + 1) + 1) from this hn
      refine .add_const (.add ?_ ?_) 1
      · refine fun x y hxy ↦ Nat.pow_le_pow_of_le one_lt_two ?_
        simpa using hxy
      · refine fun x y hxy ↦ Nat.pow_le_pow_of_le one_lt_two ?_
        simpa using hxy
  · refine ne_of_lt ?_
    calc _
    _ < 2 ^ (2 + 1) * (2 ^ 2 - 1) + 1 := by norm_num
    _ ≤ 2 ^ (n + 1) * (2 ^ n - 1) + 1 := by
      suffices Monotone (fun x ↦ 2 ^ (x + 1) * (2 ^ x - 1) + 1) from this hn
      refine .add_const (.mul' ?_ ?_) 1
      · refine fun x y hxy ↦ Nat.pow_le_pow_of_le one_lt_two ?_
        simpa using hxy
      · refine fun x y hxy ↦ Nat.sub_le_sub_right ?_ 1
        exact Nat.pow_le_pow_of_le one_lt_two hxy
    _ = _ := by
      rw [mul_tsub]
      congr 2 <;> ring
