-- https://cloud.kili-technology.com/label/projects/label/cm92t1t8l00384ev5q1rpmzxa

import Mathlib

/- Given that the sum of several positive integers is 2019.
Find the maximum value of their product. -/

theorem number_theory_152633 :
    IsGreatest (Multiset.prod '' {s | s.sum = 2019}) (3 ^ 673) := by
  -- It will suffice to show that the maximum product for any `n > 1` can be obtained
  -- using 2s and 3s, where there are at most two 2s.
  suffices ∀ n ≥ 2, ∃ a b, a < 3 ∧ 2 * a + 3 * b = n ∧
      IsGreatest (Multiset.prod '' {s | s.sum = n}) (2 ^ a * 3 ^ b) by
    specialize this 2019 (by norm_num)
    rcases this with ⟨a, b, ha, h_sum, h_prod⟩
    -- The desired result can be obtained by showing that `a = 0`.
    suffices ha : a = 0 by
      replace h_sum : 3 * b = 2019 := by simpa [ha] using h_sum
      have hb : b = 673 := (Nat.mul_right_inj three_ne_zero).mp h_sum
      rw [← hb]
      simpa [ha] using h_prod
    -- We can determine that `a = 0` since `3 ∣ 2019` and `a < 3`.
    refine Nat.eq_zero_of_dvd_of_lt ?_ ha
    refine Nat.dvd_of_mod_eq_zero ?_
    suffices 2 * a ≡ 2 * 0 [MOD 3] from Nat.ModEq.cancel_left_of_coprime (by norm_num) this
    suffices 2 * a % 3 = 0 by simpa using this
    have := congrArg (· % 3) h_sum
    simpa using this
  intro n hn

  -- Rephrase condition using Multiset.
  suffices ∃ s : Multiset ℕ, s.count 2 < 3 ∧ s.toFinset ⊆ {2, 3} ∧ s.sum = n ∧
      IsGreatest (Multiset.prod '' {s | s.sum = n}) s.prod by
    rcases this with ⟨s, hs_count, hs_elem, hs_sum, hs_prod⟩
    use s.count 2, s.count 3
    refine ⟨hs_count, ?_, ?_⟩
    · convert hs_sum
      rw [Finset.sum_multiset_count_of_subset _ _ hs_elem]
      simp [mul_comm (s.count _)]
    · convert hs_prod
      rw [Finset.prod_multiset_count_of_subset _ _ hs_elem]
      simp

  -- It suffices to prove the existence of an optimal set using {2, 3}, since
  -- the constraint that there are less than three 2s follows from `2^3 < 3^2`.
  suffices ∃ s : Multiset ℕ, s.toFinset ⊆ {2, 3} ∧ s.sum = n ∧
      IsGreatest (Multiset.prod '' {s | s.sum = n}) s.prod by
    refine this.imp fun s hs ↦ ⟨?_, hs⟩
    rcases hs with ⟨hs_elem, hs_sum, hs_max⟩
    replace hs_max : ∀ t : Multiset ℕ, t.sum = n → t.prod ≤ s.prod := by
      simpa [mem_upperBounds] using hs_max.2
    -- Show that if we have three 2s, we can obtain a greater product using 3s.
    contrapose hs_max with hs2
    suffices ∃ t : Multiset ℕ, t.sum = n ∧ s.prod < t.prod by simpa using this
    rw [not_lt] at hs2
    -- Obtain a set without three 2s removed.
    obtain ⟨t, rfl⟩ : ∃ t, s = t + Multiset.replicate 3 2 := by
      refine le_iff_exists_add'.mp ?_
      exact Multiset.le_count_iff_replicate_le.mp hs2
    -- Replace with two 3s.
    use t + Multiset.replicate 2 3
    refine ⟨?_, ?_⟩
    · convert hs_sum using 1
      simp only [Multiset.sum_add]
      simp
    · simp only [Multiset.prod_add]
      gcongr
      · refine Nat.zero_lt_of_ne_zero ?_
        suffices 0 ∉ t.toFinset by simpa using this
        suffices t.toFinset ⊆ {2, 3} from Finset.not_mem_mono this (by norm_num)
        refine .trans ?_ hs_elem
        simp
      -- `2 ^ 3 < 3 ^ 2`
      · simp only [Multiset.prod_replicate]
        norm_num

  -- Any 4 can be replaced with 2s: same sum, same product.
  suffices ∃ s : Multiset ℕ, s.toFinset ⊆ Finset.Icc 2 4 ∧ s.sum = n ∧
      IsGreatest (Multiset.prod '' {s | s.sum = n}) s.prod by
    rcases this with ⟨s, hs_elem, hs_sum, hs_prod⟩
    -- Replace each 4 with two 2s.
    use Multiset.replicate (s.count 2 + 2 * s.count 4) 2 + Multiset.replicate (s.count 3) 3
    refine ⟨?_, ?_⟩
    · rw [Multiset.toFinset_add]
      refine Finset.union_subset ?_ ?_
      · refine .trans (Multiset.toFinset_subset.mpr (Multiset.replicate_subset_singleton _ _)) ?_
        simp
      · refine .trans (Multiset.toFinset_subset.mpr (Multiset.replicate_subset_singleton _ _)) ?_
        simp
    refine ⟨?_, ?_⟩
    -- Prove that sums are equal.
    · convert hs_sum using 1
      calc _
      _ = (s.count 2 + 2 * s.count 4) * 2 + s.count 3 * 3 := by simp
      _ = s.count 2 * 2 + s.count 3 * 3 + s.count 4 * 4 := by ring
      _ = ∑ x ∈ {2, 3, 4}, s.count x * x := by simp [add_assoc]
      _ = _ := (Finset.sum_multiset_count_of_subset _ _ hs_elem).symm
    -- Prove that products are equal.
    · convert hs_prod using 1
      calc _
      _ = 2 ^ s.count 2 * 4 ^ s.count 4 * 3 ^ s.count 3 := by simp [pow_add, pow_mul]
      _ = 2 ^ s.count 2 * 3 ^ s.count 3 * 4 ^ s.count 4 := by ring
      _ = ∏ x ∈ {2, 3, 4}, x ^ s.count x := by simp [mul_assoc]
      _ = _ := (Finset.prod_multiset_count_of_subset _ _ hs_elem).symm

  -- Now it suffices to show that any solution must use only {2, 3, 4}
  -- (since it can be demonstrated that there does exist a maximal multiset).
  suffices ∀ s : Multiset ℕ, s.sum = n → IsGreatest (Multiset.prod '' {s | s.sum = n}) s.prod →
      s.toFinset ⊆ Finset.Icc 2 4 by
    suffices ∃ y, IsGreatest (Multiset.prod '' {s | s.sum = n}) y by
      rcases this with ⟨y, hy⟩
      obtain ⟨t, ⟨ht_sum, rfl⟩⟩ : ∃ s : Multiset ℕ, s.sum = n ∧ s.prod = y := by simpa using hy.1
      have h : ∀ s : Multiset ℕ, s.sum = n → s.prod ≤ t.prod := by
        simpa [mem_upperBounds] using hy.2
      use t
      exact ⟨this t ht_sum hy, ht_sum, hy⟩
    -- Establish existence of a maximal element since set is bounded and nonempty.
    refine BddAbove.exists_isGreatest_of_nonempty ?_ ?_
    · refine bddAbove_def.mpr ?_
      -- Use a trivial but finite bound.
      -- The multiset could be anything between n • {1} and 1 • {n}, hence n ^ n is a bound.
      use n ^ n
      suffices ∀ s : Multiset ℕ, s.sum = n → s.prod ≤ n ^ n by simpa using this
      intro s hs_sum
      -- Need to establish that there are no 0s in order to have at most n elements.
      by_cases hs_zero : 0 ∈ s
      · simp [Multiset.prod_eq_zero hs_zero]
      · calc _
        _ ≤ n ^ s.card := by
          refine Multiset.prod_le_pow_card s n fun x hx ↦ ?_
          refine le_of_le_of_eq ?_ hs_sum
          exact Multiset.le_sum_of_mem hx
        _ ≤ n ^ n := by
          suffices s.card ≤ n by
            refine Nat.pow_le_pow_right ?_ this
            exact Nat.zero_lt_of_lt hn
          suffices ∀ x ∈ s, 1 ≤ x by
            refine le_of_le_of_eq ?_ hs_sum
            simpa using Multiset.card_nsmul_le_sum this
          intro x hx
          refine Nat.one_le_iff_ne_zero.mpr ?_
          exact ne_of_mem_of_not_mem hx hs_zero
    · refine .image Multiset.prod ?_
      exact Set.nonempty_of_mem (by simp : {n} ∈ _)

  intro s hs_sum hs_max
  replace hs_max : ∀ t : Multiset ℕ, t.sum = n → t.prod ≤ s.prod := by
    simpa [mem_upperBounds] using hs_max.2

  -- First prove that none of the elements are zero.
  have h_zero : 0 ∉ s := by
    have : n ≤ s.prod := by simpa using hs_max {n} rfl
    refine mt (fun h ↦ ?_) (Nat.not_lt.mpr this)
    rw [Multiset.prod_eq_zero h]
    exact Nat.zero_lt_of_lt hn

  suffices ∀ x ∈ s, 2 ≤ x ∧ x ≤ 4 from fun x ↦ by simpa using this x
  refine fun x hx_mem ↦ ⟨?_, ?_⟩

  -- For `n > 1`, there cannot be a 1 in the set, since the product could be increased
  -- by adding 1 to another member of the set.
  · suffices x ≠ 1 by
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨?_, this⟩
      exact ne_of_mem_of_not_mem hx_mem h_zero
    suffices x = 1 → ∃ (t : Multiset ℕ), t.sum = n ∧ s.prod < t.prod by
      refine mt this ?_
      simpa using hs_max
    rintro rfl
    -- Obtain any another element of the multiset `s`.
    obtain ⟨y, hy⟩ : ∃ y, y ∈ s.erase 1 := by
      refine Multiset.exists_mem_of_ne_zero ?_
      suffices (s.erase 1).sum ≠ 0 from mt (fun h ↦ h ▸ Multiset.sum_zero) this
      rw [← Multiset.sum_erase hx_mem] at hs_sum
      linarith
    -- Combine with 1 to obtain a greater product.
    use (1 + y) ::ₘ (s.erase 1).erase y
    refine ⟨?_, ?_⟩
    · refine .trans ?_ hs_sum
      rw [Multiset.sum_cons, add_assoc, Multiset.sum_erase hy, Multiset.sum_erase hx_mem]
    · rw [Multiset.prod_cons, ← Multiset.prod_erase hx_mem, ← Multiset.prod_erase hy, ← mul_assoc]
      gcongr
      · -- Requires that product non-zero.
        refine Nat.pos_of_ne_zero ?_
        refine Multiset.prod_ne_zero ?_
        refine mt (fun h ↦ ?_) h_zero
        exact Multiset.mem_of_mem_erase <| Multiset.mem_of_mem_erase h
      · simp

  -- Finally, there cannot be a number greater than or equal to 5 in the set,
  -- since it could be split `x = 5 + a = 2 + (3 + a) < 2 * (3 + a) = 6 + 2 a`.
  · refine Nat.ge_of_not_lt ?_
    suffices 5 ≤ x → ∃ t : Multiset ℕ, t.sum = n ∧ s.prod < t.prod by
      refine mt this ?_
      simpa using hs_max
    intro hx
    obtain ⟨a, rfl⟩ : ∃ a, 5 + a = x := Nat.le.dest hx
    use {2, 3 + a} + s.erase (5 + a), ?_, ?_
    · rw [Multiset.sum_add, Multiset.sum_pair]
      calc _
      _ = 5 + a + (s.erase (5 + a)).sum := by ring
      _ = s.sum := Multiset.sum_erase hx_mem
      _ = n := hs_sum
    · rw [Multiset.prod_add, Multiset.prod_pair]
      rw [← Multiset.prod_erase hx_mem]
      gcongr
      -- Must establish that product is non-zero to have strict inequality.
      · refine Nat.pos_of_ne_zero ?_
        suffices 0 ∉ (s.erase (5 + a)) from Multiset.prod_ne_zero this
        exact Multiset.not_mem_mono (Multiset.erase_subset (5 + a) s) h_zero
      -- 5 + a < 6 + 2 a
      · linarith
