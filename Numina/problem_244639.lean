-- https://cloud.kili-technology.com/label/projects/label/cmcbovi8e00u6ueaxfcah8cdr

import Mathlib

open scoped Finset

/- $A = \{a, b, c\}$ is a set containing three positive integers. Prove that we can find a set
$B = \{x, y\} \subset A$ such that for all odd positive integers $m, n$ we have
$$
10 \mid x^{m} y^{n} - x^{n} y^{m}
$$
-/

-- Any size-3 subset of {1, 2, 3, 4} must contain a pair of elements with sum 5.
lemma exists_subset_card_two_sum_five (s : Finset ℕ) (hs_card : #s = 3) (hs : s ⊆ {1, 2, 3, 4}) :
    ∃ a ⊆ s, #a = 2 ∧ ∑ i ∈ a, i = 5 := by
  -- Since we only exclude one element from `{1, 2, 3, 4}` to obtain `s`,
  -- it must contain either `{1, 4}` or `{2, 3}`.
  suffices {2, 3} ⊆ s ∨ {1, 4} ⊆ s by
    refine this.elim ?_ ?_
    · exact fun h ↦ ⟨_, h, rfl, rfl⟩
    · exact fun h ↦ ⟨_, h, rfl, rfl⟩
  -- Partition {1, 2, 3, 4} into {1, 4} and {2, 3}.
  have h_part : ({1, 2, 3, 4} : Finset ℕ) = {2, 3} ∪ {1, 4} := by ext; simp
  -- Observe that the difference contains exactly one element.
  have h_diff : #({1, 2, 3, 4} \ s) = 1 := by simp [Finset.card_sdiff hs, hs_card]
  -- Distribute the difference over the (disjoint) union.
  rw [h_part, Finset.union_sdiff_distrib] at h_diff
  rw [Finset.card_union_of_disjoint] at h_diff
  swap
  · refine .disjoint_sdiff_left ?_
    refine .disjoint_sdiff_right ?_
    simp
  -- Since the two cardinalities add to 1, one of them will be 0.
  rw [Nat.add_eq_one_iff] at h_diff
  refine h_diff.imp ?_ ?_
  · exact fun ⟨h, _⟩ ↦ by simpa using h
  · exact fun ⟨_, h⟩ ↦ by simpa using h

-- In any set of 3 natural numbers, there must exist a pair (x, y) that satisfies one of:
-- 1. x ≡ 0 [MOD 5], or
-- 2. x ≡ y [MOD 5], or
-- 3. x + y ≡ 0 [MOD 5].
lemma exists_pair_modEq_zero_or_modEq_or_add_modEq_zero (a : Finset ℕ) (ha_card : #a = 3) :
    ∃ x ∈ a, ∃ y ∈ a, x ≠ y ∧ (x ≡ 0 [MOD 5] ∨ x ≡ y [MOD 5] ∨ x + y ≡ 0 [MOD 5]) := by
  cases exists_or_forall_not (fun x ↦ x ∈ a ∧ x % 5 = 0) with
  | inl h_zero =>
    obtain ⟨x, hxa, hx⟩ := h_zero
    -- Obtain an arbitrary second element.
    obtain ⟨y, hya, hyx⟩ := a.exists_mem_ne (by simp [ha_card]) x
    exact ⟨x, hxa, y, hya, hyx.symm, .inl hx⟩
  | inr h_zero =>
    simp only [not_and] at h_zero
    -- If there exist two elements with the same residue, take these.
    -- Otherwise, we have three distinct residues in {1, 2, 3, 4}.
    -- These three elements must contain either (1, 4) or (2, 3) as a pair.
    by_cases h_nodup : (a.val.map (· % 5)).Nodup
    · -- Use injectivity to obtain the pair of elements whose residues [MOD 5] add to 5.
      have h_inj : Set.InjOn (· % 5) a := by simpa using Multiset.inj_on_of_nodup_map h_nodup
      have := exists_subset_card_two_sum_five (a.image (· % 5))
        (by simpa [Finset.card_image_of_injOn h_inj])
        (by
          intro u hu
          suffices u ≠ 0 ∧ u < 5 by
            rcases this with ⟨h_zero, h_five⟩
            rw [Nat.ne_zero_iff_zero_lt] at h_zero
            interval_cases u <;> simp
          rw [Finset.mem_image] at hu
          rcases hu with ⟨x, hx, rfl⟩
          -- Use the fact that there is no `x ≡ 0 [MOD 5]` in `a`.
          exact ⟨h_zero x hx, Nat.mod_lt x (by norm_num)⟩)
      rcases this with ⟨t, ht_elem, ht_card, ht_sum⟩
      -- Replace `t` with `s.image (· % 5)`.
      rw [Finset.subset_image_iff] at ht_elem
      rcases ht_elem with ⟨s, hsa, rfl⟩
      rw [Finset.card_image_of_injOn (h_inj.mono hsa)] at ht_card
      rw [Finset.sum_image (h_inj.mono hsa)] at ht_sum
      -- Replace `s` with `{x, y}` where `x ≠ y`.
      rw [Finset.card_eq_two] at ht_card
      rcases ht_card with ⟨x, y, hxy, rfl⟩
      have ⟨hxa, hya⟩ : x ∈ a ∧ y ∈ a := by simpa [Finset.subset_iff] using hsa
      refine ⟨x, hxa, y, hya, hxy, .inr (.inr ?_)⟩
      rw [Finset.sum_pair hxy] at ht_sum
      simpa using congrArg (fun n : ℕ ↦ n % 5) ht_sum
    · -- If there *are* duplicate residues (not Nodup), then select these.
      rw [Multiset.nodup_map_iff_inj_on a.nodup] at h_nodup
      simp only [Finset.mem_val, not_forall, exists_prop] at h_nodup
      rcases h_nodup with ⟨x, hx, y, hy, hxy_mod, hxy⟩
      exact ⟨x, hx, y, hy, hxy, .inr (.inl hxy_mod)⟩

-- The difference of powers `y ^ k - x ^ k` factors into `y - x` and a sum.
lemma pow_sub_pow_eq_sub_mul_sum_range (x y : ℤ) (k : ℕ) :
    y ^ k - x ^ k = (y - x) * ∑ i ∈ Finset.range k, x ^ i * y ^ (k - (i + 1)) := by
  rw [Finset.mul_sum]
  symm
  calc _
  _ = ∑ i ∈ Finset.range k, (x ^ i * y ^ (k - (i + 1) + 1) - x ^ (i + 1) * y ^ (k - (i + 1))) := by
    congr
    funext i
    ring
  _ = ∑ i ∈ Finset.range k, (x ^ i * y ^ (k - i) - x ^ (i + 1) * y ^ (k - (i + 1))) := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [Finset.mem_range] at hi
    congr
    calc _
    _ = k + 1 - (i + 1) := (Nat.sub_add_comm hi).symm
    _ = _ := Nat.add_sub_add_right k 1 i
  _ = _ := by
    rw [Finset.sum_range_sub']
    simp

theorem number_theory_244639
    (a : Finset ℕ) (ha_pos : ∀ x ∈ a, 0 < x) (ha_card : #a = 3) :
    ∃ x y, x ≠ y ∧ {x, y} ⊆ a ∧ ∀ m n, Odd m → Odd n → (10 : ℤ) ∣ x^m * y^n - x^n * y^m := by
  -- Obtain and use a pair `{x, y} ⊆ a` that satisfies one of the three conditions.
  obtain ⟨x, hx, y, hy, hxy, h_mod⟩ :=
    exists_pair_modEq_zero_or_modEq_or_add_modEq_zero a ha_card
  refine ⟨x, y, hxy, ?_, ?_⟩
  · exact Finset.insert_subset hx (by simpa using hy)

  intro m n hm hn
  -- Due to symmetry, we can assume `m ≤ n`.
  -- Furthermore, when `m = n`, the terms cancel and we have the trivial `10 ∣ 0`.
  wlog hmn : m < n generalizing m n
  · simp only [not_lt] at hmn
    cases Nat.eq_or_lt_of_le hmn with
    | inl hmn => simp [hmn]
    | inr hmn =>
      rw [← Int.dvd_neg]
      simpa using this n m hn hm hmn

  -- Replace `x ^ n` with `x ^ m * x ^ (n - m)` and factor out `(x * y) ^ m`.
  suffices (10 : ℤ) ∣ x ^ m * y ^ m * (y ^ (n - m) - x ^ (n - m)) by
    have hn_add_eq : n - m + m = n := Nat.sub_add_cancel hmn.le
    rw [← hn_add_eq]
    convert this using 1
    ring

  -- Before factoring `y - x` from `y ^ (n - m) - x ^ (n - m)`, note that `y - x` is even.
  -- Therefore we can factor `y ^ 2 - x ^ 2` from the expression.
  obtain ⟨k, hk⟩ : ∃ k, n - m = 2 * k := Even.exists_two_nsmul (n - m) (Nat.Odd.sub_odd hn hm)
  simp only [hk, pow_mul]
  rw [pow_sub_pow_eq_sub_mul_sum_range, sq_sub_sq]
  -- Disregard the sum for the purpose of proving divisibility.
  -- At the same time, split 10 into 2 * 5 (coprime factors).
  -- It will suffices to show divisibility by each separately.
  suffices 2 * 5 ∣ x ^ m * y ^ m * (y + x) * (y - x : ℤ) by
    simpa [mul_assoc] using Dvd.dvd.mul_right this _
  -- For the purpose of divisibility, we will need the fact that `m ≠ 0`.
  have hm_zero : m ≠ 0 := Nat.ne_of_odd_add hm
  refine IsCoprime.mul_dvd (by norm_num) ?_ ?_
  · -- Either `x` is even, `y` is even, or their sum is even.
    refine dvd_mul_of_dvd_left ?_ _
    -- Switch to `ℕ` since we do not consider the difference.
    suffices 2 ∣ x ^ m * y ^ m * (y + x) by simpa using Int.ofNat_dvd.mpr this
    cases Nat.even_or_odd x with
    | inl hx =>
      refine dvd_mul_of_dvd_left ?_ _
      refine dvd_mul_of_dvd_left ?_ _
      exact dvd_pow (even_iff_two_dvd.mp hx) hm_zero
    | inr hx =>
      cases Nat.even_or_odd y with
      | inl hy =>
        refine dvd_mul_of_dvd_left ?_ _
        refine dvd_mul_of_dvd_right ?_ _
        exact dvd_pow (even_iff_two_dvd.mp hy) hm_zero
      | inr hy =>
        -- If both are odd, then `x + y` is even.
        refine dvd_mul_of_dvd_right ?_ _
        exact even_iff_two_dvd.mp (hy.add_odd hx)
  · -- Use the three possible conditions on `(x, y)`.
    -- Switch to `ℕ` where we can to simplify result.
    suffices 5 ∣ ↑(x ^ m * y ^ m * (y + x)) * (y - x : ℤ) by simpa
    cases h_mod with
    | inl h_mod =>
      refine dvd_mul_of_dvd_left ?_ _
      refine Int.ofNat_dvd.mpr ?_
      refine dvd_mul_of_dvd_left ?_ _
      refine dvd_mul_of_dvd_left ?_ _
      exact (Nat.dvd_of_mod_eq_zero h_mod).pow hm_zero
    | inr h_mod =>
      cases h_mod with
      | inl h_mod =>
        refine dvd_mul_of_dvd_right ?_ _
        exact Nat.modEq_iff_dvd.mp h_mod
      | inr h_mod =>
        refine dvd_mul_of_dvd_left ?_ _
        refine Int.ofNat_dvd.mpr ?_
        refine dvd_mul_of_dvd_right ?_ _
        simpa [add_comm] using Nat.dvd_of_mod_eq_zero h_mod
