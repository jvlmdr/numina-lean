-- https://cloud.kili-technology.com/label/projects/label/cmcbovi8e00u6ueaxfcah8cdr

import Mathlib

open scoped Finset

/- $A = \{a, b, c\}$ is a set containing three positive integers. Prove that we can find a set
$B = \{x, y\} \subset A$ such that for all odd positive integers $m, n$ we have
$$
10 \mid x^{m} y^{n} - x^{n} y^{m}
$$
-/

lemma exists_subset_asdf  -- TODO
    (a : Finset ℕ) (ha_pos : ∀ x ∈ a, 0 < x) (ha_card : #a = 3) :
    ∃ x y, x ≠ y ∧ {x, y} ⊆ a ∧
      (5 ∣ x ∨ x ≡ y [MOD 5] ∨ 5 ∣ y + x) := by
  cases Decidable.em (∃ x ∈ a, 5 ∣ x) with
  | inl h_zero =>
    rcases h_zero with ⟨x, hx⟩
    -- How to get a second element?
    sorry
  | inr h_zero =>
    simp only [not_exists, not_and] at h_zero
    replace h_zero (x) (hx : x ∈ a) : x % 5 ≠ 0 := (mt Nat.dvd_of_mod_eq_zero) (h_zero x hx)
    sorry

lemma sub_mul_sum_range_eq_pow_sub_pow (x y : ℤ) (k : ℕ) :
    (y - x) * ∑ i in Finset.range k, x ^ i * y ^ (k - (i + 1)) = y ^ k - x ^ k := by
  rw [Finset.mul_sum]
  calc _
  _ = ∑ i in Finset.range k, (x ^ i * y ^ (k - (i + 1) + 1) - x ^ (i + 1) * y ^ (k - (i + 1))) := by
    congr
    funext i
    ring
  _ = ∑ i in Finset.range k, (x ^ i * y ^ (k - i) - x ^ (i + 1) * y ^ (k - (i + 1))) := by
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
  obtain ⟨x, y, h_ne, h_subset, hxy⟩ := exists_subset_asdf a ha_pos ha_card
  refine ⟨x, y, h_ne, h_subset, ?_⟩
  intro m n hm hn

  wlog hmn : m < n generalizing m n
  · simp only [not_lt] at hmn
    cases Nat.eq_or_lt_of_le hmn with
    | inl hmn =>
      -- When `m = n`, the terms cancel and we have the trivial `10 ∣ 0`.
      simp [hmn]
    | inr hmn =>
      -- When `n < m`, swap `m` and `n` using symmetry.
      rw [← Int.dvd_neg]
      simpa using this n m hn hm hmn

  -- Replace `x ^ n` with `x ^ m * x ^ (n - m)` and factor out `(x * y) ^ m`.
  suffices (10 : ℤ) ∣ x ^ m * y ^ m * (y ^ (n - m) - x ^ (n - m)) by
    have hn_add_eq : n - m + m = n := Nat.sub_add_cancel hmn.le
    rw [← hn_add_eq]
    convert this using 1
    ring

  have h_even_sub : Even (n - m) := Nat.Odd.sub_odd hn hm
  obtain ⟨k, hk⟩ : ∃ k, n - m = 2 * k := h_even_sub.exists_two_nsmul _
  simp only [hk, pow_mul]
  rw [← sub_mul_sum_range_eq_pow_sub_pow, sq_sub_sq]
  generalize (∑ i ∈ Finset.range k, (x ^ 2) ^ i * (y ^ 2) ^ (k - (i + 1)) : ℤ) = c
  suffices (2 * 5 : ℤ) ∣ ↑(x ^ m * y ^ m * (y + x)) * (y - x) * c by
    convert this using 1
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add]
    ring
  -- TODO: eliminate `c` earlier?
  refine IsCoprime.mul_dvd (by norm_num) ?_ ?_
  · -- Either `x` is even, `y` is even, or both are odd.
    refine dvd_mul_of_dvd_left ?_ _
    refine dvd_mul_of_dvd_left ?_ _
    refine Int.ofNat_dvd.mpr ?_
    cases Nat.even_or_odd x with
    | inl hx =>
      refine dvd_mul_of_dvd_left ?_ _
      refine dvd_mul_of_dvd_left ?_ _
      exact dvd_pow (even_iff_two_dvd.mp hx) (Nat.ne_of_odd_add hm)
    | inr hx =>
      cases Nat.even_or_odd y with
      | inl hy =>
        refine dvd_mul_of_dvd_left ?_ _
        refine dvd_mul_of_dvd_right ?_ _
        exact dvd_pow (even_iff_two_dvd.mp hy) (Nat.ne_of_odd_add hm)
      | inr hy =>
        -- If both are odd, then `x + y` is even.
        refine dvd_mul_of_dvd_right ?_ _
        exact even_iff_two_dvd.mp (hy.add_odd hx)
  · cases hxy with
    | inl hxy =>
      -- TODO: avoid this ridiculous situation
      refine dvd_mul_of_dvd_left ?_ _
      refine dvd_mul_of_dvd_left ?_ _
      refine Int.ofNat_dvd.mpr ?_
      refine dvd_mul_of_dvd_left ?_ _
      refine dvd_mul_of_dvd_left ?_ _
      exact dvd_pow hxy (Nat.ne_of_odd_add hm)
    | inr hxy =>
      cases hxy with
      | inl hxy =>
        replace hxy : 5 ∣ (y - x : ℤ) := by simpa [Nat.modEq_iff_dvd] using hxy
        simp [dvd_mul_of_dvd_left, dvd_mul_of_dvd_right, hxy]
      | inr hxy =>
        -- have hxy : (5 : ℤ) ∣ y + x := by simpa using Int.ofNat_dvd_right.mpr hxy
        -- simp [dvd_mul_of_dvd_left, dvd_mul_of_dvd_right, hxy]
        refine dvd_mul_of_dvd_left ?_ _
        refine dvd_mul_of_dvd_left ?_ _
        refine Int.ofNat_dvd.mpr ?_
        exact dvd_mul_of_dvd_right hxy _
