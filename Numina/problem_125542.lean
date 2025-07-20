-- https://cloud.kili-technology.com/label/projects/label/cmaktgyj8005qy1v5z9nm25ue

import Mathlib

/- The sum of the squares of two consecutive positive integers can be a square,
for example 3^2 + 4^2 = 5^2.
Show that the sum of the squares of 3 or 6 consecutive positive integers cannot be a square.
Give an example of the sum of the squares of 11 consecutive positive integers which is a square. -/

-- The range of `fun x ↦ x % n` on the naturals is the set with `x < n`.
lemma range_mod {n : ℕ} (hn : 0 < n) : Set.range (· % n) = Set.Iio n := by
  ext x
  simp only [Set.mem_range, Set.mem_Iio]
  constructor
  · exact fun ⟨y, hy⟩ ↦ hy ▸ Nat.mod_lt y hn
  · exact fun hx ↦ ⟨x, Nat.mod_eq_of_lt hx⟩

-- Useful lemma for finding the set of squares modulo a number.
lemma range_sq_mod_eq_image_finset {n : ℕ} (hn : 0 < n) :
    Set.range (· ^ 2 % n) = (Finset.range n).image (· ^ 2 % n) := by
  calc _
  _ = Set.range ((· ^ 2 % n) ∘ (· % n)) := by simp [Function.comp_def, Nat.pow_mod]
  _ = (· ^ 2 % n) '' Set.range (· % n) := Set.range_comp _ _
  _ = (Finset.range n).image (· ^ 2 % n) := by simp [range_mod hn]

-- The set of squares modulo 3 is {0, 1}.
lemma range_sq_mod_three : Set.range (· ^ 2 % 3) = ({0, 1} : Finset ℕ) := by
  rw [range_sq_mod_eq_image_finset three_pos]
  rfl

-- The set of squares modulo 4 is {0, 1}.
lemma range_sq_mod_four : Set.range (· ^ 2 % 4) = ({0, 1} : Finset ℕ) := by
  rw [range_sq_mod_eq_image_finset four_pos]
  rfl

-- Squares modulo 4 are either 0 (for even numbers) or 1 (for odd numbers).
lemma sq_mod_four (n : ℕ) : n ^ 2 % 4 = if 2 ∣ n then 0 else 1 := by
  by_cases hn : 2 ∣ n
  · obtain ⟨k, rfl⟩ := hn
    simp [mul_pow]
  · obtain ⟨k, rfl⟩ : Odd n := by simpa [Nat.odd_iff] using hn
    simp [add_sq, mul_pow, ← mul_assoc, Nat.add_mod]

theorem number_theory_125542 :
    (¬∃ n m, ∑ i ∈ Finset.range 3, (n + i) ^ 2 = m ^ 2) ∧
    (¬∃ n m, ∑ i ∈ Finset.range 6, (n + i) ^ 2 = m ^ 2) ∧
    ∑ i ∈ Finset.range 11, (18 + i) ^ 2 = 77^2 := by
  refine and_assoc.mp ⟨?_, by norm_num⟩
  -- Rewrite as an `or` to highlight shared structure and introduce `k`.
  suffices ∀ k, k = 3 ∨ k = 6 → ∀ n m, ∑ i ∈ Finset.range k, (n + i) ^ 2 ≠ m ^ 2 by
    simpa using this
  intro k hk
  cases hk with
  | inl hk =>
    intro n m
    -- Take modulo 3 of both sides.
    refine mt (congrArg (· % 3)) ?_
    -- Suffices to show that the sum does not belong to the set of squares modulo 3.
    suffices (∑ i ∈ Finset.range k, (n + i) ^ 2) % 3 ∉ Set.range (· ^ 2 % 3) by
      refine mt (fun h ↦ ?_) this
      exact h ▸ Set.mem_range_self m
    suffices (∑ i ∈ Finset.range k, (n + i) ^ 2) % 3 = 2 by simp [this, range_sq_mod_three]
    calc _
    -- Distribute the sum intro three terms.
    _ = (∑ i ∈ Finset.range k, (n ^ 2 + i * 2 * n + i ^ 2)) % 3 := by
      congr
      funext i
      ring
    _ = (k * n ^ 2 + k * (k - 1) * n + ∑ i ∈ Finset.range k, i ^ 2) % 3 := by
      simp [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_range_id_mul_two]
    -- Show that the first terms are congruent to 0 modulo 3.
    _ = (∑ i ∈ Finset.range k, i ^ 2) % 3 := by
      rw [Nat.add_mod]
      suffices (k * n ^ 2 + k * (k - 1) * n) % 3 = 0 by simp [this]
      simp only [hk, mul_assoc]
      simp
    -- Only the squares remain and 0 + 1 + 4 = 5 ≡ 2 [MOD 3].
    _ = _ := by
      rw [hk]
      norm_num
  | inr hk =>
    intro n m
    -- Take modulo 4 of both sides.
    refine mt (congrArg (· % 4)) ?_
    -- Suffices to show that the sum does not belong to the set of squares modulo 4.
    suffices (∑ i ∈ Finset.range k, (n + i) ^ 2) % 4 ∉ Set.range (· ^ 2 % 4) by
      refine mt (fun h ↦ ?_) this
      exact h ▸ Set.mem_range_self m
    -- Squares modulo 4 are 0 for an even number, 1 for an odd number.
    -- Therefore the sum of 6 consecutive numbers will be 3 mod 4, which is not a square mod 4.
    suffices (∑ i ∈ Finset.range k, (n + i) ^ 2) % 4 = 3 by simp [this, range_sq_mod_four]
    suffices (∑ i ∈ Finset.range k, (n + i) ^ 2 % 4) = 3 by simp [this, Finset.sum_nat_mod]
    calc _
    _ = (Finset.filter (fun i ↦ (n + i) % 2 = 1) (Finset.range k)).card := by
      simp [sq_mod_four, Finset.sum_ite]
    _ = (Finset.filter (fun i ↦ (n + i) ≡ 1 [MOD 2]) (Finset.range k)).card := rfl
    -- Switch to (difference of) `Nat.count` to use `Nat.count_modEq_card`.
    _ = Nat.count (fun i ↦ (n + i) ≡ 1 [MOD 2]) k := (Nat.count_eq_card_filter_range _ k).symm
    _ = Nat.count (· ≡ 1 [MOD 2]) (n + k) - Nat.count (· ≡ 1 [MOD 2]) n := by simp [Nat.count_add]
    _ = (n + 2 * 3) / 2 - n / 2 := by
      simp only [Nat.count_modEq_card _ two_pos]
      -- Cancel the equal remainder terms.
      simp [hk, Nat.add_mod, Nat.add_sub_add_right]
    _ = _ := by
      -- Take `6 / 2 = 3` out of division.
      rw [Nat.add_mul_div_left n 3 two_pos]
      -- Cancel equal terms.
      simp
