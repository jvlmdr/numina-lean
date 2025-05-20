-- https://cloud.kili-technology.com/label/projects/label/cma3ygf29005qahayb0oyqqtm

import Mathlib

open scoped Finset

/- If a positive integer $n$ makes the equation $x^3 + y^3 = z^n$ have positive integer solutions
$(x, y, z)$, then $n$ is called a "good number". Then, the number of good numbers not exceeding
2019 is? -/

def isGood (n : ℕ) := ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^3 + y^3 = z^n

-- If `n` is a good number, then `n + 3` is also a good number.
-- We have `z^n = x^3 + y^3` for some `x, y, z`.
-- Then we see that `z^(n + 3) = z^n z^3 = (x^3 + y^3) z^3 = (x z)^3 + (y x)^3`.
lemma isGood_add_three (n : ℕ) : isGood n → isGood (n + 3) := by
  unfold isGood
  rintro ⟨x, y, z, hx, hy, hz, h⟩
  use x * z, y * z, z, mul_pos hx hz, mul_pos hy hz, hz
  convert congrArg (· * z ^ 3) h using 1 <;> ring

-- 1 is good since `a^3 + b^3 = (a^3 + b^3)^1` or e.g. `1^3 + 1^3 = 2^1`
lemma isGood_one : isGood 1 := by
  use 1, 1, 2
  simp

-- 2 is good since e.g. `1^3 + 2^3 = 9 = 3^2` or `2^3 + 2^3 = 16 = 4^2`
lemma isGood_two : isGood 2 := by
  use 1, 2, 3
  simp

-- Fermat's Last Theorem effectively states `¬isGood 3`.
-- The same holds for any multiple of 3.
lemma not_isGood_of_three_dvd (h_fermat : ¬∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^3 + y^3 = z^3)
    {n : ℕ} (hn : 3 ∣ n) : ¬isGood n := by
  rcases hn with ⟨k, rfl⟩
  unfold isGood
  refine mt (fun h ↦ ?_) h_fermat
  rcases h with ⟨x, y, z, hx, hy, hz, h⟩
  use x, y, z ^ k, hx, hy, Nat.pos_pow_of_pos k hz
  convert h using 1
  ring

-- Putting these results together, "good" numbers are simply those not divisible by 3.
lemma isGood_iff_not_three_dvd (h_fermat : ¬∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^3 + y^3 = z^3)
    (n : ℕ) : isGood n ↔ ¬3 ∣ n := by
  constructor
  · intro h
    contrapose! h
    exact not_isGood_of_three_dvd h_fermat h
  · -- To prove the reverse direction, use induction for `3 ≤ n`.
    induction n using Nat.strongRecOn with
    | ind n IH =>
      cases le_or_lt 3 n with
      | inr hn =>
        intro h
        interval_cases n
        · simp at h
        · exact isGood_one
        · exact isGood_two
      | inl hn =>
        -- Obbtain `m` such that `n = m + 3`.
        obtain ⟨m, rfl⟩ : ∃ m, m + 3 = n := by simpa [add_comm] using Nat.le.dest hn
        intro h
        refine isGood_add_three m ?_
        exact IH m (by simp) (by simpa using h)

theorem number_theory_260669 (h_fermat : ¬∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^3 + y^3 = z^3) :
    {n ≤ 2019 | isGood n}.ncard = 1346 := by
  -- The proof depends on Fermat's Last Theorem, which has not yet been formalized.
  -- Therefore we prove that the result follows from Fermat's Last Theorem.

  -- We can more generally show that any number congruent to 1 or 2 modulo 3 is "good".
  -- Put in the form `Nat.count (· ≡ v [MOD r])` to use the existing lemma.
  suffices ∀ m, {n < m | isGood n}.ncard = m - Nat.count (· ≡ 0 [MOD 3]) m by
    calc _
    _ = {n | n < 2020 ∧ isGood n}.ncard := by simp [Nat.lt_succ_iff]
    _ = 2020 - Nat.count (fun x ↦ x ≡ 0 [MOD 3]) 2020 := this 2020
    _ = _ := by
      rw [Nat.count_modEq_card 2020 three_pos 0]
      norm_num

  intro m
  calc _
  _ = {x < m | ¬3 ∣ x}.ncard := by simp [isGood_iff_not_three_dvd h_fermat]
  -- Switch from `Set.ncard` to `Nat.count` via `Finset.card`.
  _ = (Finset.toSet {x ∈ Finset.range m | ¬3 ∣ x}).ncard := by simp
  _ = {x ∈ Finset.range m | ¬3 ∣ x}.card := Set.ncard_coe_Finset _
  _ = Nat.count (¬3 ∣ ·) m := .symm <| Nat.count_eq_card_filter_range _ _
  -- Write a subtraction of negative condition.
  _ = m - Nat.count (3 ∣ ·) m := by
    refine Nat.eq_sub_of_add_eq' ?_
    simpa [Nat.count_eq_card_filter_range] using
      (Finset.range m).filter_card_add_filter_neg_card_eq_card (3 ∣ ·)
  -- Switch from `dvd` to `modEq` notation.
  _ = _ := by simp [Nat.modEq_zero_iff_dvd]
