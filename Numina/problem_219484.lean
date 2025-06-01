-- https://cloud.kili-technology.com/label/projects/label/cmb4vlozi0011wgaytnwllm4m

import Mathlib

/- Let's find all positive integers $n$ for which $2^{n} - 1$ and $2^{n+2} - 1$ are both prime,
and $2^{n+1}-1$ is not divisible by 7. -/

-- Since `2 ^ 3 ≡ 1 [MOD 7]`, the powers of 2 modulo 7 repeat every 3 steps.
lemma two_pow_mod_seven_periodic : (2 ^ · % 7).Periodic 3 := fun n ↦ by simp [pow_add, Nat.mul_mod]

-- A periodic function attains its entire range on `x < c`.
-- Note: `Periodic.exists_mem_Ico₀` requires `AddCommGroup` rather than `AddCommMonoid`.
lemma image_Iio_eq_range_of_periodic {f : ℕ → ℕ} {c : ℕ} (hf : f.Periodic c) (hc : 0 < c) :
    f '' Set.Iio c = Set.range f := by
  ext y
  simp only [Set.mem_image, Set.mem_range, Set.mem_Iio]
  refine ⟨Exists.imp fun _ ⟨_, h⟩ ↦ h, ?_⟩
  intro ⟨x, hy⟩
  induction x using Nat.strongRecOn with
  | ind x IH =>
    cases lt_or_le x c with
    | inl hx => exact ⟨x, hx, hy⟩
    | inr hx =>
      obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le' hx
      exact IH x (by simpa using hc) (by simpa [hf x] using hy)

-- A periodic function attains its entire range on any period.
-- Note: `Function.Periodic.image_Ioc` requires `AddCommGroup` rather than `AddCommMonoid`.
lemma image_Ico_of_periodic {f : ℕ → ℕ} {c : ℕ} (hf : f.Periodic c) (hc : 0 < c) (n : ℕ) :
    f '' Set.Ico n (n + c) = Set.range f := by
  calc _
  _ = (f ∘ (· % c)) '' Finset.Ico n (n + c) := by simp [hf.map_mod_nat]
  _ = f '' Finset.image (· % c) (Finset.Ico n (n + c)) := by
    rw [Set.image_comp]
    simp
  _ = f '' Finset.range c := by rw [Nat.image_Ico_mod]
  _ = _ := by simpa using image_Iio_eq_range_of_periodic hf hc

-- Explicitly obtain three consecutive numbers from `Finset.Ico`.
lemma finset_Ico_add_three (n : ℕ) : Finset.Ico n (n + 3) = {n, n + 1, n + 2} := by
  have : Finset.Ico 0 3 = {0, 1, 2} := rfl
  convert congrArg (Finset.map (addLeftEmbedding n)) this using 1
  · rw [Finset.map_add_left_Ico]
    simp
  · simp

-- Explicitly obtain three consecutive numbers from `Set.Ico`.
lemma Ico_add_three (n : ℕ) : Set.Ico n (n + 3) = {n, n + 1, n + 2} := by
  simpa using congrArg Finset.toSet (finset_Ico_add_three n)

theorem number_theory_219484 (n : ℕ) (hn : 0 < n) :
    Nat.Prime (2 ^ n - 1) ∧ Nat.Prime (2 ^ (n + 2) - 1) ∧ ¬7 ∣ 2 ^ (n + 1) - 1 ↔ n = 3 := by
  -- It is trivial to prove the reverse direction, that `n = 3` is a solution.
  refine ⟨?_, fun hn ↦ by norm_num [hn]⟩
  intro ⟨h_pow, h_pow_add_two, h_dvd⟩
  -- Since `2 ^ 0 = 1` and `2 ^ x % 7` has period 3,
  -- one of any three consecutive numbers must be congruent to 1.
  have h : 1 ∈ (2 ^ · % 7) '' Set.Ico n (n + 3) := by
    rw [image_Ico_of_periodic two_pow_mod_seven_periodic three_pos, Set.mem_range]
    use 0
    simp
  -- Convert the `· % 7 = 1` condition into `7 ∣ 2 ^ · - 1`.
  have h : 7 ∣ 2 ^ n - 1 ∨ 7 ∣ 2 ^ (n + 1) - 1 ∨ 7 ∣ 2 ^ (n + 2) - 1 := by
    suffices ∀ n, 7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 by simpa [Ico_add_three, this] using h
    intro n
    calc _
    _ ↔ 1 ≡ 2 ^ n [MOD 7] := .symm <| Nat.modEq_iff_dvd' Nat.one_le_two_pow
    _ ↔ 2 ^ n ≡ 1 [MOD 7] := Nat.ModEq.comm
    _ ↔ 2 ^ n % 7 = 1 % 7 := .rfl
    _ ↔ _ := by simp
  -- Eliminate the divisibility condition for `2 ^ (n + 1) - 1`.
  have h : 7 ∣ 2 ^ n - 1 ∨ 7 ∣ 2 ^ (n + 2) - 1 := by simpa [h_dvd] using h
  -- Since both of these numbers are prime, 7 divides them iff they are equal to 7.
  -- Consider each case independently.
  cases h with
  | inl h =>
    rw [Nat.prime_dvd_prime_iff_eq (by norm_num) h_pow] at h
    suffices 2 ^ n = 2 ^ 3 from Nat.pow_right_injective (le_refl 2) this
    simpa using h.symm
  | inr h =>
    rw [Nat.prime_dvd_prime_iff_eq (by norm_num) h_pow_add_two] at h
    -- We have a contradiction since `n = 1` and `2 ^ n - 1 = 1` is not prime.
    exfalso
    suffices n = 1 by
      refine Nat.not_prime_one ?_
      simpa [this] using h_pow
    suffices n + 2 = 3 by simpa
    suffices 2 ^ (n + 2) = 2 ^ 3 from Nat.pow_right_injective (le_refl 2) this
    suffices 2 ^ (n + 2) - 1 = 7 by simpa
    simpa using h.symm
