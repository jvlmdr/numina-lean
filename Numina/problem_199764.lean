-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi3001j4nayv2spcp97

import Mathlib

open scoped List

/- If you write all natural numbers $n$ with $111 \leq n \leq 999$ in any order consecutively,
you will always get a sequence of digits that forms a number divisible by 37. -/

theorem number_theory_199764 (l : List ℕ) (h_perm : l ~ List.Ico 111 1000) :
    37 ∣ Nat.ofDigits 10 (l.map (Nat.digits 10)).flatten := by
  -- Since all numbers in the list have three digits, we can treat them as digits in base 1000.
  suffices 37 ∣ Nat.ofDigits 1000 l by
    convert this using 1
    -- Use induction on the list to handle the concatenation.
    suffices ∀ t : List ℕ, (∀ x ∈ t, 100 ≤ x ∧ x < 1000) →
        Nat.ofDigits 10 (List.map (Nat.digits 10) t).flatten = Nat.ofDigits 1000 t by
      refine this l fun x hx ↦ ?_
      rw [h_perm.mem_iff, List.Ico.mem] at hx
      constructor <;> linarith
    intro t ht
    induction t with
    | nil => simp
    | cons x l IH =>
      rw [Nat.ofDigits_cons]
      rw [List.map_cons, List.flatten_cons, Nat.ofDigits_append, Nat.ofDigits_digits]
      congr 2
      · suffices (Nat.digits 10 x).length = 3 by simp [this]
        specialize ht x (List.mem_cons_self x l)
        rw [Nat.digits_len 10 x (by norm_num) (by linarith)]
        suffices Nat.log 10 x = 2 by simpa using this
        simpa [Nat.log_eq_iff] using ht
      · refine IH fun y hy ↦ ?_
        exact ht y (List.mem_cons_of_mem x hy)

  -- Since 1000 % 37 = 1, divisibility by 37 can be assessed from the sum of the digits.
  rw [Nat.dvd_iff_dvd_digits_sum 37 1000 (by norm_num)]
  rw [Nat.digits_ofDigits 1000 (by norm_num)]
  rotate_left
  · intro x hx
    rw [h_perm.mem_iff, List.Ico.mem] at hx
    exact hx.2
  · intro hl
    suffices l.getLast hl ∈ List.Ico 111 1000 by
      rw [List.Ico.mem] at this
      linarith
    simpa [h_perm.mem_iff] using List.getLast_mem hl

  -- The sum of the arithmetic sequence {111, …, 999} divides 37 since 111 = 37 * 3.
  suffices l.sum = (111 + 999) * 889 / 2 from this ▸ Nat.dvd_mul_left 37 (15 * 889)
  calc _
  _ = (List.Ico 111 1000).sum := h_perm.sum_eq
  _ = ((List.Ico 111 1000).map id).sum := by simp
  _ = ∑ x in (List.Ico 111 1000).toFinset, x := by
    refine (List.sum_toFinset _ ?_).symm
    exact List.Ico.nodup 111 1000
  _ = ∑ x in Finset.Ico 111 1000, x := by
    refine congrArg (∑ x in ·, x) ?_
    ext x
    simp
  _ = ∑ x ∈ Finset.range 889, (111 + x) := by rw [Finset.sum_Ico_eq_sum_range]
  _ = (111 + 999) * 889 / 2 := by
    rw [Finset.sum_add_distrib]
    simp [Finset.sum_range_id]
