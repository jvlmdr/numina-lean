-- https://cloud.kili-technology.com/label/projects/label/cm7eni5b9001ozz87g6qu6hy9

import Mathlib

/- Alpha and Beta both took part in a two-day problem-solving competition.
At the end of the second day, each had attempted questions worth a total of 500 points.
Alpha scored 160 points out of 300 points attempted on the first day,
and scored 140 points out of 200 points attempted on the second day.
Beta who did not attempt 300 points on the first day,
had a positive integer score on each of the two days,
and Beta's daily success rate (points scored divided by points attempted)
on each day was less than Alpha's on that day.
Alpha's two-day success ratio was 300/500 = 3/5.
The largest possible two-day success ratio that Beta could achieve is m / n, where
m and n are relatively prime positive integers. What is m + n? -/

theorem algebra_98439 :
    IsGreatest ((fun (a, b, _) ↦ a + b) '' {(a, b, q) : ℕ × ℕ × ℕ |
      a ∈ Set.Ioc 0 q ∧ b ∈ Set.Ioc 0 (500 - q) ∧
      (a / q : ℝ) < 160 / 300 ∧ (b / (500 - q) : ℝ) < 140 / 200}) 349 ∧
    Nat.Coprime 349 500 ∧ 349 + 500 = 849 := by
  refine ⟨?_, by norm_num⟩
  -- IsGreatest comprises a proof of the bound and a proof of attainment.
  -- Prove the bound first.
  -- Combining the two inequalities, we obtain a + b < 350 - q / 6.
  -- Therefore, smaller q will yield a larger sum.
  refine ⟨?_, ?_⟩
  swap
  · simp only [mem_upperBounds, Set.mem_Ioc, Set.mem_image, Set.mem_setOf_eq,
      Prod.exists, exists_and_right, forall_exists_index, and_imp]
    intro x a b q ha_pos haq hb_pos hbq ha hb hx
    rw [← hx]
    refine Nat.le_of_lt_succ ?_
    have hq_pos : 0 < q := ha_pos.trans_le haq
    have hq_rem_pos : 0 < 500 - q := hb_pos.trans_le hbq
    rw [div_lt_iff₀ (by simpa using hq_pos)] at ha
    rw [div_lt_iff₀ (by simpa using hq_rem_pos)] at hb
    refine (Nat.cast_lt (α := ℝ)).mp ?_
    calc _
    _ = (a + b : ℝ) := Nat.cast_add a b
    _ < 160 / 300 * q + 140 / 200 * (500 - q) := add_lt_add ha hb
    _ = 350 - q / 6 := by ring
    _ ≤ 350 := by
      refine sub_le_self _ ?_
      refine div_nonneg ?_ ?_ <;> simp
  · -- Take q as small as possible.
    -- Note that 2 ≤ q since 0 < a and 0 < b.
    rw [Set.mem_image]
    use (1, 348, 2)
    norm_num
