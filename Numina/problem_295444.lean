-- https://cloud.kili-technology.com/label/projects/label/cm8ct04tl021p5kayqt2czuvx

import Mathlib

open scoped NNReal

/- Positive real numbers $a$, $b$, $c$ satisfy $a^3 + b^3 = c^3$.
Prove: $a^2 + b^2 - c^2 > 6 (c - a) (c - b)$. -/

theorem inequalities_295444 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 3 + b ^ 3 = c ^ 3) :
    a ^ 2 + b ^ 2 - c ^ 2 > 6 * (c - a) * (c - b) := by
  -- Note that `c^3 - b^3 = (c - b) (c^2 + b c + b^2)`, and likewise for `b^3`.
  -- Apply the strict AM-GM inequality to 6 terms whose product is `(a b c)^6`.
  have h_am_gm : a * b * c < 6⁻¹ * (b * (c^2 + b * c + b^2) + a * (c^2 + c * a + a^2)) := by
    -- Use `NNReal` as it eliminates the need to prove non-negativity of all terms.
    suffices ∀ a b c : ℝ≥0, 0 < a → 0 < b → 0 < c → a ^ 3 + b ^ 3 = c ^ 3 →
        a * b * c < 6⁻¹ * (b * (c^2 + b * c + b^2) + a * (c^2 + c * a + a^2)) from
      this ⟨a, ha.le⟩ ⟨b, hb.le⟩ ⟨c, hc.le⟩ ha hb hc (by simpa [← NNReal.coe_inj] using h)
    intro a b c ha hb hc h
    -- Still need to use `ℝ` for the AM-GM inequality.
    refine NNReal.coe_lt_coe.mp ?_
    convert (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos .univ (fun _ ↦ 6⁻¹)
      (fun i : Fin 6 ↦ NNReal.toReal <| match i with
        | 0 => b * c^2 | 1 => b^2 * c | 2 => b^3
        | 3 => a * c^2 | 4 => a^2 * c | 5 => a^3 | _ => 1) (by simp) (by simp)
      (fun _ _ ↦ NNReal.zero_le_coe)).mpr ?_ using 1
    · -- Prove that the product is equal.
      simp only [← NNReal.coe_rpow]
      rw [← NNReal.coe_prod, NNReal.coe_inj, NNReal.finset_prod_rpow]
      simp only [Fin.prod_univ_six]
      calc _
      _ = ((a * b * c) ^ 6) ^ (6⁻¹ : ℝ) := by
        rw [← NNReal.rpow_ofNat, ← NNReal.rpow_mul]
        simp
      _ = _ := by
        congr
        ring
    · -- Prove that the sum is equal.
      rw [← Finset.mul_sum, NNReal.coe_mul, ← NNReal.coe_sum]
      congr 2
      simp only [Fin.sum_univ_six]
      ring
    · -- If `b c^2` and `b^2 c` are equal, then `b = c`.
      -- This requries that `a = 0`, providing a contradiction.
      use 0, Finset.mem_univ _, 1, Finset.mem_univ _
      simp only [ne_eq, NNReal.coe_inj]
      intro hbc
      have hbc : (b * c) * c = (b * c) * b := by refine (Eq.congr ?_ ?_).mpr hbc <;> ring
      -- Eliminate the cases `b = 0` or `c = 0` as they are positive.
      have hbc : c = b := by simpa [hb.ne', hc.ne'] using hbc
      suffices a = 0 from ha.ne' this
      simpa [hbc] using h

  -- Multiply the target inequality by `a b c` on both sides.
  suffices 6 * (c - a) * (c - b) * (a * b * c) < (a^2 + b^2 - c^2) * (a * b * c) by
    refine lt_of_mul_lt_mul_right this ?_
    simp [mul_nonneg, ha.le, hb.le, hc.le]

  calc _
  -- Use the AM-GM inequality, multiplied by `(c - a) * (c - b)`, which is positive.
  _ = (c - a) * (c - b) * (6 * (a * b * c)) := by ring
  _ < (c - a) * (c - b) * (b * (c ^ 2 + b * c + b ^ 2) + a * (c ^ 2 + c * a + a ^ 2)) := by
    refine (mul_lt_mul_left (mul_pos ?_ ?_)).mpr ?_
    · rw [sub_pos]
      suffices a ^ 3 < c ^ 3 from lt_of_pow_lt_pow_left₀ 3 hc.le this
      simpa [← h] using pow_pos hb 3
    · rw [sub_pos]
      suffices b ^ 3 < c ^ 3 from lt_of_pow_lt_pow_left₀ 3 hc.le this
      simpa [← h] using pow_pos ha 3
    rw [← lt_inv_mul_iff₀ (by norm_num)]
    exact h_am_gm
  -- Use the observation that `c^3 - b^3 = (c - b) (c^2 + b c + b^2)`.
  _ = (c - a) * (c ^ 3 - b ^ 3) * b + (c - b) * (c ^ 3 - a ^ 3) * a := by ring
  _ = (c - a) * a ^ 3 * b + (c - b) * b ^ 3 * a := by simp [← h]
  -- Take out a common factor of `a b` and expand.
  _ = a * b * (a ^ 2 * c + b ^ 2 * c - (a ^ 3 + b ^ 3)) := by ring
  _ = a * b * (a ^ 2 * c + b ^ 2 * c - c ^ 3) := by rw [h]
  _ = _ := by ring
