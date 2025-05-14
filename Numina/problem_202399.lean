-- https://cloud.kili-technology.com/label/projects/label/cmaktgyj8006ay1v58zrq97ki

import Mathlib

open Real

/- Prove the inequalities:
a) $\sqrt[n]{a_1 ⋯ a_n} ≤ \frac{a_1 + ⋯ + a_n}{n}$ (Cauchy's inequality);
b) $(\frac{b_1 + ⋯ + b_n}{n})^{b_1 + ⋯ + b_n} ≤ b_1^{b_1} ⋯ b_n^{b_n}$
c) $c_1^{b_1} ⋯ c_n^{b_n} ≤ c_1 b_1 + ⋯ + c_n b_n$, where $b_1 + ⋯ + b_n = 1$.
The values of the variables are assumed to be positive. -/

theorem inequalities_202399 {n : ℕ} (hn : 0 < n) (a b c : Fin n → ℝ)
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i) (hc_pos : ∀ i, 0 < c i)
    (hb : ∑ i, b i = 1) :
    (∏ i, a i) ^ (1 / n : ℝ) ≤ (∑ i, a i) / n ∧
    ((∑ i, b i) / n) ^ (∑ i, b i) ≤ ∏ i, (b i) ^ (b i) ∧
    ∏ i, (c i) ^ (b i) ≤ ∑ i, c i * b i := by
  refine ⟨?_, ?_, ?_⟩
  -- The first result is simply the unweighted AM-GM inequality for `n` elements.
  · convert geom_mean_le_arith_mean Finset.univ 1 a (by simp) ?_ ?_ using 1
    · simp
    · simp
    · simpa using hn
    · simpa using fun i ↦ (ha_pos i).le
  -- The second result can be obtained from the weighted GM-HM inequality.
  · convert harm_mean_le_geom_mean_weighted Finset.univ b b ?_ ?_ hb ?_ using 1
    · calc _
      _ = (n⁻¹ : ℝ) := by simp [hb]
      _ = _ := by
        suffices ∀ i, b i / b i = 1 by simp [this]
        exact fun i ↦ div_self (hb_pos i).ne'
    · suffices Nonempty (Fin n) from Finset.univ_nonempty
      exact Fin.pos_iff_nonempty.mp hn
    · simpa using hb_pos
    · simpa using hb_pos
  -- The third result is precisely the weighted AM-GM inequality.
  · convert geom_mean_le_arith_mean_weighted Finset.univ b c ?_ hb ?_ using 1
    · simp [mul_comm]
    · simpa using fun i ↦ (hb_pos i).le
    · simpa using fun i ↦ (hc_pos i).le
