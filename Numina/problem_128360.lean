-- https://cloud.kili-technology.com/label/projects/label/cma3ygioc00boahayrryfnwxq

import Mathlib

open Polynomial Filter

/- p(x) is a polynomial of degree n with real coefficients and is non-negative for all x.
Show that p(x) + p'(x) + p''(x) + ... (n+1 terms) ≥ 0 for all x. -/

theorem algebra_128360 {n : ℕ} (p : Polynomial ℝ) (hn : p.natDegree = n)
    (hp_nonneg : ∀ x, 0 ≤ p.eval x) :
    ∀ x, 0 ≤ ∑ i ∈ Finset.range (n + 1), (derivative^[i] p).eval x := by
  -- If `n = 0`, then `q(x) = p(x) = c ≥ 0` and the inequality holds trivially.
  -- This allows us to focus on the case where `p` is non-trivial with `0 < p.degree`.
  cases Nat.eq_zero_or_pos n with
  | inl hn =>
    simpa [hn] using hp_nonneg
  | inr hn_pos =>
    let q := ∑ i ∈ Finset.range (n + 1), derivative^[i] p
    suffices ∀ x, 0 ≤ q.leval x by simpa [q] using this
    change ∀ x, 0 ≤ q.eval x

    suffices Tendsto q.eval (cocompact ℝ) atTop by
      suffices h_deriv : q.derivative = q - p by
        obtain ⟨u, hu_min⟩ : ∃ x, IsMinOn q.eval Set.univ x := by
          suffices ∃ x ∈ Set.univ, IsMinOn q.eval Set.univ x by simpa using this
          refine ContinuousOn.exists_isMinOn' q.continuousOn_aeval isClosed_univ (Set.mem_univ 0) ?_
          simpa using this.eventually_ge_atTop (eval 0 q)

        suffices 0 ≤ q.eval u from fun x ↦ le_trans this (isMinOn_iff.mp hu_min x (Set.mem_univ x))
        suffices q.eval u = p.eval u by simpa [this] using hp_nonneg u
        refine sub_eq_zero.mp ?_
        suffices eval u (q - p) = 0 by simpa using this
        rw [← h_deriv]
        simpa using (hu_min.isLocalMin univ_mem).deriv_eq_zero

      unfold q
      calc _
      _ = ∑ i ∈ Finset.range (n + 1), derivative^[i + 1] p := by
        simp_rw [Function.iterate_succ']
        simp
      _ = ∑ i ∈ Finset.range n, derivative^[i + 1] p := by
        rw [Finset.sum_range_succ, add_right_eq_self]
        refine iterate_derivative_eq_zero ?_
        simp [hn]
      _ = _ := by simp [Finset.sum_range_succ']

    -- TODO: This ends up being two names for the same thing.
    have hp_natDegree : 0 < p.natDegree := hn ▸ hn_pos
    have hp_degree : 0 < p.degree := natDegree_pos_iff_degree_pos.mp hp_natDegree

    -- The degree of all terms in `q` after the first is less than that of `p`.
    have hq_degree_rest_lt : (∑ i ∈ Finset.range n, derivative^[i + 1] p).degree < p.degree := by
      refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      refine (Finset.sup_lt_iff (bot_lt_of_lt hp_degree)).mpr ?_
      intro i hi
      refine degree_lt_degree ?_
      calc _
      _ ≤ (derivative p).natDegree - i := by
        simpa using natDegree_iterate_derivative (derivative p) i
      _ ≤ (derivative p).natDegree := Nat.sub_le _ i
      _ < p.natDegree := natDegree_derivative_lt hp_natDegree.ne'
    -- Therefore, the degree and leading coefficient of `q` are equal to those of `p`.
    have hq_degree : q.degree = p.degree := by
      unfold q
      rw [Finset.sum_range_succ']
      simpa using degree_add_eq_right_of_degree_lt hq_degree_rest_lt
    have hq_lead : q.leadingCoeff = p.leadingCoeff := by
      unfold q
      rw [Finset.sum_range_succ']
      simpa using leadingCoeff_add_of_degree_lt hq_degree_rest_lt

    -- Get rid of `n` to reduce rewrites and substitutions.
    rcases hn with rfl
    clear hn_pos  -- TODO
    have hq_natDegree : q.natDegree = p.natDegree := natDegree_eq_of_degree_eq hq_degree

    -- Mathlib contains results for a polynomial as x tends to +∞.
    -- To obtain results for x tending to -∞, use `p.comp (-X)`.
    have h_tendsto_atBot {p : ℝ[X]} :
        Tendsto p.eval atBot atTop ↔ Tendsto (p.comp (-X)).eval atTop atTop := by
      constructor
      · intro h
        simpa using h.comp tendsto_neg_atTop_atBot
      · intro h
        simpa [Function.comp_def] using h.comp tendsto_neg_atBot_atTop

    have h_degree_comp_neg_X {p : ℝ[X]} (hp : 0 < p.degree) : 0 < (p.comp (-X)).degree := by
      simpa [← natDegree_pos_iff_degree_pos, natDegree_comp] using hp

    have hp_tendsto_atTop : Tendsto p.eval atTop atTop := by
      refine tendsto_atTop_of_leadingCoeff_nonneg p hp_degree ?_
      refine le_of_not_lt ?_
      intro hp_lead
      have := tendsto_atBot_of_leadingCoeff_nonpos p hp_degree hp_lead.le
      suffices ¬∀ᶠ x in atTop, 0 ≤ p.eval x from this (.of_forall hp_nonneg)
      simpa using fun x ↦ exists_lt_of_tendsto_atBot this x 0

    have hp_tendsto_atBot : Tendsto p.eval atBot atTop := by
      rw [h_tendsto_atBot]
      refine tendsto_atTop_of_leadingCoeff_nonneg _ (h_degree_comp_neg_X hp_degree) ?_
      refine le_of_not_lt ?_
      intro hp_lead
      have := tendsto_atBot_of_leadingCoeff_nonpos _ (h_degree_comp_neg_X hp_degree) hp_lead.le
      suffices ¬∀ᶠ x in atTop, 0 ≤ p.eval (-x) from this (.of_forall fun x ↦ hp_nonneg (-x))
      simpa using fun x ↦ exists_lt_of_tendsto_atBot this x 0

    -- TODO: Avoid multiple uses of `tendsto_atTop_iff_leadingCoeff_nonneg`?
    suffices Tendsto p.eval (cocompact ℝ) atTop by
      simp only [cocompact_eq_atBot_atTop, tendsto_sup] at this ⊢
      convert this using 1
      · simp only [h_tendsto_atBot, tendsto_atTop_iff_leadingCoeff_nonneg]
        simp [← natDegree_pos_iff_degree_pos, natDegree_comp, hq_natDegree, hq_lead]
      · simp [tendsto_atTop_iff_leadingCoeff_nonneg, hq_degree, hq_lead]

    simp only [cocompact_eq_atBot_atTop, tendsto_sup]
    exact ⟨hp_tendsto_atBot, hp_tendsto_atTop⟩
