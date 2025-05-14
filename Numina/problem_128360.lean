-- https://cloud.kili-technology.com/label/projects/label/cma3ygioc00boahayrryfnwxq

import Mathlib

open Polynomial Filter

/- p(x) is a polynomial of degree n with real coefficients and is non-negative for all x.
Show that p(x) + p'(x) + p''(x) + ... (n+1 terms) ≥ 0 for all x. -/

theorem algebra_128360 (p : Polynomial ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p.eval x) :
    ∀ x, 0 ≤ ∑ i ∈ Finset.range (p.natDegree + 1), (derivative^[i] p).eval x := by
  -- If `n = 0`, then `q(x) = p(x) = c ≥ 0` and the inequality holds trivially.
  -- This allows us to focus on the case where `p` is non-trivial with `0 < p.degree`.
  cases Nat.eq_zero_or_pos p.natDegree with
  | inl hp_natDegree =>
    simpa [hp_natDegree] using hp_nonneg
  | inr hp_natDegree =>
    generalize hn : p.natDegree = n
    let q := ∑ i ∈ Finset.range (n + 1), derivative^[i] p
    -- Rewrite sum of polynomial evaluations as evaluation of sum of polynomials.
    -- Use the linear version `leval` to map through the sum.
    suffices ∀ x, 0 ≤ q.leval x by simpa [q] using this
    simp only [leval_apply]

    -- The leading term of `q` matches that of `p`.
    -- Therefore `q`, like `p`, will go to +∞ as `x` becomes large in either direction.
    -- It will therefore suffice to show that `q` is non-negative at all stationary points.
    suffices Tendsto q.eval (cocompact ℝ) atTop by
      -- The derivative of `q` is `q - p`. When this is zero, `q x = p x ≥ 0`.
      have h_deriv : q.derivative = q - p := by
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

      -- Obtain the global minimum since `q` is continuous and goes to infinity.
      obtain ⟨u, hu_min⟩ : ∃ x, IsMinOn q.eval Set.univ x := by
        suffices ∃ x ∈ Set.univ, IsMinOn q.eval Set.univ x by simpa using this
        refine ContinuousOn.exists_isMinOn' q.continuousOn_aeval isClosed_univ (Set.mem_univ 0) ?_
        simpa using this.eventually_ge_atTop (eval 0 q)
      -- We only need to prove that the minimum is non-negative.
      suffices 0 ≤ q.eval u from fun x ↦ this.trans (isMinOn_iff.mp hu_min x (Set.mem_univ x))
      -- Obtain this from the derivative being zero at any local minimum.
      convert hp_nonneg u using 1
      simpa [h_deriv, sub_eq_zero] using (hu_min.isLocalMin univ_mem).deriv_eq_zero

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

    -- It will often be useful to have `natDegree` (e.g. `natDegree_comp`).
    have hq_natDegree : q.natDegree = p.natDegree := natDegree_eq_of_degree_eq hq_degree
    -- Get rid of `n` to reduce rewrites and substitutions.
    rcases hn with rfl

    -- Split into two `Tendsto` statements, `atBot` and `atTop`.
    simp only [cocompact_eq_atBot_atTop, tendsto_sup]

    -- Mathlib contains results for a polynomial `p` as `x` tends to +∞.
    -- To handle `x` going to -∞, instead consider `p.comp (-X)` as `x` tends to +∞.
    suffices Tendsto (q.comp (-X)).eval atTop atTop ∧ Tendsto q.eval atTop atTop by
      convert this using 1
      constructor
      -- The forward direction is a straightforward application of `Tendsto.comp`.
      · intro h
        simpa using h.comp tendsto_neg_atTop_atBot
      -- To prove the reverse direction, compose again with negation.
      · intro h
        simpa [Function.comp_def] using h.comp tendsto_neg_atBot_atTop

    -- Suffices to prove this behavior for `p` rather than `q` as they share a leading term.
    suffices Tendsto (p.comp (-X)).eval atTop atTop ∧ Tendsto p.eval atTop atTop by
      convert this using 1
      · simp only [tendsto_atTop_iff_leadingCoeff_nonneg, ← natDegree_pos_iff_degree_pos]
        simp [natDegree_comp, hq_natDegree, hq_lead]
      · simp only [tendsto_atTop_iff_leadingCoeff_nonneg]
        rw [hq_degree, hq_lead]

    -- Given that the degree is non-zero, a non-negative polynomial must tend to +∞.
    suffices ∀ p : ℝ[X], 0 < p.degree → (∀ x, 0 ≤ p.eval x) → Tendsto p.eval atTop atTop by
      refine ⟨?_, this p hp_degree hp_nonneg⟩
      refine this ?_ ?_ ?_
      · simpa [← natDegree_pos_iff_degree_pos, natDegree_comp] using hp_natDegree
      · simpa using fun x ↦ hp_nonneg (-x)

    intro p hp_degree hp_nonneg
    refine tendsto_atTop_of_leadingCoeff_nonneg p hp_degree ?_
    -- Need to show that the leading coefficient is non-negative; prove by contradiction.
    -- If the leading coefficient were negative, `p` would tend to -∞ (i.e. < 0) for large `x`.
    suffices ¬∃ x ≥ 0, p.eval x < 0 by
      refine le_of_not_lt ?_
      refine mt (fun hp_lead ↦ ?_) this
      -- We can use `Tendsto p.eval atTop atBot` to obtain some `x` such that `p.eval x < 0`.
      refine exists_lt_of_tendsto_atBot ?_ 0 0
      exact tendsto_atBot_of_leadingCoeff_nonpos p hp_degree hp_lead.le
    simpa using fun x _ ↦ hp_nonneg x
