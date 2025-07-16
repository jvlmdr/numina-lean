-- https://cloud.kili-technology.com/label/projects/label/cmauuk3x300041rayopcw3mue

import Mathlib

/- Let $f : [0, 1] \rightarrow \mathbb{R}$ be continuous and satisfy:
$$
\begin{aligned}
b f(2 x) & = f(x), & & 0 \leq x \leq 1 / 2 \\
f(x) & = b + (1-b) f(2 x - 1), & & 1 / 2 \leq x \leq 1
\end{aligned}
$$
where $b=\frac{1+c}{2+c}, c>0$.
Show that $0 < f(x) - x < c$ for every $x, 0 < x < 1$. -/

-- For any `ε > 0`, there exist binary rationals `k / 2 ^ n` within `ε` of all `x ∈ [0, 1)`.
lemma exists_binary (ε : ℝ) (hε : 0 < ε) (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
    ∃ n k : ℕ, k < 2 ^ n ∧ dist x (k / 2 ^ n) < ε := by
  simp only [Set.mem_Ico] at hx
  let n := ⌊Real.logb 2 (1 / ε)⌋₊ + 1
  let k := ⌊x * 2 ^ n⌋₊
  use n, k
  split_ands
  · unfold k
    rw [← @Nat.cast_lt ℝ]
    calc _
    _ ≤ x * 2 ^ n := Nat.floor_le <| by simpa using hx.1
    _ < _ := by simpa using hx.2
  · calc _
    _ = x - k / 2 ^ n := by
      suffices k / 2 ^ n ≤ x by simpa [Real.dist_eq]
      refine div_le_of_le_mul₀ (by simp) hx.1 ?_
      exact Nat.floor_le (by simpa using hx.1)
    _ = (x * 2 ^ n - k) / 2 ^ n := by simp [sub_div]
    _ < 1 / 2 ^ n := by
      refine div_lt_div_of_pos_right ?_ (by simp)
      refine sub_left_lt_of_lt_add ?_
      exact Nat.lt_floor_add_one (x * 2 ^ n)
    _ < ε := by
      rw [one_div_lt (by simp) hε]
      rw [← Real.rpow_natCast, ← Real.logb_lt_iff_lt_rpow one_lt_two (by simpa)]
      unfold n
      simpa using Nat.lt_floor_add_one (Real.logb 2 (1 / ε))

-- TODO: It feels like this should be a one-liner!
lemma nonneg_of_continuousOn_of_binary {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ico 0 1))
    (h : ∀ n k : ℕ, k < 2 ^ n → 0 ≤ f (k / 2 ^ n)) :
    ∀ x ∈ Set.Ico 0 1, 0 ≤ f x := by
  intro x hx
  -- Use contradiction.
  -- If `f x < 0`, then we can find a binary rational `q` close to `x` such that `f q < 0`.
  -- However, we have a proof that `0 ≤ f q`.
  contrapose! h
  -- Use continuity of `f` to obtain a radius `δ` within which `f` is negative.
  rw [Metric.continuousOn_iff] at hf
  obtain ⟨δ, hδ_pos, hδ⟩ := hf x hx (-f x) (by simpa)
  -- Find a binary rational `q` within this radius.
  obtain ⟨n, k, hk, hq⟩ := exists_binary δ hδ_pos x hx
  use n, k, hk
  -- Use `f q ≤ f x + |f q - f x| < f x + (-f x) = 0`.
  calc _
  _ ≤ f x + dist (f (k / 2 ^ n)) (f x) := by
    rw [← sub_le_iff_le_add']
    exact Real.sub_le_dist _ _
  _ < f x + -f x := by
    gcongr
    refine hδ (k / 2 ^ n) ?_ ?_
    · split_ands
      · simp [div_nonneg]
      · simpa [div_lt_one, ← @Nat.cast_lt ℝ] using hk
    · simpa [dist_comm] using hq
  _ = 0 := by simp

theorem algebra_23856 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    {b c : ℝ} (hb : b = (1 + c) / (2 + c)) (hc : 0 < c)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    ∀ x ∈ Set.Ioo 0 1, f x - x ∈ Set.Ioo 0 c := by

  have hb_lt : b < 1 := by
    rw [hb]
    refine (div_lt_one ?_).mpr ?_
    · simp [add_pos, hc]
    · simp
  -- TODO: keep one of these?
  have hb_half : 1 / 2 < b := by
    rw [hb]
    refine (div_lt_div_iff₀ two_pos ?_).mpr ?_
    · simp [add_pos, hc]
    · simp [add_mul, hc]
  have hb_two : 1 < 2 * b := (div_lt_iff₀' two_pos).mp hb_half

  have hf_zero : f 0 = 0 := by sorry
  have hf_half : f 2⁻¹ = b := by sorry
  have hf_one : f 1 = 1 := by sorry

  -- Split into two separate goals.
  simp only [Set.mem_Ioo, forall_and]

  refine ⟨?_, sorry⟩

  -- Rewrite using `≤`, which can be proved using density of binary rationals.
  suffices ∀ r : ℝ, r ∈ Set.Ico 0 1 →
      -- (1 - r) * f 0 + r * f 2⁻¹ ≤ f ((1 - r) * 0 + r * 2⁻¹) ∧
      -- (1 - r) * f 2⁻¹ + r * f 1 ≤ f ((1 - r) * 2⁻¹ + r * 1) by
      r * b ≤ f (r * 2⁻¹) ∧ (1 - r) * b + r ≤ f ((1 - r) * 2⁻¹ + r) by
    intro x hx_mem
    rw [sub_pos]
    cases lt_or_le x 2⁻¹ with
    | inl hx_half =>
      specialize this (x * 2) (by split_ands <;> linarith)
      calc _
      _ < 2 * b * x := lt_mul_of_one_lt_left hx_mem.1 hb_two
      _ = _ := by ring
      _ ≤ _ := this.1  -- TODO: suffices?
      _ = _ := by simp
    | inr hx_half =>
      specialize this (x * 2 - 1) (by split_ands <;> linarith)
      calc _
      _ = 1 - (1 - x) := by ring  -- TODO: suffices?
      _ < 1 - 2 * (1 - b) * (1 - x) := by
        refine sub_lt_sub_left ?_ _
        refine mul_lt_of_lt_one_left ?_ ?_ <;> linarith
      _ = _ := by ring
      _ ≤ _ := this.2
      _ = _ := congrArg f (by ring)

  -- Use the density of binary rationals and the fact that `f` is continuous.
  -- TODO: Should be separate foralls?
  suffices ∀ n k : ℕ, k < 2 ^ n →
      k / 2 ^ n * b ≤ f (k / 2 ^ n * 2⁻¹) ∧
      (1 - k / 2 ^ n) * b + k / 2 ^ n ≤ f ((1 - k / 2 ^ n) * 2⁻¹ + k / 2 ^ n) by
    intro r hr_mem
    -- simp at hr_mem  -- TODO
    split_ands
    · rw [← sub_nonneg]
      refine nonneg_of_continuousOn_of_binary ?_ ?_ r hr_mem (f := fun r ↦ f (r * 2⁻¹) - r * b)
      · refine .sub (.comp hf ?_ ?_) ?_
        · exact (continuous_mul_right _).continuousOn
        · intro x hx_mem
          simp at hr_mem hx_mem  -- TODO
          split_ands <;> linarith
        · exact (continuous_mul_right b).continuousOn
      intro n k hk
      simp only
      rw [sub_nonneg]
      exact (this n k hk).1
    · rw [← sub_nonneg]
      refine nonneg_of_continuousOn_of_binary ?_ ?_ r hr_mem
        (f := fun r ↦ f ((1 - r) * 2⁻¹ + r) - ((1 - r) * b + r))
      · refine .sub (.comp hf ?_ ?_) ?_
        -- TODO: finalize after proving the induction
        · sorry
        · intro x hx_mem
          simp at hr_mem hx_mem  -- TODO
          split_ands <;> linarith
        · sorry
      intro n k hk
      rw [sub_nonneg]
      exact (this n k hk).2

  -- This is what we can show by induction.
  sorry
