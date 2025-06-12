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


-- From `f` continuous, show that non-negativity on `ℚ` implies non-negativity on `ℝ`.
-- TODO: There probably exists a higher-level way to obtain this result? Avoiding contradiction?
example {f : ℝ → ℝ} (h_cont : Continuous f)
    (h : ∀ x : ℚ, 0 ≤ f x) :
    ∀ x : ℝ, 0 ≤ f x := by
  intro x
  -- Prove by contradiction: Find `q` close enough to `x` to ensure `f q < 0`.
  contrapose! h
  -- Use `Continuous f` to obtain `δ` such that `|f q - f x| < -f x` for `|q - x| < δ`.
  rw [Metric.continuous_iff] at h_cont
  obtain ⟨δ, hδ, h_cont⟩ := h_cont x (-f x) (by simpa using h)
  -- Use `DenseRange Rat.cast` to find `q` such that `|q - x| < δ`.
  have h_dense := Rat.denseRange_cast (𝕜 := ℝ)
  rw [Metric.denseRange_iff] at h_dense
  obtain ⟨q, h_dense⟩ := h_dense x δ hδ
  use q
  calc _
  _ ≤ f x + dist (f q) (f x) := by simpa [add_comm] using Real.sub_le_dist (f q) (f x)
  _ < 0 := by simpa [lt_neg_iff_add_neg'] using h_cont q (by simpa [dist_comm])


lemma dense_binary_rat_Ico (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
    ∀ ε > 0, ∃ (n : ℕ) (a : BitVec n), dist x (a.toNat / (2 ^ n)) < ε := by
  intro ε hε
  rw [Set.mem_Ico] at hx
  let n := ⌈Real.logb 2 ε⁻¹⌉₊
  -- Use floor instead of round to ensure strictly less than `2 ^ n`.
  use n, ⌊2 ^ n * x⌋₊
  simp  -- TODO
  rw [Nat.mod_eq_of_lt]
  swap
  · suffices (⌊2 ^ n * x⌋₊ : ℝ) < ↑(2 ^ n : ℕ) by simpa only [Nat.cast_lt] using this
    calc _
    _ ≤ 2 ^ n * x := by
      refine Nat.floor_le ?_
      simpa using hx.1
    _ < (2 ^ n : ℝ) := by simpa using hx.2  -- Requires `x < 1`.
    _ = ((2 ^ n : ℕ) : ℝ) := by simp

  -- suffices 2 ^ n * dist x (↑⌊2 ^ n * x⌋₊ / 2 ^ n) < 2 ^ n * ε by simpa
  rw [Real.dist_eq]
  -- suffices 2 ^ n * |x - ⌊2 ^ n * x⌋₊ / 2 ^ n| < 2 ^ n * ε by simpa
  suffices |2 ^ n * (x - ⌊2 ^ n * x⌋₊ / 2 ^ n)| < 2 ^ n * ε by simpa [abs_mul]
  suffices |2 ^ n * x - ⌊2 ^ n * x⌋₊| < 2 ^ n * ε by simpa [mul_sub, mul_div_cancel₀]

  suffices |Int.fract (2 ^ n * x)| < 2 ^ n * ε by
    convert this using 2
    unfold Int.fract
    congr
    refine natCast_floor_eq_intCast_floor ?_
    simpa using hx.1

  rw [abs_of_nonneg (Int.fract_nonneg _)]
  refine lt_of_lt_of_le (Int.fract_lt_one _) ?_
  suffices ε⁻¹ ≤ 2 ^ n from (inv_le_iff_one_le_mul₀ hε).mp this
  unfold n
  calc _
  _ = (2 : ℝ) ^ (Real.logb 2 ε⁻¹) := by
    symm
    exact Real.rpow_logb two_pos (by norm_num) (by simpa using hε)
  _ ≤ 2 ^ (⌈Real.logb 2 ε⁻¹⌉₊ : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le one_le_two ?_
    exact Nat.le_ceil _
  _ = _ := by simp


-- TODO: If `Ico` satisfies, the solution is cleaner.
lemma dense_binary_frac_Icc (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    ∀ ε > 0, ∃ (n : ℕ) (a : BitVec n), dist x (a.toNat / (2 ^ n)) < ε := by
  rw [Set.mem_Icc] at hx
  intro ε hε
  -- We need to determine `n` and `a < 2 ^ n` such that `a / 2 ^ n` is within `ε` of `x`.
  -- We could use `a = round (2 ^ n * x)` with `n = logb 2 ε⁻¹`.
  -- However, if `x = 1`, this will not satisfy `a < 2 ^ n`.
  -- If we did use `(2 ^ n - 1) / 2 ^ n` in this case, it could be `ε` away from `1`.
  -- Therefore, use `(⌊2 ^ (n + 1) * x - 1⌋₊) / 2 ^ (n + 1)`?

  let n := ⌈Real.logb 2 ε⁻¹⌉₊
  use n + 1, ⌊2 ^ (n + 1) * x - 1⌋₊
  simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  swap
  · simp only [Nat.floor_sub_one]
    suffices (⌊2 ^ (n + 1) * x⌋₊ - 1) ⊔ (2 - 1) < 2 ^ (n + 1) from lt_of_le_of_lt le_sup_left this
    rw [Nat.sub_max_sub_right]
    refine Nat.sub_one_lt_of_le (by simp) ?_
    rw [sup_le_iff]
    split_ands
    · rw [← @Nat.cast_le ℝ]
      refine le_trans (Nat.floor_le ?_) ?_
      · simpa using hx.1
      · simpa using hx.2
    · simp [Nat.le_self_pow]

  -- TODO: come back and do this if needed
  sorry



theorem algebra_23856 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    {b c : ℝ} (hb : b = (1 + c) / (2 + c)) (hc : 0 < c)
    (h1 : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (h2 : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    ∀ x ∈ Set.Ioo 0 1, 0 < f x - x ∧ f x - x < c := by

  -- TODO: keep one of these?
  have hb_half : 1 / 2 < b := by
    rw [hb]
    refine (div_lt_div_iff₀ two_pos ?_).mpr ?_
    · simp [add_pos, hc]
    · simp [add_mul, hc]
  have hb_two : 1 < 2 * b := (div_lt_iff₀' two_pos).mp hb_half

  intro x hx
  split_ands
  · rw [sub_pos]
    rw [Set.mem_Ioo] at hx
    cases lt_or_le x (1 / 2) with
    | inl hx' =>
      suffices 2 * b * x ≤ f x by
        refine lt_of_lt_of_le ?_ this
        refine lt_mul_left hx.1 hb_two
      -- `2 * b * x ≤ f x`

      sorry

    | inr hx' =>
      -- Suffices to show that `f x` is above the line joining
      -- `(1/2, b)` and `(1, 1)`.
      suffices b + (1 - b) * (2 * x - 1) ≤ f x by
        refine lt_of_lt_of_le ?_ this
        refine lt_add_of_sub_right_lt ?_
        suffices (2 * b - 1) * x - (b - 1) < b from lt_of_eq_of_lt (by ring) this
        refine sub_right_lt_of_lt_add ?_
        suffices (2 * b - 1) * x < 2 * b - 1 from lt_of_lt_of_eq this (by ring)
        refine mul_lt_of_lt_one_right ?_ hx.2
        simpa using hb_two
      -- `b + (1 - b) * (2 * x - 1)`
      sorry

  · sorry
