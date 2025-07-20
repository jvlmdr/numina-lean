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

-- For any `ε > 0`, there exist binary fractions `k / 2 ^ n` within `ε` of all `x ∈ [0, 1)`.
lemma exists_binary_fraction (ε : ℝ) (hε : 0 < ε) (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
    ∃ n k : ℕ, k < 2 ^ n ∧ dist (k / 2 ^ n : ℝ) x < ε := by
  rw [Set.mem_Ico] at hx
  let n := ⌈Real.logb 2 (1 / ε)⌉₊
  let k := ⌊x * 2 ^ n⌋₊
  use n, k
  split_ands
  · rw [Nat.floor_lt' (by simp)]
    simpa using hx.2
  · calc _
    _ = x - k / 2 ^ n := by
      rw [dist_comm _ x]
      suffices k / 2 ^ n ≤ x by simpa [Real.dist_eq]
      refine div_le_of_le_mul₀ (by simp) hx.1 ?_
      exact Nat.floor_le (by simpa using hx.1)
    _ = (x * 2 ^ n - k) / 2 ^ n := by simp [sub_div]
    _ < 1 / 2 ^ n := by
      refine div_lt_div_of_pos_right ?_ (by simp)
      refine sub_left_lt_of_lt_add ?_
      exact Nat.lt_floor_add_one (x * 2 ^ n)
    _ ≤ ε := by
      rw [one_div_le (by simp) hε]
      rw [← Real.rpow_natCast, ← Real.logb_le_iff_le_rpow one_lt_two (by simpa)]
      exact Nat.le_ceil _

-- If a continuous function is nonnegative on all binary fractions, it is nonnegative on [0, 1).
lemma nonneg_of_continuousOn_of_binary {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ico 0 1))
    (h : ∀ n k : ℕ, k < 2 ^ n → 0 ≤ f (k / 2 ^ n)) :
    ∀ x ∈ Set.Ico 0 1, 0 ≤ f x := by
  intro x hx
  -- Use contradiction:
  -- If `f x < 0`, then we can find a binary rational `q` close to `x` such that `f q < 0`.
  -- However, we have a proof that `0 ≤ f q`.
  contrapose! h
  -- Use continuity of `f` to obtain a radius `δ` within which `f` is negative.
  rw [Metric.continuousOn_iff] at hf
  obtain ⟨δ, hδ_pos, hδ⟩ := hf x hx (-f x) (by simpa)
  -- Obtain a binary rational `q` within the radius `δ` of `x`.
  obtain ⟨n, k, hk, hq⟩ := exists_binary_fraction δ hδ_pos x hx
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

-- From the recursive function specification, `f 0 = 0`.
lemma lemma_0 {f : ℝ → ℝ} {b : ℝ} (hb : b ≠ 1)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x) :
    f 0 = 0 := by
  specialize hf₁ 0 (by simp)
  have : b * f 0 = f 0 := by simpa using hf₁
  exact eq_zero_of_mul_eq_self_left hb this

-- From the recursive function specification, `f 1 = 1`.
lemma lemma_1 {f : ℝ → ℝ} {b : ℝ} (hb : b ≠ 0)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    f 1 = 1 := by
  specialize hf₂ 1 (by norm_num)
  have : f 1 = b - b * f 1 + f 1 :=
    calc _
    _ = _ := hf₂
    _ = b + (1 - b) * f 1 := by norm_num
    _ = _ := by ring
  have : b = b * f 1 := by simpa [sub_eq_zero]
  exact (mul_eq_left₀ hb).mp this.symm

-- From the recursive function specification, `f 2⁻¹ = b`.
lemma lemma_2 {f : ℝ → ℝ} {b : ℝ} (hb : b ≠ 0)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    f 2⁻¹ = b := by
  specialize hf₁ 2⁻¹ (by simp)
  simpa [lemma_1 hb hf₂] using hf₁.symm

-- The recursive specification on [0, 1/2] applied to binary fractions.
-- This is more suitable for induction.
lemma lemma_3 {f : ℝ → ℝ} {b : ℝ}
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (n k : ℕ) (hkn : k ≤ 2 ^ n) :
    f (k / 2 ^ (n + 1)) = b * f (k / 2 ^ n) := by
  symm
  convert hf₁ (k / 2 ^ (n + 1)) ?_ using 1
  · congr
    ring
  · split_ands
    · simp [div_nonneg]
    · rw [div_le_div_iff₀ (by simp) two_pos]
      suffices (k : ℝ) ≤ 2 ^ n by simpa [pow_succ]
      simpa [← @Nat.cast_le ℝ] using hkn

-- The recursive specification on [1/2, 1] applied to binary fractions.
-- This is more suitable for induction.
lemma lemma_4 {f : ℝ → ℝ} {b : ℝ}
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1))
    (n k : ℕ) (hkn : k ≤ 2 ^ n) :
    f (↑(2 ^ n + k) / 2 ^ (n + 1)) = b + (1 - b) * f (k / 2 ^ n) := by
  convert hf₂ ((1 + k / 2 ^ n) / 2) ?_ using 1
  · congr 1
    suffices ↑(2 ^ n + k) / 2 ^ n = (1 + k / 2 ^ n : ℝ) by
      convert congrArg (· / 2) this using 1
      ring
    simp [add_div]
  · congr
    ring
  · split_ands
    · gcongr
      simp [div_nonneg]
    · refine div_le_one_of_le₀ ?_ zero_le_two
      suffices (k : ℝ) / 2 ^ n ≤ 1 by linarith
      refine div_le_one_of_le₀ ?_ (by simp)
      simpa [← @Nat.cast_le ℝ] using hkn

-- Show that `x ≤ f x` for all `x = k / 2 ^ n` using induction on `n`.
lemma lemma_5 {f : ℝ → ℝ} {b : ℝ} (hb : b ∈ Set.Ioo (1 / 2) 1)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1))
    (n k : ℕ) (hkn : k ≤ 2 ^ n) :
    k / 2 ^ n ≤ f (k / 2 ^ n) := by
  rw [Set.mem_Ioo] at hb
  induction n generalizing k with
  | zero =>
    interval_cases k
    · suffices f 0 = 0 by simp [this]
      exact lemma_0 (by linarith) hf₁
    · suffices f 1 = 1 by simp [this]
      exact lemma_1 (by linarith) hf₂
  | succ n IH =>
    cases lt_or_le k (2 ^ n) with
    | inl hk =>
      rw [lemma_3 hf₁ n k hk.le]
      calc _
      _ = 2⁻¹ * (k / 2 ^ n : ℝ) := by ring
      _ ≤ b * (k / 2 ^ n) := by
        gcongr
        linarith
      _ ≤ b * f (k / 2 ^ n) := by
        gcongr
        · linarith
        · exact IH _ hk.le
    | inr hk =>
      -- Replace `k ≥ 2 ^ n` with `k = 2 ^ n + j`.
      obtain ⟨j, rfl⟩ : ∃ j, 2 ^ n + j = k := Nat.le.dest hk
      replace hkn : j ≤ 2 ^ n := by
        rw [pow_succ] at hkn
        linarith
      rw [lemma_4 hf₂ n j hkn]
      calc _
      _ = 2⁻¹ + (j / 2 ^ (n + 1) : ℝ) := by simp [add_div, pow_succ, div_mul_cancel_left₀]
      -- Rewrite in terms of `1 - j / 2 ^ n` to show inequality.
      _ = 1 - 2⁻¹ * (1 - j / 2 ^ n : ℝ) := by ring
      _ ≤ 1 - (1 - b) * (1 - j / 2 ^ n) := by
        gcongr
        · simpa [div_le_one₀, ← @Nat.cast_le ℝ] using hkn
        · linarith
      _ = b + (1 - b) * (j / 2 ^ n : ℝ) := by ring
      _ ≤ _ := by
        gcongr
        · linarith
        · exact IH j hkn

-- The left side of the main result, `0 < f x - x`.
lemma lemma_6 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    {b : ℝ} (hb : b ∈ Set.Ioo (1 / 2) 1)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    ∀ x ∈ Set.Ioo 0 1, 0 < f x - x := by
  rw [Set.mem_Ioo] at hb
  -- To prove that `f x` is *strictly* greater than `x`, we prove that `f x` is greater than
  -- or equal to the piecewise linear function joining `(0, 0), (2⁻¹, b), (1, 1)`.
  -- To prove the weak inequality, it will suffice to prove it for binary fractions and
  -- extend this to all reals in `[0, 1)` using density and the fact that `f` is continuous.

  -- First, rewrite in terms of the piecewise linear function.
  suffices ∀ r : ℝ, r ∈ Set.Ico 0 1 →
      r * b ≤ f (r * 2⁻¹) ∧ (1 - r) * b + r ≤ f ((1 - r) * 2⁻¹ + r) by
    intro x hx_mem
    rw [Set.mem_Ioo] at hx_mem
    rw [sub_pos]
    cases lt_or_le x 2⁻¹ with
    | inl hx_half =>
      specialize this (x * 2) (by split_ands <;> linarith)
      calc _
      _ < 2 * b * x := lt_mul_of_one_lt_left hx_mem.1 (by linarith)
      _ = _ := by ring
      _ ≤ _ := this.1
      _ = _ := by simp
    | inr hx_half =>
      specialize this (x * 2 - 1) (by split_ands <;> linarith)
      calc _
      _ = 1 - (1 - x) := by ring
      _ < 1 - 2 * (1 - b) * (1 - x) := by
        refine sub_lt_sub_left ?_ _
        refine mul_lt_of_lt_one_left ?_ ?_ <;> linarith
      _ = _ := by ring
      _ ≤ _ := this.2
      _ = _ := congrArg f (by ring)

  -- Now reduce the problem to binary fractions.
  suffices ∀ n k : ℕ, k < 2 ^ n →
      k / 2 ^ n * b ≤ f (k / 2 ^ n * 2⁻¹) ∧
      (1 - k / 2 ^ n) * b + k / 2 ^ n ≤ f ((1 - k / 2 ^ n) * 2⁻¹ + k / 2 ^ n) by
    intro r hr_mem
    split_ands
    · rw [← sub_nonneg]
      refine nonneg_of_continuousOn_of_binary ?_ ?_ r hr_mem (f := fun r ↦ f (r * 2⁻¹) - r * b)
      · refine .sub (.comp hf ?_ ?_) ?_
        · exact (continuous_mul_right _).continuousOn
        · intro x hx_mem
          rw [Set.mem_Ico] at hx_mem
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
        · refine Continuous.continuousOn ?_
          exact .add (.mul (continuous_sub_left 1) continuous_const) continuous_id
        · intro x hx_mem
          rw [Set.mem_Ico] at hx_mem
          split_ands <;> linarith
        · refine Continuous.continuousOn ?_
          exact .add (.mul (continuous_sub_left 1) continuous_const) continuous_id
      intro n k hk
      rw [sub_nonneg]
      exact (this n k hk).2

  -- Combine `x ≤ f x` and the recursive specification applied to binary fractions.
  intro n k hkn
  split_ands
  · suffices b * (k / 2 ^ n) ≤ f (2⁻¹ * k / 2 ^ n) by
      convert this using 1
      · ring
      · congr 1
        ring
    calc _
    _ ≤ b * f (k / 2 ^ n) := by
      gcongr
      · linarith
      · exact lemma_5 hb hf₁ hf₂ n k hkn.le
    _ = f (k / 2 ^ (n + 1)) := (lemma_3 hf₁ n k hkn.le).symm
    _ = _ := by
      congr 1
      ring
  · suffices b + (1 - b) * (k / 2 ^ n) ≤ f (2⁻¹ + 2⁻¹ * (k / 2 ^ n)) by
      convert this using 1
      · ring
      · congr 1
        ring
    calc _
    _ ≤ b + (1 - b) * f (k / 2 ^ n) := by
      gcongr
      · linarith
      · exact lemma_5 hb hf₁ hf₂ n k hkn.le
    _ = f (↑(2 ^ n + k) / 2 ^ (n + 1)) := (lemma_4 hf₂ n k hkn.le).symm
    _ = _ := by
      congr
      calc _
      _ = 2⁻¹ + (k : ℝ) / (2 ^ (n + 1)) := by simp [add_div, pow_succ, div_mul_cancel_left₀]
      _ = _ := by ring

-- For the second part, we represent the numbers in `[0, 1)` as infinite binary expansions.
-- That is, we write `x = ∑' i, (f i).toNat * (2 ^ (i + 1) : ℝ)⁻¹`
-- where `f k = Bool.ofNat (⌊x * 2 ^ (k + 1)⌋₊ % 2)`.

-- The composition `Bool.ofNat ∘ Bool.toNat` is identity on `x < 2`.
-- This is the converse of `Bool.ofNat_toNat`.
lemma bool_toNat_ofNat_of_lt_two {x : ℕ} (hx : x < 2) : (Bool.ofNat x).toNat = x := by
  interval_cases x <;> rfl

-- Therefore, if we convert `x % 2` to `Bool` and back, we get `x % 2`.
lemma bool_toNat_ofNat_mod_two (x : ℕ) : (Bool.ofNat (x % 2)).toNat = x % 2 :=
  bool_toNat_ofNat_of_lt_two (x.mod_lt two_pos)

-- The explicit form for the `k`-th digit of `n` in base `b`.
-- This explicit form is more useful for an infinite fraction.
lemma digits_getD {b : ℕ} (hb : 1 < b) (n k : ℕ) : (Nat.digits b n).getD k 0 = n / b ^ k % b := by
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => simp
    | succ n => simp [Nat.digits_eq_cons_digits_div hb]
  | succ k IH =>
    cases lt_or_le n b with
    | inl hn =>
      cases n with
      | zero => simp
      | succ n =>
        calc _
        _ = 0 := by simp [Nat.digits_of_lt b _ _ hn]
        _ = (n + 1) / b / b ^ k % b := by simp [Nat.div_eq_of_lt hn]
        _ = _ := by rw [pow_succ', Nat.div_div_eq_div_mul]
    | inr hn =>
      calc _
      _ = (b.digits (n % b + b * (n / b))).getD (k + 1) 0 := by
        congr
        convert (Nat.div_add_mod' n b).symm using 1
        ring
      _ = n / b / b ^ k % b := by
        rw [Nat.digits_add _ hb]
        rotate_left
        · exact Nat.mod_lt n (Nat.zero_lt_of_lt hb)
        · refine Or.inr (ne_of_gt ?_)
          exact Nat.div_pos hn (Nat.zero_lt_of_lt hb)
        rw [List.getD_cons_succ]
        exact IH (n / b)
      _ = _ := by simp [pow_succ', Nat.div_div_eq_div_mul]

-- Any natural `x < b ^ n` can be represented as a sum of `n` digits, some of which may be zero.
lemma sum_digits_getD {b : ℕ} (hb : 1 < b) (x n : ℕ) (hn : x < b ^ n) :
    ∑ k ∈ Finset.range n, (Nat.digits b x).getD k 0 * b ^ k = x := by
  induction n generalizing x with
  | zero =>
    suffices x = 0 by simp [this]
    simpa using hn
  | succ n IH =>
    cases eq_or_ne x 0 with
    | inl hx => simp [hx]
    | inr hx =>
      calc _
      _ = ∑ k ∈ Finset.range n, (b.digits (x / b)).getD k 0 * b ^ (k + 1) + x % b := by
        rw [Nat.digits_eq_cons_digits_div hb hx]
        simp [Finset.sum_range_succ']
      _ = (∑ k ∈ Finset.range n, (b.digits (x / b)).getD k 0 * b ^ k) * b + x % b := by
        simp only [pow_succ, mul_assoc, Finset.sum_mul]
      _ = (x / b) * b + x % b := by
        congr
        refine IH (x / b) ?_
        refine Nat.div_lt_of_lt_mul ?_
        simpa [pow_succ'] using hn
      _ = _ := Nat.div_add_mod' x b

-- Any real in `[0, 1)` can be represented using an infinite binary expansion `f : ℕ → Bool`.
lemma exists_binary_expansion {x : ℝ} (hx : x ∈ Set.Ico 0 1) :
    ∃ (f : ℕ → Bool), HasSum (fun i ↦ (f i).toNat * (2 ^ (i + 1) : ℝ)⁻¹) x := by
  rw [Set.mem_Ico] at hx
  let f : ℕ → Bool := fun k ↦ Bool.ofNat (⌊x * 2 ^ (k + 1)⌋₊ % 2)
  use f
  rw [hasSum_iff_tendsto_nat_of_nonneg (by simp), Metric.tendsto_atTop]
  intro ε hε
  use ⌈Real.logb 2 (ε⁻¹)⌉₊
  intro n hn
  -- Replace the truncated binary expansion with `⌊x * 2 ^ n⌋₊ / 2 ^ n`.
  suffices ∑ i ∈ Finset.range n, ((f i).toNat : ℝ) * (2 ^ (i + 1))⁻¹ = (⌊x * 2 ^ n⌋₊ : ℝ) / 2 ^ n by
    rw [this, dist_comm _ x, Real.dist_eq]
    suffices |(x - ⌊x * 2 ^ n⌋₊ / 2 ^ n) * 2 ^ n| < ε * 2 ^ n by simpa [abs_mul]
    rw [sub_mul, div_mul_cancel₀ _ (by simp)]
    calc _
    _ = x * 2 ^ n - ⌊x * 2 ^ n⌋₊ := by
      refine abs_of_nonneg ?_
      rw [sub_nonneg]
      refine Nat.floor_le ?_
      simp [hx.1]
    _ < (1 : ℝ) := by
      suffices x * 2 ^ n < ⌊x * 2 ^ n⌋₊ + 1 from sub_left_lt_of_lt_add this
      exact Nat.lt_floor_add_one (x * 2 ^ n)
    _ ≤ _ := by
      rw [← inv_le_iff_one_le_mul₀' hε]
      rw [← Real.rpow_natCast, ← Real.logb_le_iff_le_rpow one_lt_two (inv_pos_of_pos hε)]
      simpa using hn
  refine eq_div_of_mul_eq (by simp) ?_
  calc _
  _ = ∑ i ∈ Finset.range n, ((f i).toNat : ℝ) * (2 ^ n / 2 ^ (i + 1)) := by
    simp only [Finset.sum_mul, mul_assoc, inv_mul_eq_div]
  _ = ∑ k ∈ Finset.range n, ↑(⌊x * 2 ^ (k + 1)⌋₊ % 2) * (2 ^ n / 2 ^ (k + 1)) := by
    simp only [f, bool_toNat_ofNat_mod_two]
  _ = ∑ k ∈ Finset.range n, ↑(⌊x * (2 ^ n / 2 ^ k)⌋₊ % 2) * 2 ^ k := by
    -- One of the sums needs to be flipped.
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    -- Use powers in `ℤ` to take advantage of negative powers.
    simp only [← zpow_natCast, ← zpow_sub₀ (two_ne_zero (α := ℝ))]
    simp only [tsub_tsub, add_comm 1]
    rw [Finset.mem_range] at hk
    simp only [← Nat.sub_add_comm hk]
    simp [hk.le]
  _ = ∑ k ∈ Finset.range n, ↑(⌊x * 2 ^ n⌋₊ / 2 ^ k % 2) * 2 ^ k := by
    simp only [← Nat.floor_div_nat]
    simp [mul_div_assoc]
  _ = ↑(∑ k ∈ Finset.range n, (Nat.digits 2 ⌊x * 2 ^ n⌋₊).getD k 0 * 2 ^ k) := by
    simp only [digits_getD one_lt_two]
    simp
  _ = (⌊x * 2 ^ n⌋₊ : ℝ) := by
    refine congrArg Nat.cast (sum_digits_getD one_lt_two _ n ?_)
    rw [Nat.floor_lt' (by simp)]
    simpa using hx.2

-- Infinite binary expansions are summable.
lemma summable_binary_expansion (a : ℕ → Bool) :
    Summable (fun i ↦ (a i).toNat * (2 ^ (i + 1) : ℝ)⁻¹) := by
  rw [← summable_mul_right_iff two_ne_zero]
  refine summable_geometric_two.of_nonneg_of_le (by simp) ?_
  intro i
  calc _
  _ = (a i).toNat * (2 ^ i : ℝ)⁻¹ := by ring
  _ ≤ _ := by simp [Bool.toNat_le]

-- Infinite binary expansions do not exceed one.
lemma binary_expansion_le_one (a : ℕ → Bool) :
    ∑' i, (a i).toNat * (2 ^ (i + 1) : ℝ)⁻¹ ≤ 1 := by
  rw [← mul_le_iff_le_one_left two_pos]
  calc _
  _ = ∑' (i : ℕ), (a i).toNat * (2 ^ i : ℝ)⁻¹ := by
    rw [← tsum_mul_right]
    exact tsum_congr fun i ↦ by ring
  _ ≤ ∑' (i : ℕ), (1 / 2 : ℝ) ^ i := by
    suffices ∀ i, (a i).toNat * (2 ^ i : ℝ)⁻¹ ≤ (1 / 2 : ℝ) ^ i by
      refine tsum_le_tsum this ?_ summable_geometric_two
      refine summable_geometric_two.of_nonneg_of_le ?_ this
      simp
    simp [Bool.toNat_le]
  _ = (2 : ℝ) := tsum_geometric_two

-- The first term can be separated from a product over `j ∈ Finset.Iio i.succ`.
-- Defined in analogy to `Finset.prod_range_succ'` and `Fin.prod_univ_succ`.
lemma fin_prod_Iio_succ_bot (n : ℕ) (f : Fin (n + 1) → ℝ) (i : Fin n) :
    ∏ j < i.succ, f j = f 0 * ∏ j < i, f j.succ := by
  have : ∏ j < i.val + 1, f j = f 0 * ∏ j < i.val, f (j + 1) := by
    simp [Nat.Iio_eq_range, Finset.prod_range_succ', mul_comm (f 0)]
  convert this
  · calc _
    _ = ∏ j ∈ (Finset.Iio i.succ).map Fin.valEmbedding, f j := by
      rw [Finset.prod_map]
      simp
    _ = _ := by simp
  · calc _
    _ = ∏ j ∈ (Finset.Iio i).map Fin.valEmbedding, f (j + 1) := by
      rw [Finset.prod_map]
      simp
    _ = _ := by simp

-- The binary expansion of a natural number using `n` bits is less than `2 ^ n`.
lemma binary_expansion_lt_two_pow (n : ℕ) (a : Fin n → Bool) :
    ∑ k, (a k).toNat * 2 ^ (n - (k + 1)) < 2 ^ n := by
  calc _
  _ ≤ ∑ k : Fin n, 2 ^ (n - (k + 1)) := Finset.sum_le_sum (by simp [Bool.toNat_le])
  _ = ∑ k ∈ Finset.range n, 2 ^ (n - (k + 1)) := by rw [Finset.sum_range]
  _ = ∑ k ∈ Finset.range n, 2 ^ (n - 1 - k) := by simp only [Nat.add_comm _ 1, Nat.sub_add_eq]
  _ = ∑ k ∈ Finset.range n, 2 ^ k := Finset.sum_range_reflect _ n
  _ < 2 ^ n := Nat.geomSum_lt (le_refl 2) (by simp)

-- When `x` is a *finite* binary expansion, `f x` is a finite sum of products.
lemma lemma_7 {f : ℝ → ℝ} {b : ℝ} (hb : b ≠ 1)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1))
    (n : ℕ) (a : Fin n → Bool) :
    f (∑ j, (a j).toNat * (2 ^ (j + 1 : ℕ))⁻¹) =
      ∑ j, (a j).toNat * (b * ∏ k ∈ Finset.Iio j, if a k then 1 - b else b) := by
  -- Before applying induction, rewrite fnite expansion as a binary fraction `k / 2 ^ n`.
  suffices f (↑(∑ j, (a j).toNat * 2 ^ (n - (j + 1))) / 2 ^ n) =
      ∑ j, (a j).toNat * (b * ∏ k ∈ Finset.Iio j, if a k then 1 - b else b) by
    convert this
    simp only [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    suffices (2 ^ (j + 1 : ℕ) : ℝ)⁻¹ = 2 ^ (n - (j + 1 : ℕ)) / 2 ^ n by simp [mul_div_assoc, this]
    simp only [← zpow_natCast]
    rw [← zpow_neg, ← zpow_sub₀ two_ne_zero]
    congr
    simp [Nat.cast_sub j.isLt]

  induction n with
  | zero =>
    suffices f 0 = 0 by simpa
    exact lemma_0 hb hf₁
  | succ n IH =>
    specialize IH (fun j ↦ a j.succ)
    -- Extract the terms dependent on `a 0` from the sum and product.
    simp only [Fin.sum_univ_succ, fin_prod_Iio_succ_bot]
    cases a 0 with
    | false =>
      calc _
      _ = f (↑(∑ k : Fin n, (a k.succ).toNat * 2 ^ (n - (k.val + 1))) / 2 ^ (n + 1)) := by simp
      _ = b * f (↑(∑ k : Fin n, (a k.succ).toNat * 2 ^ (n - (k.val + 1))) / 2 ^ n) := by
        rw [lemma_3 hf₁ n]
        exact (binary_expansion_lt_two_pow n (a ∘ Fin.succ)).le
      _ = ∑ i : Fin n, (a i.succ).toNat *
          (b * (b * ∏ k ∈ Finset.Iio i, if a k.succ then 1 - b else b)) := by
        rw [IH, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i hi ↦ by ring
      _ = _ := by simp
    | true =>
      calc _
      _ = f (↑(2 ^ n + ∑ k : Fin n, (a k.succ).toNat * 2 ^ (n - (k + 1))) / 2 ^ (n + 1)) := by
        simp
      _ = b + (1 - b) * f (↑(∑ k : Fin n, (a k.succ).toNat * 2 ^ (n - (k + 1))) / 2 ^ n) := by
        rw [lemma_4 hf₂ n]
        exact (binary_expansion_lt_two_pow n (a ∘ Fin.succ)).le
      _ = b + ∑ k : Fin n, (a k.succ).toNat *
          (b * ((1 - b) * ∏ j ∈ Finset.Iio k, if a j.succ then 1 - b else b)) := by
        rw [IH, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun i hi ↦ by ring
      _ = _ := by simp [← Fin.bot_eq_zero]

-- The *infinite* binary expansion of `f x` given the infinite binary expansion of `x`.
lemma lemma_8 {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Set.Icc 0 1))
    {b : ℝ} (hb : b ∈ Set.Ioo (1 / 2) 1)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1))
    {x : ℝ} {a : ℕ → Bool} (ha : HasSum (fun n ↦ (a n).toNat * (2 ^ (n + 1) : ℝ)⁻¹) x) :
    HasSum (fun n ↦ (a n).toNat * (b * ∏ k ∈ Finset.range n, if a k then 1 - b else b)) (f x) := by
  rw [Set.mem_Ioo] at hb
  refine (hasSum_iff_tendsto_nat_of_nonneg ?_ (f x)).mpr ?_
  · intro n
    refine mul_nonneg ?_ (mul_nonneg ?_ ?_)
    · simp
    · linarith
    · refine Finset.prod_nonneg fun k hk ↦ ?_
      split_ifs <;> linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Given `ε`, find radius `δ` within which `f y` is close to `f x`.
  rw [Metric.continuousOn_iff] at hf_cont
  have hx_mem : x ∈ Set.Icc 0 1 := by
    rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · exact ha.nonneg (by simp)
    · rw [← ha.tsum_eq]
      exact binary_expansion_le_one a
  specialize hf_cont x hx_mem ε hε
  obtain ⟨δ, hδ, hf_cont⟩ := hf_cont
  -- Find `N` such that the truncated expansion is within `δ` of `x`.
  rw [hasSum_iff_tendsto_nat_of_nonneg (by simp), Metric.tendsto_atTop] at ha
  obtain ⟨N, hN⟩ := ha δ hδ
  use N
  intro n hn
  -- Show that `f` evaluated at the truncated expansion satisfies the distance condition.
  convert hf_cont (∑ i ∈ Finset.range n, (a i).toNat * (2 ^ (i + 1))⁻¹) ?_ (hN n hn)
  · symm
    convert lemma_7 hb.2.ne hf₁ hf₂ n (fun k ↦ a k.val) using 1
    · rw [Finset.sum_range]
    · rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      congr 2
      calc _
      _ = ∏ k ∈ (Finset.Iio i).map Fin.valEmbedding, if a k then 1 - b else b := by
        simp [Nat.Iio_eq_range]
      _ = _ := by
        rw [Finset.prod_map]
        simp
  · -- Show that the truncated expansion belongs to `[0, 1]`.
    rw [Set.mem_Icc]
    split_ands
    · exact Finset.sum_nonneg (by simp)
    · refine le_trans ?_ (binary_expansion_le_one a)
      refine sum_le_tsum _ (by simp) ?_
      exact summable_binary_expansion a

-- If `a` is the infinite binary fraction of `x` and `x ≠ 0`, then some bit must be true.
lemma exists_bit_true_of_ne_zero {x : ℝ} (a : ℕ → Bool)
    (ha : HasSum (fun i ↦ (a i).toNat * (2 ^ (i + 1) : ℝ)⁻¹) x) (h : x ≠ 0) :
    ∃ n, a n = true := by
  contrapose! h
  rw [← ha.tsum_eq]
  simp [h]

-- Represent each term in the inequality as an infinite sum.
-- Use the infinite binary expansion of `x` and the infinite sum above for `f x`.
-- Prove *strict* inequality using the fact that at least one bit in `x` must be non-zero.
lemma lemma_9 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    {b c : ℝ} (hb : b = (1 + c) / (2 + c)) (hc_pos : 0 < c)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1))
    (x : ℝ) (hx : x ∈ Set.Ioo 0 1) :
    f x - x < c := by
  have hb_one : b < 1 := by rw [hb, div_lt_one] <;> linarith
  have hb_half : 1 / 2 < b := by rw [hb, div_lt_div_iff₀] <;> linarith
  -- Observe from the definition of `b` that `c = b / (1 - b) - 1`, and these are equal to the
  -- infinite geometric series `∑ n ≥ 1, b ^ n` and `∑ n ≥ 1, (1/2) ^ n`.
  have hc : c = b / (1 - b) - 1 := by
    rw [hb, one_sub_div (by linarith), div_div_div_cancel_right₀ (by linarith)]
    ring
  have h_sum_b : HasSum (fun n ↦ b ^ (n + 1)) (b / (1 - b)) := by
    rw [hasSum_nat_add_iff]
    convert hasSum_geometric_of_lt_one (by linarith) hb_one using 1
    rw [div_add' _ _ _ (by linarith)]
    simp
  have h_sum_half : HasSum (fun n ↦ (2⁻¹ : ℝ) ^ (n + 1)) 1 := by
    rw [hasSum_nat_add_iff (f := fun n ↦ 2⁻¹ ^ n)]
    simpa [one_add_one_eq_two] using hasSum_geometric_two
  -- Obtain infinite sums equal to `x` and `f x`.
  obtain ⟨a, hx_sum⟩ := exists_binary_expansion (Set.mem_Ico_of_Ioo hx)
  have hfx_sum := lemma_8 hf ⟨hb_half, hb_one⟩ hf₁ hf₂ hx_sum
  -- Replace both sides with an infinite sum.
  rw [← (hfx_sum.sub hx_sum).tsum_eq]
  rw [hc, ← (h_sum_b.sub h_sum_half).tsum_eq]

  -- It remains to prove that the left sum is (strictly) less that the right.
  -- It suffices to give some `i` such that
  -- `(a i) * (b * (∏ k ∈ Finset.range i, if a k then 1 - b else b) - 2 ^ (i + 1))`
  -- is strictly less than `b ^ (i + 1) - (1 / 2) ^ (i + 1)`.
  -- If `a i = 0`, then the left side is zero and the right side is positive.
  -- If `a i = 1`, then we need some `k < i` such that we can use `1 - b < b`.
  -- Therefore, find `k` such that `a k = 1` and use `i = k + 1`.
  rw [Set.mem_Ioo] at hx
  obtain ⟨k, hk⟩ := exists_bit_true_of_ne_zero a hx_sum hx.1.ne'
  refine tsum_lt_tsum (i := k + 1) ?_ ?_ (hfx_sum.sub hx_sum).summable
    (h_sum_b.sub h_sum_half).summable
  · intro n
    simp only [inv_pow]
    calc _
    -- Bound `b` and `1 - b` above by `b`.
    _ ≤ (a n).toNat * b ^ (n + 1) - (a n).toNat * (2 ^ (n + 1))⁻¹ := by
      refine sub_le_sub_right ?_ _
      rw [pow_succ']
      refine mul_le_mul_of_nonneg_left ?_ (by simp)
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      calc _
      _ ≤ ∏ _ ∈ Finset.range n, b := by
        refine Finset.prod_le_prod (fun i hi ↦ ?_) (fun i hi ↦ ?_) <;> split_ifs <;> linarith
      _ = _ := by simp
    -- Take out the factor of `a n`.
    _ = (a n).toNat * (b ^ (n + 1) - (2 ^ (n + 1))⁻¹) := by ring
    _ ≤ _ := by
      refine mul_le_of_le_one_left ?_ (by simp [Bool.toNat_le])
      suffices (2⁻¹ : ℝ) ^ (n + 1) ≤ b ^ (n + 1) by simpa
      gcongr
      linarith
  · simp only [inv_pow]
    cases a (k + 1) with
    | false =>
      -- The left side is zero. This case is trivial, it suffices to know that `2⁻¹ < b`.
      suffices 2⁻¹ ^ (k + 1 + 1) < b ^ (k + 1 + 1) by simpa
      gcongr
      linarith
    | true =>
      have hb_pos : 0 < b := by linarith
      suffices ((1 - b) * ∏ x ∈ Finset.range k, if a x then 1 - b else b) < b * b ^ k by
        simpa [pow_succ', Finset.range_succ, hk, hb_pos]
      refine mul_lt_mul_of_lt_of_le_of_nonneg_of_pos ?_ ?_ (by linarith) (pow_pos hb_pos k)
      · linarith
      · calc _
        _ ≤ ∏ _ ∈ .range k, b := by
          refine Finset.prod_le_prod (fun i hi ↦ ?_) (fun i hi ↦ ?_) <;> split_ifs <;> linarith
        _ = _ := by simp

theorem algebra_23856 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    {b c : ℝ} (hb : b = (1 + c) / (2 + c)) (hc : 0 < c)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    ∀ x ∈ Set.Ioo 0 1, f x - x ∈ Set.Ioo 0 c := by
  intro x hx
  rw [Set.mem_Ioo]
  refine ⟨?_, ?_⟩
  · -- For the left side, show that `f x` is greater than or equal to the piecewise linear function
    -- `(0, 0), (2⁻¹, b), (1, 1)`, which is strictly greater than `x`, for all binary rationals `x`.
    -- This extends to real `x` by continuity of `f` and density of binary rationals.
    rcases hb with rfl
    refine lemma_6 hf ?_ hf₁ hf₂ x hx
    rw [Set.mem_Ioo]
    split_ands
    · rw [div_lt_div_iff₀] <;> linarith
    · rw [div_lt_one] <;> linarith
  · -- For the right side, rewrite `x` as an infinite binary expansion and use this to obtain `f x`
    -- as an infinite sum. Compare to `c = b / (1 - b) - 1`, which is a geometric series.
    -- Show that *strict* inequality holds by the existence of a non-zero bit for `x ≠ 0`.
    exact lemma_9 hf hb hc hf₁ hf₂ x hx
