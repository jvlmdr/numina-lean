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

lemma lemma_0 {f : ℝ → ℝ} {b : ℝ} (hb : b ≠ 1)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x) :
    f 0 = 0 := by
  have : b * f 0 = f 0 := by simpa using hf₁ 0 (by simp)
  exact eq_zero_of_mul_eq_self_left hb this

lemma lemma_0a {f : ℝ → ℝ} {b : ℝ} (hb : b ≠ 0)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    f 1 = 1 := by
  have : f 1 = b - b * f 1 + f 1 :=
    calc _
    _ = _ := hf₂ 1 (by norm_num)
    _ = b + (1 - b) * f 1 := by norm_num
    _ = _ := by ring
  have : b = b * f 1 := by simpa [sub_eq_zero]
  exact (mul_eq_left₀ hb).mp this.symm

lemma lemma_0b {f : ℝ → ℝ} {b : ℝ} (hb_zero : b ≠ 0)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    f 2⁻¹ = b := by
  simpa [lemma_0a hb_zero hf₂] using (hf₁ 2⁻¹ (by simp)).symm

lemma lemma_1a1 {f : ℝ → ℝ} {b : ℝ}
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

lemma lemma_1a2 {f : ℝ → ℝ} {b : ℝ}
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
    · refine div_le_one_of_le₀ ?_ two_pos.le
      -- This feels like it should be easier...
      -- TODO: maybe use `2 ^ n ≤ k ≤ 2 ^ (n + 1)` with subtraction?
      suffices 1 + (k / 2 ^ n : ℝ) ≤ 1 + 1 by simpa [one_add_one_eq_two]
      rw [add_le_add_iff_left]
      refine div_le_one_of_le₀ ?_ (by simp)
      simpa [← @Nat.cast_le ℝ] using hkn

lemma lemma_1b {f : ℝ → ℝ} {b : ℝ} (hb : b ∈ Set.Ioo (1 / 2) 1)
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
      exact lemma_0a (by linarith) hf₂
  | succ n IH =>
    cases lt_or_le k (2 ^ n) with
    | inl hk =>
      rw [lemma_1a1 hf₁ n k hk.le]
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
      obtain ⟨j, rfl⟩ : ∃ j, 2 ^ n + j = k := Nat.le.dest hk
      replace hkn : j ≤ 2 ^ n := by
        rw [pow_succ] at hkn
        linarith
      rw [lemma_1a2 hf₂ n j hkn]
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

-- TODO: these might be better folded into the main proof?
-- they are simple applications of lemma_1b, lemma_1a1, lemma_1a2

-- The function `f` lies above the line joining `(2⁻¹, b)` and `(1, 1)`
-- on all binary rationals in the interval `(2⁻¹, 1)`.
lemma lemma_2a {f : ℝ → ℝ} {b : ℝ} (hb : b ∈ Set.Ioo (1 / 2) 1)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1))
    (n k : ℕ) (hkn : k ≤ 2 ^ n) :
    b * (k / 2 ^ n) ≤ f (2⁻¹ * k / 2 ^ n) := by
  rw [Set.mem_Ioo] at hb
  calc b * (k / 2 ^ n)
  _ ≤ b * f (k / 2 ^ n) := by
    gcongr
    · linarith
    · exact lemma_1b hb hf₁ hf₂ n k hkn
  _ = f (k / 2 ^ (n + 1)) := (lemma_1a1 hf₁ n k hkn).symm
  _ = f (2⁻¹ * k / 2 ^ n) := by
    congr 1
    ring

-- The function `f` lies above the line joining `(2⁻¹, b)` and `(1, 1)`
-- on all binary rationals in the interval `(2⁻¹, 1)`.
lemma lemma_2b {f : ℝ → ℝ} {b : ℝ} (hb : b ∈ Set.Ioo (1 / 2) 1)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1))
    (n k : ℕ) (hkn : k ≤ 2 ^ n) :
    b + (1 - b) * (k / 2 ^ n) ≤ f (2⁻¹ + 2⁻¹ * (k / 2 ^ n)) := by
  rw [Set.mem_Ioo] at hb
  calc _
  _ ≤ b + (1 - b) * f (k / 2 ^ n) := by
    gcongr
    · linarith
    · exact lemma_1b hb hf₁ hf₂ n k hkn
  _ = f (↑(2 ^ n + k) / 2 ^ (n + 1)) := (lemma_1a2 hf₂ n k hkn).symm
  _ = f (2⁻¹ + 2⁻¹ * (k / 2 ^ n)) := by
    congr
    calc _
    _ = 2⁻¹ + (k : ℝ) / (2 ^ (n + 1)) := by simp [add_div, pow_succ, div_mul_cancel_left₀]
    _ = _ := by ring

theorem algebra_23856 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    {b c : ℝ} (hb : b = (1 + c) / (2 + c)) (hc : 0 < c)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    ∀ x ∈ Set.Ioo 0 1, f x - x ∈ Set.Ioo 0 c := by

  have hb_one : b < 1 := by
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

  have hf_zero : f 0 = 0 := lemma_0 (by linarith) hf₁
  have hf_one : f 1 = 1 := lemma_0a (by linarith) hf₂
  have hf_half : f 2⁻¹ = b := lemma_0b (by linarith) hf₁ hf₂

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
        -- wait until form of induction is finalized
        · sorry
        · intro x hx_mem
          simp at hr_mem hx_mem  -- TODO
          split_ands <;> linarith
        · sorry
      intro n k hk
      rw [sub_nonneg]
      exact (this n k hk).2

  -- Use the result from the induction.
  intro n k hkn
  split_ands
  · convert lemma_2a ⟨hb_half, hb_one⟩ hf₁ hf₂ n k hkn.le using 1
    · ring
    · congr 1
      ring
  · convert lemma_2b ⟨hb_half, hb_one⟩ hf₁ hf₂ n k hkn.le using 1
    · ring
    · congr 1
      ring
