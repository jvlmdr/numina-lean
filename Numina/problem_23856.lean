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


-- TODO: remove?
lemma fin_Iio_succ' {n : ℕ} (m : Fin n) :
    Finset.Iio m.succ = {0} ∪ (Finset.Iio m).map (Fin.succEmb n) := by
  ext x
  simp only [Finset.mem_Iio, Finset.mem_union, Finset.mem_singleton]
  constructor
  · intro h
    refine (eq_or_ne x 0).imp_right ?_
    intro hx
    rw [Finset.mem_map]
    use x.pred hx
    split_ands
    · simpa [Fin.pred_lt_iff hx] using h
    · simp
  · revert x
    simp

lemma fin_Ioo_zero_succ {n : ℕ} (b : Fin n) :
    Finset.Ioo 0 b.succ = Finset.map (Fin.succEmb n) (Finset.Iio b) := by
  ext x
  simp only [Finset.mem_map, Finset.mem_Iio, Fin.val_succEmb, Finset.mem_Ioo]
  constructor
  · intro ⟨hx, hxb⟩
    use x.pred hx.ne'
    simpa [Fin.pred_lt_iff hx.ne'] using hxb
  · rintro ⟨y, hyb, rfl⟩
    split_ands
    · simp
    · simpa using hyb

lemma fin_prod_Iio_succ' {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin (n + 1) → M) (b : Fin n) :
    ∏ i ∈ Finset.Iio b.succ, f i = f 0 * ∏ i ∈ Finset.Iio b, f (i.succ) := by
  calc _
  _ = ∏ i ∈ Finset.Ico 0 b.succ, f i := rfl
  _ = ∏ i ∈ insert 0 (Finset.Ioo 0 b.succ), f i := by simp
  _ = f 0 * ∏ i ∈ Finset.Ioo 0 b.succ, f i := Finset.prod_insert (by simp)
  _ = f 0 * ∏ i ∈ (Finset.Iio b).map (Fin.succEmb n), f i := by rw [fin_Ioo_zero_succ]
  _ = _ := by simp


lemma eq_on_binary {f : ℝ → ℝ} {b : ℝ} (hb : b ≠ 1)
    (hf1 : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf2 : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1))
    (n : ℕ) (a : Fin n → Fin 2) :
    f (∑ j, a j * (2 ^ (j + 1 : ℕ))⁻¹) =
      b * ∑ j, (∏ k ∈ Finset.Iio j, if a k = 0 then b else 1 - b) * a j := by
  induction n with
  | zero =>
    suffices f 0 = 0 by simpa
    -- For `x = 0`, we obtain `f 0 = b * f 0`, which implies either `f 0 = 0` or `b = 1`.
    have h_zero : b * f 0 = f 0 := by simpa using hf1 0 (by norm_num)
    rw [mul_left_eq_self₀] at h_zero
    exact h_zero.resolve_left hb

  | succ n IH =>
    -- TODO: Could use `Fin.consEquiv` here?
    -- obtain ⟨x, a⟩ : ∃ (x : Fin 2) (b : Fin n → Fin 2), Fin.cons x b = a := by apply?
    revert a
    -- Note, this may take the wrong end? Change definition to match?
    rw [← Equiv.forall_congr_right (Fin.consEquiv fun _ ↦ Fin 2)]
    simp only [Fin.consEquiv_apply, Prod.forall]
    rw [forall_comm]
    intro a

    simp [Fin.sum_univ_succ]
    simp [fin_prod_Iio_succ']

    specialize IH a

    have h_eq_half_mul : ∑ x : Fin n, a x * (2 ^ (x + 2 : ℕ) : ℝ)⁻¹ =
        2⁻¹ * ∑ x : Fin n, a x * (2 ^ (x + 1 : ℕ) : ℝ)⁻¹ := by
      sorry
    rw [h_eq_half_mul]  -- TODO: move?

    rw [Fin.forall_fin_two]

    -- TODO: non-terminal simps
    split_ands
    · simp
      rw [← hf1]
      swap
      · sorry
      congr
      simp
      rw [IH]
      rw [Finset.mul_sum]
      congr
      funext j
      rw [← mul_assoc]

    · simp
      rw [hf2]
      swap
      · sorry
      rw [← Fin.bot_eq_zero]
      simp [mul_add]
      rw [IH]
      simp only [Finset.mul_sum]
      congr
      funext i
      ring


theorem algebra_23856 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    {b c : ℝ} (hb : b = (1 + c) / (2 + c)) (hc : 0 < c)
    (hf1 : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf2 : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    ∀ x ∈ Set.Ioo 0 1, 0 < f x - x ∧ f x - x < c := by

  -- TODO: keep one of these?
  have hb_gt : 1 / 2 < b := by
    rw [hb]
    refine (div_lt_div_iff₀ two_pos ?_).mpr ?_
    · simp [add_pos, hc]
    · simp [add_mul, hc]
  have hb_two : 1 < 2 * b := (div_lt_iff₀' two_pos).mp hb_gt

  have hb_lt : b < 1 := by sorry

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
