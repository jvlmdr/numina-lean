-- https://cloud.kili-technology.com/label/projects/label/cmauuk3x300041rayopcw3mue

import Mathlib

open Filter

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


lemma toNat_ofNat_of_lt_two {x : ℕ} (hx : x < 2) :
    (Bool.ofNat x).toNat = x := by
  interval_cases x <;> rfl

lemma toNat_ofNat_mod_two (x : ℕ) :
    (Bool.ofNat (x % 2)).toNat = x % 2 :=
  toNat_ofNat_of_lt_two (x.mod_lt two_pos)


-- For any `x < b ^ n`, we can
-- TODO: Does this not exist somewhere in Mathlib? Not from Nat.digits? Maybe with List.getD?
lemma sum_div_pow_mod_mul_pow (b : ℕ) (n : ℕ) :
    ∀ x < b ^ n, ∑ k ∈ Finset.range n, x / b ^ k % b * b ^ k = x := by
  induction n with
  | zero => simp
  | succ n IH =>
    intro x hx
    specialize IH (x / b) (by
      refine Nat.div_lt_of_lt_mul ?_
      simpa [Nat.pow_succ'] using hx)
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.div_one, mul_one]  -- TODO?
    convert Nat.div_add_mod' x b using 2
    convert congrArg (· * b) IH
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp only [Nat.div_div_eq_div_mul, Nat.pow_succ, mul_assoc]
    congr 3
    ring

-- -- For `x` in `[0, 1)`, we can obtain `
-- -- This is useful for approximating `x` with a
-- -- TODO: write as `⌊x * 2 ^ n⌋₊ / 2 ^ n` with inverse powers? or build that on this?
-- example {x : ℝ} (hx : x ∈ Set.Ico 0 1) (n : ℕ) :
--     ∑ i ∈ Finset.range n, (⌊x * 2 ^ (i + 1)⌋₊ % 2) * 2 ^ (n - (i + 1)) =
--       ⌊x * 2 ^ n⌋₊ := by
--   rw [Set.mem_Ico] at hx
--   -- TODO: clean up
--   have := sum_div_pow_mod_mul_pow 2 n ⌊x * 2 ^ n⌋₊ (by
--     rw [← @Nat.cast_lt ℝ]
--     calc _
--     _ ≤ x * 2 ^ n := Nat.floor_le (by simpa using hx.1)
--     _ < _ := by simpa using hx.2)
--   convert this using 1
--   conv => rhs; rw [← Finset.sum_range_reflect]  -- TODO
--   refine Finset.sum_congr rfl fun k hk ↦ ?_
--   rw [Finset.mem_range] at hk
--   have h_sub_sub : n - 1 - k = n - (k + 1) := by rw [add_comm, Nat.sub_add_eq]
--   rw [h_sub_sub]
--   congr
--   rw [← Nat.floor_div_nat]
--   simp [pow_sub₀ (2 : ℝ) two_ne_zero hk, div_mul_eq_div_div]

-- The approximation `⌊x * b ^ n⌋₊ / b ^ n` for `x ∈ [0, 1)` as a sum of fractional digits.
lemma sum_mul_pow_inv_eq_floor_div_pow (b : ℕ) (hb : 1 < b) (n : ℕ) (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
    ∑ i ∈ Finset.range n, (⌊x * b ^ (i + 1)⌋₊ % b : ℕ) * (b ^ (i + 1) : ℝ)⁻¹ =
      (⌊x * b ^ n⌋₊ / b ^ n : ℝ) := by
  rw [Set.mem_Ico] at hx
  have hb_pos : 0 < b := Nat.zero_lt_of_lt hb
  have hb_zero : b ≠ 0 := Nat.not_eq_zero_of_lt hb
  rw [eq_div_iff (by simp [hb_zero])]
  -- Move from `ℝ` back to `ℕ`.
  -- Replace `b ^ n * (b ^ (i + 1))⁻¹` with `b ^ (n - (i + 1))`.
  suffices ∑ i ∈ Finset.range n, ⌊x * b ^ (i + 1)⌋₊ % b * b ^ (n - (i + 1)) = ⌊x * b ^ n⌋₊ by
    convert congrArg (Nat.cast : ℕ → ℝ) this using 1
    simp only [Finset.sum_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    rw [pow_sub₀ _ (by simpa) (Nat.add_one_le_of_lt hi)]
    ring
  convert sum_div_pow_mod_mul_pow b n ⌊x * b ^ n⌋₊ ?_ using 1
  swap
  · rw [← @Nat.cast_lt ℝ]
    calc _
    _ ≤ x * b ^ n := by
      refine Nat.floor_le ?_
      simpa [hb_pos] using hx.1
    _ < _ := by
      simpa [hb_pos] using hx.2
  symm
  -- Flip the sum such that they both start with the most significant bit.
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  -- Replace `n - 1 - k` with `n - (k + 1)`.
  rw [Nat.sub_sub, add_comm 1 k]
  congr
  -- Move the division (with truncation) inside the floor.
  rw [← Nat.floor_div_nat]
  congr
  simp only [Nat.cast_pow]
  -- Cancel the `b ^ n` terms.
  rw [pow_sub₀ _ (by simpa using hb_zero) (Nat.add_one_le_of_lt hk)]
  rw [div_mul_eq_div_div]
  simp [hb_zero]


-- For any real in `[0, 1)`, there exists a binary fraction defined by a function `ℕ → Bool`.
-- We use the "exists" form to keep the notation succinct without introducing a definition.
-- Note: This could be generalized to arbitrary base `b` using `Fin b` instead of `Bool`.
lemma exists_binary_fraction {x : ℝ} (hx : x ∈ Set.Ico 0 1) :
    ∃ (f : ℕ → Bool), HasSum (fun i ↦ (f i).toNat * (2 ^ (i + 1 : ℕ) : ℝ)⁻¹) x := by
  let f : ℕ → Bool := fun k ↦ Bool.ofNat (⌊x * 2 ^ (k + 1)⌋₊ % 2)
  use f
  rw [hasSum_iff_tendsto_nat_of_nonneg (by simp), Metric.tendsto_atTop]
  intro ε hε
  -- Specify `n` based on `ε`.
  use ⌈Real.logb 2 (ε⁻¹)⌉₊
  intro n hn
  rw [dist_comm, Real.dist_eq]
  calc _
  _ = |x - ⌊x * 2 ^ n⌋₊ / 2 ^ n| := by
    congr
    unfold f
    -- Replace `toNat (ofNat (x % 2))` with `x % 2`.
    simp only [toNat_ofNat_mod_two]
    simpa using sum_mul_pow_inv_eq_floor_div_pow 2 one_lt_two n x hx
  _ = |(x * 2 ^ n - ⌊x * 2 ^ n⌋₊)| / 2 ^ n := by simp [sub_div', abs_div]
  _ < 1 / 2 ^ n := by
    -- Remove the constant factor of `1 / 2 ^ n` from both sides.
    rw [div_lt_div_iff_of_pos_right (by simp)]
    calc _
    _ = |Int.fract (x * 2 ^ n)| := by
      congr
      refine natCast_floor_eq_intCast_floor ?_
      rw [Set.mem_Ico] at hx
      simpa using hx.1
    _ = Int.fract (x * 2 ^ n) := by simp [abs_of_nonneg]
    _ < 1 := Int.fract_lt_one _
  _ ≤ ε := by
    suffices ε⁻¹ ≤ 2 ^ (n : ℝ) by simpa [inv_le_comm₀, hε]
    rw [← Real.logb_le_logb one_lt_two (by simpa) (by simp)]
    rw [Real.logb_rpow two_pos (by simp)]
    simpa using hn



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

  rw [Real.dist_eq]
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


-- TODO: if `Ico` suffices, the solution is cleaner.
-- If we do really need this, can we implement it using the above?
-- That is, find a number in `[0, 1)` which is at most `ε / 2` away, then apply the above.
-- It feels ugly to scale by `n / (n + m)`.
-- But then how?
-- Round towards `1/2`?
-- subtract `ε/2` and clip at 0? or just clip at `1 - ε/2`?

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


example {n : ℕ} (a : Fin n → Bool) :
    (∑ i, (a i).toNat * 2 ^ i.rev.val : ℝ) / (2 ^ n : ℝ) =
      ∑ i, (a i).toNat * (2 ^ (i.val + 1) : ℝ)⁻¹ := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_div_assoc]
  congr
  rw [Fin.val_rev, pow_sub₀ (2 : ℝ) two_ne_zero j.prop]
  simp


-- Express a binary fraction as a sum of inverse powers.
lemma sum_mul_two_pow_div_two_pow {n : ℕ} (a : Fin n → Fin 2) :
    (∑ i, a i * 2 ^ (i.rev : ℕ) : ℝ) / (2 ^ n) = ∑ i, a i * (2 ^ (i + 1 : ℕ) : ℝ)⁻¹ := by
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mul_div_assoc]
  congr
  rw [Fin.val_rev, pow_sub₀ (2 : ℝ) two_ne_zero j.prop]
  simp


-- Note: We use `Fin 2` rather than `Bool` to avoid the need for `toNat` everywhere.
lemma eq_on_finite_binary' {f : ℝ → ℝ} {b : ℝ} (hb : b ≠ 1)
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

    have h_eq_half_mul : ∑ x : Fin n, a x * (2 ^ (x + 2 : ℕ) : ℝ)⁻¹ =
        2⁻¹ * ∑ x : Fin n, a x * (2 ^ (x + 1 : ℕ) : ℝ)⁻¹ := by
      simp [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring

    rw [h_eq_half_mul]  -- TODO: move? use calc?

    rw [Fin.forall_fin_two]

    -- TODO: extract as lemma?
    have h_sum_mem_Icc : ∑ x, a x * (2 ^ (x + 1 : ℕ) : ℝ)⁻¹ ∈ Set.Icc 0 1 := by
      -- TODO: depends on form that we will use...
      sorry

    -- TODO: non-terminal simps
    split_ands
    · simp
      rw [← hf1]
      swap
      · suffices ∑ x, a x * (2 ^ (x + 1 : ℕ) : ℝ)⁻¹ ∈ Set.Icc 0 1 by simpa
        -- Add as lemma? Relate to BitVec?
        exact h_sum_mem_Icc
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
      · -- TODO: better to use (pre)image of `fun x ↦ 2⁻¹ * (1 + x)`?
        -- We have `Set.image_mul_left_Icc` etc.
        suffices 2⁻¹ * (1 + ∑ x, a x * (2 ^ (x + 1 : ℕ) : ℝ)⁻¹) ∈ Set.Icc 2⁻¹ 1 by simpa [mul_add]
        suffices 1 + ∑ x, a x * (2 ^ (x + 1 : ℕ) : ℝ)⁻¹ ∈ Set.Icc 1 2 by
          simpa [inv_mul_le_iff₀ (two_pos : 0 < (2 : ℝ))]
        suffices ∑ x, a x * (2 ^ (x + 1 : ℕ) : ℝ)⁻¹ ∈ Set.Icc 0 (2 - 1) by
          simpa [le_sub_iff_add_le']
        convert h_sum_mem_Icc
        norm_num

      rw [← Fin.bot_eq_zero]
      simp [mul_add]
      rw [IH]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring

lemma eq_on_finite_binary {f : ℝ → ℝ} {b : ℝ} (hb : b ≠ 1)
    (hf1 : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf2 : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1))
    (n : ℕ) (a : Fin n → Bool) :
    f (∑ j, (a j).toNat * (2 ^ (j + 1 : ℕ))⁻¹) =
      ∑ i, b * (a i).toNat * ∏ k ∈ Finset.Iio i, if a k then 1 - b else b := by
  sorry



-- TODO: Doesn't this exist in standard library?
lemma ite_elim {α : Type*} (p : α → Prop) {q : Prop} [Decidable q] {x y : α} (hx : p x) (hy : p y) :
    p (if q then x else y) := by
  cases (em q) with
  | inl hq => simpa [hq]
  | inr hq => simpa [hq]


-- If `a` is the binary expansion of `x`, then we can express `f x` as a series of products.
lemma hasSum_binary_apply_of_hasSum_binary {f : ℝ → ℝ} (h_cont : Continuous f)
    {b : ℝ} (hb : b ∈ Set.Ioo (2⁻¹) 1)
    (hf1 : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf2 : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1))
    {x : ℝ} {a : ℕ → Bool}
    (ha : HasSum (fun n ↦ (a n).toNat * (2 ^ (n + 1) : ℝ)⁻¹) x) :
    HasSum (fun n ↦ b * (a n).toNat * ∏ k ∈ Finset.range n, if a k then 1 - b else b) (f x) := by
  rw [Set.mem_Ioo] at hb
  refine (hasSum_iff_tendsto_nat_of_nonneg ?_ (f x)).mpr ?_
  · intro n
    refine mul_nonneg ?_ ?_
    · refine mul_nonneg ?_ ?_ <;> linarith
    · refine Finset.prod_nonneg fun k hk ↦ ?_
      refine ite_elim (0 ≤ ·) ?_ ?_ <;> linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Given the `ε` for `f x`, we need to determine `ε'` for x. This will provide `N`.
  rw [hasSum_iff_tendsto_nat_of_nonneg (by simp), Metric.tendsto_atTop] at ha
  -- We need to obtain `N` such that `∑ n < N, v n = f (∑ n < N, u n)` is close to `f x`.
  rw [Metric.continuous_iff] at h_cont
  specialize h_cont x ε hε
  obtain ⟨δ, hδ, h_cont⟩ := h_cont
  specialize ha δ hδ
  obtain ⟨N, hN⟩ := ha
  use N
  intro n hn
  specialize hN n hn
  convert h_cont (∑ i ∈ Finset.range n, (a i).toNat * (2 ^ (i + 1))⁻¹) hN
  · symm
    convert eq_on_finite_binary hb.2.ne hf1 hf2 n (fun k ↦ a k.val) using 1
    · rw [Finset.sum_range]
    · rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      congr 1
      calc _
      -- Rewrite product on `Fin n` as a product on `Finset.map`.
      _ = ∏ k ∈ (Finset.Iio i).map Fin.valEmbedding, if a k then 1 - b else b := by
        simp [Nat.Iio_eq_range]
      _ = _ := by
        rw [Finset.prod_map]
        simp


lemma hasSum {f : ℝ → ℝ} {b : ℝ} (hb : b ∈ Set.Ioo (2⁻¹) 1)
    (hf1 : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf2 : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1))
    (x : ℝ) (a : ℕ → Bool)
    (ha : HasSum (fun i ↦ (a i).toNat * (2 ^ (i + 1 : ℕ) : ℝ)⁻¹) x) :
    HasSum (fun j ↦ b * (∏ k ∈ Finset.Iio j, if a k = false then b else 1 - b) * (a j).toNat)
      (f x) := by
  simp only [Set.mem_Ioo] at hb
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  swap
  · intro i
    refine mul_nonneg (mul_nonneg ?_ ?_) (Nat.cast_nonneg _)
    · linarith
    · refine Finset.prod_nonneg fun k hk ↦ ?_
      -- rw [apply_ite (f := fun x : ℝ ↦ 0 ≤ x)]
      -- rw [ite_prop_iff_or]
      -- refine (em (a k = false)).imp ?_ ?_
      refine ite_elim _ ?_ ?_ <;> linarith

  rw [hasSum_iff_tendsto_nat_of_nonneg (by simp)] at ha

  rw [Metric.tendsto_atTop]
  rw [Metric.tendsto_atTop] at ha

  intro ε hε
  specialize ha ε hε
  -- Not sure if we can bound this?
  -- Perhaps, since it's bounded by a geometric series?
  -- Seems like way too much work though.

  sorry

-- def bitVec_fin_equiv (n : ℕ) : BitVec n ≃ (Fin n → Bool) where
--   toFun := BitVec.getLsb'
--   -- invFun f := (BitVec.ofBoolListLE ((List.finRange n).map f)).cast (by simp)
--   invFun f := Nat.ofDigits 2 ((List.finRange n).map fun i ↦ (f i).toNat)
--   left_inv := by
--     intro x
--     simp
--     sorry
--   right_inv := by
--     intro x
--     simp
--     sorry


-- lemma exists_bitVec_iff_exists_fin (n : ℕ) (p : (Fin n → Bool) → Prop) :
--     (∃ x : BitVec n, p x.getLsb') ↔ ∃ f : Fin n → Bool, p f := by
--   refine ⟨fun ⟨x, hx⟩ ↦ ⟨x.getLsb', hx⟩, ?_⟩
--   intro ⟨a, ha⟩

--   use ∑ i, (a i).toNat * 2 ^ i.val
--   simp
--   sorry


-- Note: We use `getMsbD` instead of `getMsb'` as it includes e.g. `getMsbD_cons_succ`.
lemma sum_getMsbD_toNat_mul_two_pow {n : ℕ} (x : BitVec n) :
    ∑ i : Fin n, (x.getMsbD i).toNat * 2 ^ i.rev.val = x.toNat := by
  induction n with
  | zero => simp [BitVec.of_length_zero]
  | succ n IH =>
    -- Replace `x` with `b.cons a` where `a = x.msb` and `b = x.setWidth n` (like tail).
    obtain ⟨a, b, rfl⟩ : ∃ (a : Bool) (b : BitVec n), b.cons a = x :=
      ⟨x.msb, x.setWidth n, x.cons_msb_setWidth⟩
    calc _
    -- Split `a` from the sum and simplify both terms.
    _ = a.toNat * 2 ^ n + ∑ x : Fin n, (b.getMsbD x).toNat * 2 ^ (x.rev : ℕ) := by
      simp [Fin.sum_univ_succ]
    -- Apply the hypothesis from induction.
    _ = a.toNat * 2 ^ n + b.toNat := by rw [IH]
    -- Show equal to `(b.cons a).toNat`.
    _ = _ := by
      rw [BitVec.toNat_cons']
      simp [Nat.shiftLeft_eq]


-- If `a` is the binary fraction of `x ≠ 0`, then some bit must be true.
lemma exists_bit_true_of_ne_zero {x : ℝ} (a : ℕ → Bool)
    (ha : HasSum (fun i ↦ (a i).toNat * (2 ^ (i + 1) : ℝ)⁻¹) x) (h : x ≠ 0) :
    ∃ n, a n := by
  contrapose! h
  simpa [h] using ha.tsum_eq.symm


theorem algebra_23856 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    {b c : ℝ} (hb : b = (1 + c) / (2 + c)) (hc : 0 < c)
    (hf1 : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf2 : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    ∀ x ∈ Set.Ioo 0 1, 0 < f x - x ∧ f x - x < c := by

  have hb_lt : b < 1 := by
    rw [hb]
    refine (div_lt_one ?_).mpr ?_
    · simp [add_pos, hc]
    · simp
  -- TODO: keep one of these?
  have hb_gt : 1 / 2 < b := by
    rw [hb]
    refine (div_lt_div_iff₀ two_pos ?_).mpr ?_
    · simp [add_pos, hc]
    · simp [add_mul, hc]
  have hb_two : 1 < 2 * b := (div_lt_iff₀' two_pos).mp hb_gt

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

  · -- Need to write as a `≤` condition to use density of binary fractions.
    -- However, the strictness comes from the fact that one of the `a j` is not zero since `x ≠ 0`?
    -- Not sure how to express this.

    -- Rewrite the right side as an infinite sum.
    suffices f x - x < ∑' n : ℕ, (b ^ (n + 1) - 2⁻¹ ^ (n + 1)) by
      refine lt_of_lt_of_eq this ?_
      calc _
      _ = b / (1 - b) - 1 := by
        refine (HasSum.sub ?_ ?_).tsum_eq
        · rw [hasSum_nat_add_iff]
          convert hasSum_geometric_of_lt_one (by linarith) hb_lt using 1
          rw [div_add' _ _ _ (by linarith)]
          simp
        · rw [hasSum_nat_add_iff (f := fun n ↦ 2⁻¹ ^ n)]
          simpa [one_add_one_eq_two] using hasSum_geometric_two
      _ = c := by
        rw [hb, one_sub_div (by linarith), div_div_div_cancel_right₀ (by linarith)]
        ring

    -- Now we need to show that `f x` tends to a sum as well?
    -- However, this requires showing that the function is `Summable`.

    -- Maybe we can obtain this easily by bounding the series by a geometric series?

    let v (a : ℕ → Bool) (j : ℕ) : ℝ :=
        (a j).toNat * (b * (∏ k in Finset.range j, if a k then 1 - b else b))


    have hv_summable (a : ℕ → Bool) : Summable (v a) := by
      refine Summable.of_nonneg_of_le (f := fun n ↦ b ^ (n + 1)) ?_ ?_ ?_
      · intro j
        refine mul_nonneg (by simp) (mul_nonneg (by linarith) ?_)
        refine Finset.prod_nonneg fun k hk ↦ ite_elim _ ?_ ?_ <;> linarith
      · intro j
        unfold v
        calc _
        _ ≤ b * ∏ k in Finset.range j, if a k then 1 - b else b := by
          refine mul_le_of_le_one_left ?_ ?_
          · refine mul_nonneg (by linarith) ?_
            refine Finset.prod_nonneg fun k hk ↦ ite_elim _ ?_ ?_ <;> linarith
          · simp [Bool.toNat_le]
        _ ≤ b * ∏ k in Finset.range j, b := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          refine Finset.prod_le_prod ?_ ?_
          · refine fun k hk ↦ ite_elim _ ?_ ?_ <;> linarith  -- TODO: written three times..?
          · refine fun k hk ↦ ?_
            refine ite_elim (p := (· ≤ b)) (by linarith) (by simp)
        _ = _ := by simp [pow_succ']
      ·
        -- refine summable_geometric_of_lt_one (by linarith) ?_
        sorry

    obtain ⟨a, ha⟩ := exists_binary_fraction (Set.mem_Ico_of_Ioo hx)

    have hv : HasSum (v a) (f x) := by
      -- TODO if useful
      -- Could be tricky to handle infiniteness?
      unfold v
      rw [hasSum_iff_tendsto_nat_of_nonneg]
      rw [Metric.tendsto_atTop]
      intro ε hε
      -- The remainder is less than `b ^ N / (1 - b) < 2 * b ^ N`.
      sorry

    -- Let `u n` be the series of binary fractions that approximates `x`.
    -- TODO: Generalize to `u a n`?
    let u : ℕ → ℝ := fun n ↦ (a n).toNat * (2 ^ (n + 1 : ℕ) : ℝ)⁻¹

    have hu : ∑' k, u k = x := ha.tsum_eq

    have ha_zero (hx : x ≠ 0) : ∃ n, a n := by
      contrapose! hx with h
      rw [← ha.tsum_eq]
      simp [h]

    have : ∑' n, (v a n - u n) < ∑' n, (b ^ (n + 1) - 2⁻¹ ^ (n + 1)) := by
      suffices ∃ n, v a n - u n < b ^ (n + 1) - 2⁻¹ ^ (n + 1) by
        rcases this with ⟨n, hn⟩
        refine tsum_lt_tsum ?_ hn ?_ ?_
        · -- Already proved somewhere?
          sorry
        · refine Summable.sub ?_ ?_
          · sorry
          · sorry
        · refine Summable.sub ?_ ?_
          · sorry
          · sorry
      -- Since `x ≠ 0`, there must be some `n` such that `a n ≠ 0`.
      specialize ha_zero hx.1.ne'
      refine ha_zero.imp fun m hm ↦ ?_
      unfold v u
      rw [← mul_sub]
      simp [hm]

      sorry


    -- rcases ha.tsum_eq with rfl


    suffices ∀ᶠ n in atTop, f (∑ k in Finset.range n, z k) - ∑ k in Finset.range n, z k < c by
      rw [eventually_atTop] at this
      rcases this with ⟨N, hN⟩
      sorry

    -- have : HasSum (fun i ↦ (a i).toNat * (2 ^ (i + 1 : ℕ) : ℝ)⁻¹) x := by sorry

    -- have := ha.tendsto_sum_nat

    -- have : ∃ N, ∀ n ≥ N, f () - () < c := by
    --   sorry

    rcases this with rfl

    sorry

    -- suffices f x - x ≤ ∑' n : ℕ, (b⁻¹ ^ n - 2⁻¹ ^ n) by
    --   sorry

    -- suffices ∀ (n : ℕ) (a : Fin n → Fin 2),
    --     (fun x ↦ f x - x) (∑ j, a j * (2 ^ (j + 1 : ℕ) : ℝ)⁻¹) - c < 0 by
    --   sorry
    -- intro k a
    -- rw [sub_neg]

    -- calc _
    -- _ ≤
    -- _ < b / (1 - b) - 1 := by

    --   sorry

    -- _ = c := by
    --   rw [hb, one_sub_div (by linarith), div_div_div_cancel_right₀ (by linarith)]
    --   ring
