-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9z0020ueaxjchnxxp7

import Mathlib

/- $n$ is a positive integer. Try to determine how many real numbers $x$ satisfy
$1 \le x < n$ and $x^{3} - [x^{3}] = (x - [x])^{3}$. -/

-- The mapping from (z, r) to z + r is injective on the set with r in [0, 1).
lemma injOn_int_add_real_Ico :
    Set.InjOn (fun m : ℤ × ℝ ↦ m.1 + m.2) {(_, r) : ℤ × ℝ | r ∈ Set.Ico 0 1} := by
  intro u hu v hv h
  simp only [Set.mem_setOf_eq, Set.mem_Ico] at hu hv
  ext
  · simpa [Int.floor_eq_zero_iff.mpr, hu, hv] using congrArg Int.floor h
  · simpa [Int.fract_eq_self.mpr, hu, hv] using congrArg Int.fract h

-- The set of reals `x` that satisfy `p x` is equivalent to (integer, fraction) pairs `x = z + r`.
lemma lemma_1 (p : ℝ → Prop) :
    {x | p x}.ncard = {(z, r) : ℤ × ℝ | r ∈ Set.Ico 0 1 ∧ p (z + r)}.ncard := by
  calc _
  _ = ((fun m : ℤ × ℝ ↦ m.1 + m.2) '' {(z, r) : ℤ × ℝ | r ∈ Set.Ico 0 1 ∧ p (z + r)}).ncard := by
    congr
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, Prod.exists]
    constructor
    · intro hx
      use ⌊x⌋, Int.fract x
      simp [Int.fract_lt_one, hx]
    · rintro ⟨z, r, ⟨_, hx⟩, rfl⟩
      exact hx
  _ = _ := by
    refine Set.ncard_image_of_injOn ?_
    refine injOn_int_add_real_Ico.mono ?_
    exact fun m ⟨hr, _⟩ ↦ hr

-- We have `(a + r)^3 - ⌊(a + r)^3⌋ = r^3` iff `a^3 + 3 a^2 r + 3 a r^2` is an integer.
lemma lemma_2 (a : ℤ) (r : ℝ) (hr : r ∈ Set.Ico 0 1) :
    (a + r)^3 - ⌊(a + r)^3⌋ = r^3 ↔ ∃ n : ℤ, a^3 + 3*a^2*r + 3*a*r^2 = n := by
  calc _
  _ ↔ (a + r)^3 - r^3 = ⌊(a + r)^3⌋ := by rw [sub_eq_iff_eq_add, sub_eq_iff_eq_add']
  _ ↔ a^3 + 3 * a^2 * r + 3 * a * r^2 = ⌊a^3 + 3 * a^2 * r + 3 * a * r^2 + r^3⌋ := by
    refine Eq.congr ?_ ?_ <;> congr <;> ring
  _ ↔ _ := by
    generalize a ^ 3 + 3 * a ^ 2 * r + 3 * a * r ^ 2 = x
    -- The forward direction is trivial.
    refine ⟨fun h ↦ ⟨_, h⟩, ?_⟩
    intro ⟨n, hn⟩
    rw [hn]
    -- Adding `r ^ 3` to an integer will not reach the next integer.
    suffices 0 ≤ r ^ 3 ∧ r ^ 3 < 1 by simpa
    rw [Set.mem_Ico] at hr
    refine ⟨pow_nonneg ?_ 3, pow_lt_one₀ ?_ ?_ three_ne_zero⟩ <;> linarith

-- The function `r ↦ a^3 + 3 a^2 r + 3 a r^2` is strictly monotone on `0 ≤ r`.
lemma lemma_3 {a : ℤ} (ha : 1 ≤ a) :
    StrictMonoOn (fun r : ℝ ↦ a^3 + 3*a^2*r + 3*a*r^2) (Set.Ici 0) := by
  refine MonotoneOn.add_strictMono ?_ ?_
  · refine Monotone.monotoneOn ?_ _
    refine .const_add ?_ _
    refine monotone_mul_left_of_nonneg ?_
    simp [sq_nonneg]
  · intro x hx y hy hxy
    simp only
    refine (mul_lt_mul_left ?_).mpr ?_
    · simpa using ha
    · exact (sq_lt_sq₀ hx hy).mpr hxy

-- As `r` ranges on `[0, 1)`, `a^3 + 3 a^2 r + 3 a r^2` ranges on `[a^3, a^3 + 3 a^2 + 3 a)`.
-- The set of integer values in this range is `[a^3, a^3 + 3 a^2 + 3 a)`.
lemma lemma_4 {a : ℤ} (ha : 1 ≤ a) :
    Set.range Int.cast ∩ ((fun r : ℝ ↦ a^3 + 3*a^2*r + 3*a*r^2) '' Set.Ico 0 1) =
    Int.cast '' Set.Ico (a ^ 3) (a ^ 3 + 3 * a ^ 2 + 3 * a) := by
  -- Introduce `f` to simplify notation.
  let f (a : ℤ) (r : ℝ) : ℝ := a^3 + 3*a^2*r + 3*a*r^2
  have hf_mono {a : ℤ} (ha : 1 ≤ a) : StrictMonoOn (f a) (Set.Ici 0) := lemma_3 ha
  have hf_inj {a : ℤ} (ha : 1 ≤ a) : Set.InjOn (f a) (Set.Ici 0) := (hf_mono ha).injOn
  -- Further, we can establish that `r ↦ f a r` is a bijection.
  have hf_cont {a : ℤ} : Continuous (f a) := by
    unfold f
    refine .add (.add ?_ ?_) ?_
    · exact continuous_const
    · exact continuous_mul_left _
    · exact .mul continuous_const (continuous_pow 2)
  have hf_bijOn {a : ℤ} (ha : 1 ≤ a) : Set.BijOn (f a) (Set.Ico 0 1) (Set.Ico (f a 0) (f a 1)) := by
    convert Set.InjOn.bijOn_image ?_
    · refine Set.Subset.antisymm ?_ ?_
      · refine intermediate_value_Ico zero_le_one ?_
        exact hf_cont.continuousOn
      · refine StrictMonoOn.image_Ico_subset ?_
        exact (hf_mono ha).mono Set.Icc_subset_Ici_self
    · exact (hf_inj ha).mono Set.Ico_subset_Ici_self

  calc _
  -- The image of `f a` on `[0, 1)` is `[f a 0, f a 1)`.
  _ = Set.range Int.cast ∩ Set.Ico (f a 0) (f a 1) := by rw [(hf_bijOn ha).image_eq]
  _ = Set.range Int.cast ∩ Set.Ico ((a^3 : ℤ) : ℝ) (a^3 + 3*a^2 + 3*a : ℤ) := by simp [f]
  -- Obtain the set of integers within the interval.
  _ = Int.cast '' ((Int.cast : ℤ → ℝ) ⁻¹' Set.Ico ↑(a^3) ↑(a^3 + 3*a^2 + 3*a : ℤ)) :=
    Set.image_preimage_eq_range_inter.symm
  _ = _ := by simp only [Int.preimage_Ico, Int.ceil_intCast]

-- The sum of squares is a product that is divisible by 6.
-- It is easier to simplify expressions with addition only in the natural numbers.
lemma sum_range_succ_sq_mul_six (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), k^2) * 6 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [Finset.sum_range_succ, add_mul, IH]
    ring

-- The expression for the sum of squares using subtraction.
lemma sum_range_sq_mul_six (n : ℕ) :
    (∑ k in Finset.range n, k^2) * 6 = (n - 1) * n * (2 * n - 1) := by
  cases n with
  | zero => simp
  | succ n => simpa using sum_range_succ_sq_mul_six n

theorem algebra_213467 (n : ℕ) (hn : 0 < n) :
    {x : ℝ | x ∈ Set.Ico 1 ↑n ∧ x^3 - ⌊x^3⌋ = (x - ⌊x⌋)^3}.ncard = n^3 - n := by
  -- Introduce `f` to simplify notation.
  let f (a : ℤ) (r : ℝ) : ℝ := a^3 + 3*a^2*r + 3*a*r^2
  calc _
  -- Split `x` into its integer and fractional parts.
  -- The `Ico` constraint can be placed on the integer part alone.
  _ = {x : ℝ | ⌊x⌋ ∈ Set.Ico 1 (n : ℤ) ∧
      (⌊x⌋ + Int.fract x)^3 - ⌊(⌊x⌋ + Int.fract x)^3⌋ = Int.fract x^3}.ncard := by
    simp [Int.le_floor, Int.floor_lt]

  -- The number of such `x` is equal to the number of pairs `(a, r)`.
  _ = {(a, r) : ℤ × ℝ | r ∈ Set.Ico 0 1 ∧ a ∈ Set.Ico 1 (n : ℤ) ∧
      (a + r)^3 - ⌊(a + r)^3⌋ = r^3}.ncard := by
    rw [lemma_1]
    congr
    ext ⟨a, r⟩
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro hr
    simp [Int.fract_eq_self.mpr hr, Int.floor_eq_zero_iff.mpr hr]

  -- The condition on `r` is equivalent to the existence of an integer `k`.
  _ = {(a, r) : ℤ × ℝ | r ∈ Set.Ico 0 1 ∧ a ∈ Set.Ico 1 (n : ℤ) ∧ ∃ k : ℤ, f a r = k}.ncard := by
    congr
    ext ⟨a, r⟩
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro hr ha
    exact lemma_2 a r hr

  -- Replace the number of pairs `(a, r)` with the number of pairs `(a, f a r)`.
  _ = ((Function.uncurry fun a r ↦ (a, f a r)) ''
      {(a, r) : ℤ × ℝ | r ∈ Set.Ico 0 1 ∧ a ∈ Set.Ico 1 (n : ℤ) ∧ ∃ k : ℤ, f a r = k}).ncard := by
    refine (Set.ncard_image_of_injOn ?_).symm
    simp only [Set.InjOn, Prod.forall, Function.uncurry_apply_pair, Prod.mk.injEq]
    intro a₁ r₁ ⟨hr₁, ha₁, _⟩ a₂ r₂ ⟨hr₂, ha₂, _⟩ h
    refine ⟨h.1, ?_⟩
    -- Use injectivity of `r ↦ f a r` to prove `r₁ = r₂`.
    suffices Set.InjOn (fun r : ℝ ↦ f a₁ r) (Set.Ico 0 1) from this hr₁ hr₂ (h.1 ▸ h.2)
    exact ((lemma_3 ha₁.1).mono Set.Ico_subset_Ici_self).injOn

  -- Write the set of pairs as a union over `a`.
  _ = ((Function.uncurry fun a r ↦ (a, f a r)) ''
      ⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) '' {r ∈ Set.Ico 0 (1 : ℝ) | ∃ k : ℤ, f a r = k}).ncard := by
    congr
    refine congrArg _ ?_
    ext ⟨a, r⟩
    -- Re-order the conditions.
    suffices (r ∈ Set.Ico 0 1 ∧ a ∈ Set.Ico 1 ↑n ∧ ∃ k : ℤ, f a r = k) ↔
        (r ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, f a r = k) ∧ a ∈ Set.Ico 1 ↑n by simpa
    rw [and_assoc, and_congr_right_iff]
    simp [and_comm]
  -- Move the image of `f a` inside the union.
  _ = (⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      (f a '' {r ∈ Set.Ico 0 (1 : ℝ) | ∃ k : ℤ, f a r = k})).ncard := by
    simp [Set.image_iUnion, Set.image_image]
  -- Rewrite the condition as intersection with the set of integers.
  _ = (⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      (Set.range Int.cast ∩ f a '' (Set.Ico 0 (1 : ℝ)))).ncard := by
    congr
    refine Set.iUnion₂_congr fun a ha ↦ ?_
    refine congrArg _ ?_
    ext y
    -- Re-order the conditions.
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_range]
    constructor
    · exact fun ⟨r, ⟨hr, k, hk⟩, hy⟩ ↦ ⟨⟨k, hk ▸ hy⟩, ⟨r, hr, hy⟩⟩
    · exact fun ⟨⟨k, hk⟩, ⟨r, hr, hy⟩⟩ ↦ ⟨r, ⟨hr, k, hk ▸ hy⟩, hy⟩
  -- Rewrite the set of integers as the image of a finite set.
  _ = (⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      (Int.cast '' (Set.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)) : Set ℝ)).ncard := by
    congr
    refine Set.iUnion₂_congr fun a ha ↦ ?_
    refine congrArg _ ?_
    exact lemma_4 ha.1

  -- Move the image (of an injective function) outside of the union and eliminate it.
  _ = (Prod.map id (Int.cast : ℤ → ℝ) '' ⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      Set.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).ncard := by
    simp [Set.image_iUnion, Set.image_image]
  _ = (⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) '' Set.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).ncard := by
    refine Set.ncard_image_of_injective _ ?_
    rw [Prod.map_injective]
    exact ⟨Function.injective_id, Int.cast_injective⟩

  -- Switch to `Finset`.
  _ = ((Finset.Ico 1 (n : ℤ)).biUnion fun a ↦
      (Finset.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).image fun k ↦ (a, k)).toSet.ncard := by
    simp
  _ = ((Finset.Ico 1 (n : ℤ)).biUnion fun a ↦
      (Finset.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).image (a, ·)).card :=
    Set.ncard_coe_Finset _
  -- Rewrite cardinality of union as a sum of cardinalities.
  _ = ∑ a ∈ Finset.Ico 1 (n : ℤ), ((Finset.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).image (a, ·)).card := by
    rw [Finset.card_biUnion]
    intro a ha b hb hab
    suffices ∀ {s t : Finset ℤ}, Disjoint (s.image (a, ·)) (t.image (b, ·)) from this
    simp [Finset.disjoint_iff_ne, hab]
  _ = ∑ a ∈ Finset.Ico 1 (n : ℤ), (Finset.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).card := by
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    refine Finset.card_image_of_injective _ ?_
    exact Prod.mk.inj_left a

  -- Switch from `ℤ` to `ℕ` to evaluate the sum.
  _ = ∑ a ∈ Finset.Ico 1 (n : ℤ), Int.toNat (3 * a ^ 2 + 3 * a) := by simp [add_assoc]
  _ = ∑ a ∈ (Finset.Ico 1 n).map Nat.castEmbedding, Int.toNat (3 * a ^ 2 + 3 * a) := by
    congr
    refine Finset.coe_injective ?_
    simpa using (Nat.image_cast_int_Ico 1 n).symm
  _ = ∑ a ∈ Finset.Ico 1 n, (3 * a ^ 2 + 3 * a) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    calc _
    _ = Int.toNat (Nat.cast (3 * x ^ 2 + 3 * x)) := by simp
    _ = _ := Int.toNat_natCast _
  -- Include `a = 0` in the sum (without affecting the value) to obtain a sum over `range`.
  _ = ∑ a in Finset.range n, (3 * a^2 + 3 * a) := by
    refine Finset.sum_subset ?_ ?_
    · intro a
      simp
    · intro a ha ha'
      suffices a = 0 by simpa
      rw [Finset.mem_range] at ha
      rw [Finset.mem_Ico, not_and'] at ha'
      simpa using ha' ha
  -- Introduce factors of 6 and 2 to obtain integer expressions for each sum.
  _ = (∑ a in Finset.range n, (a^2 + a)) * 3 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  _ = (∑ a in Finset.range n, (a^2 + a)) * 6 / 2 := by
    rw [Nat.mul_div_assoc _ (by norm_num)]
  _ = ((∑ a in Finset.range n, a^2) * 6 + (∑ a in Finset.range n, a) * 2 * 3) / 2 := by
    simp [Finset.sum_add_distrib, add_mul, mul_assoc]
  -- Use `ring` in `ℤ` to prove that expressions are equal.
  _ = (n^3 - n) * 2 / 2 := by
    congr 1
    rw [Finset.sum_range_id_mul_two, sum_range_sq_mul_six]
    -- This is easy to prove in `ℤ` using `ring`.
    have : (n - 1) * n * (2 * n - 1) + n * (n - 1) * 3 = ((n^3 - n) * 2 : ℤ) := by ring
    rw [← @Nat.cast_inj ℤ]
    -- Provide necessary conditions for `Nat.cast_sub`.
    have h₁ : 1 ≤ n := hn
    have h₂ : 1 ≤ 2 * n := by linarith
    have h₃ : n ≤ n^3 := Nat.le_self_pow three_ne_zero n
    simpa [h₁, h₂, h₃] using this
  _ = n^3 - n := by simp
