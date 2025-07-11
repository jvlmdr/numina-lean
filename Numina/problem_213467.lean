-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9z0020ueaxjchnxxp7

import Mathlib

/- $n$ is a positive integer. Try to determine how many real numbers $x$ satisfy
$1 \le x < n$ and $x^{3} - [x^{3}] = (x - [x])^{3}$. -/

lemma injOn_int_add_real_Ico :
    Set.InjOn (fun m : ℤ × ℝ ↦ m.1 + m.2) {(_, r) : ℤ × ℝ | r ∈ Set.Ico 0 1} := by
  intro u hu v hv h
  simp only [Set.mem_setOf_eq, Set.mem_Ico] at hu hv
  ext
  · simpa [Int.floor_eq_zero_iff.mpr, hu, hv] using congrArg Int.floor h
  · simpa [Int.fract_eq_self.mpr, hu, hv] using congrArg Int.fract h

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

lemma lemma_4 {a : ℤ} (ha : 1 ≤ a) :
    (fun r : ℝ ↦ a^3 + 3*a^2*r + 3*a*r^2) ''
      {r ∈ Set.Ico 0 (1 : ℝ) | ∃ k : ℤ, a^3 + 3*a^2*r + 3*a*r^2 = k} =
    Int.cast '' Set.Ico (a ^ 3) (a ^ 3 + 3 * a ^ 2 + 3 * a) := by
  let f (a : ℤ) (r : ℝ) : ℝ := a^3 + 3*a^2*r + 3*a*r^2

  have hf_mono {a : ℤ} (ha : 1 ≤ a) : StrictMonoOn (f a) (Set.Ici 0) := lemma_3 ha
  have hf_inj {a : ℤ} (ha : 1 ≤ a) : Set.InjOn (f a) (Set.Ici 0) := (hf_mono ha).injOn

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

  calc f a '' {r ∈ Set.Ico 0 (1 : ℝ) | ∃ k : ℤ, f a r = k}
  _ = (f a '' Set.Ico 0 1) ∩ Set.range Int.cast := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_range]
    constructor
    · intro ⟨r, ⟨hr, ⟨k, hk⟩⟩, hy⟩
      refine ⟨⟨r, hr, ?_⟩, ⟨k, ?_⟩⟩
      · exact hy
      · exact hk.symm.trans hy
    · intro ⟨⟨r, hr, hy⟩, ⟨k, hk⟩⟩
      refine ⟨r, ⟨hr, ⟨k, ?_⟩⟩, ?_⟩
      · exact hy.trans hk.symm
      · exact hy
  _ = Set.Ico (f a 0) (f a 1) ∩ Set.range Int.cast := by rw [(hf_bijOn ha).image_eq]
  _ = Set.Ico ((a^3 : ℤ) : ℝ) (a^3 + 3*a^2 + 3*a : ℤ) ∩ Set.range Int.cast := by simp [f]
  _ = Int.cast '' ((Int.cast : ℤ → ℝ) ⁻¹' Set.Ico ↑(a^3) ↑(a^3 + 3*a^2 + 3*a : ℤ)) :=
    Set.image_preimage_eq_inter_range.symm
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

-- lemma sum_range_succ_mul_two (n : ℕ) :
--     (∑ k ∈ Finset.range (n + 1), k) * 2 = n * (n + 1) := by
--   rw [Finset.sum_range_id_mul_two, add_tsub_cancel_right]
--   ring

theorem algebra_213467 (n : ℕ) (hn : 0 < n) :
    {x : ℝ | x ∈ Set.Ico 1 ↑n ∧ x^3 - ⌊x^3⌋ = (x - ⌊x⌋)^3}.ncard = n^3 - n := by

  let f (a : ℤ) (r : ℝ) : ℝ := a^3 + 3*a^2*r + 3*a*r^2

  have hf_mono {a : ℤ} (ha : 1 ≤ a) : StrictMonoOn (f a) (Set.Ici 0) := lemma_3 ha
  have hf_inj {a : ℤ} (ha : 1 ≤ a) : Set.InjOn (f a) (Set.Ici 0) := (hf_mono ha).injOn

  calc _
  _ = {x : ℝ | ⌊x⌋ ∈ Set.Ico 1 (n : ℤ) ∧
      (⌊x⌋ + Int.fract x)^3 - ⌊(⌊x⌋ + Int.fract x)^3⌋ = Int.fract x^3}.ncard := by
    simp [Int.le_floor, Int.floor_lt]

  _ = {(a, r) : ℤ × ℝ | r ∈ Set.Ico 0 1 ∧ a ∈ Set.Ico 1 (n : ℤ) ∧
      (a + r)^3 - ⌊(a + r)^3⌋ = r^3}.ncard := by
    rw [lemma_1]
    congr
    ext ⟨a, r⟩
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro hr
    simp [Int.fract_eq_self.mpr hr, Int.floor_eq_zero_iff.mpr hr]

  _ = {(a, r) : ℤ × ℝ | r ∈ Set.Ico 0 1 ∧ a ∈ Set.Ico 1 (n : ℤ) ∧
      ∃ k : ℤ, a^3 + 3*a^2*r + 3*a*r^2 = k}.ncard := by
    congr
    ext ⟨a, r⟩
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro hr ha
    exact lemma_2 a r hr

  _ = (⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      {r ∈ Set.Ico 0 (1 : ℝ) | ∃ k : ℤ, a^3 + 3*a^2*r + 3*a*r^2 = k}).ncard := by
    congr
    ext ⟨a, r⟩
    simp [-Set.mem_Ico] -- TODO
    rw [and_assoc]
    refine and_congr_right' ?_
    rw [and_comm]

  _ = (⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      {r ∈ Set.Ico 0 (1 : ℝ) | ∃ k : ℤ, f a r = k}).ncard := rfl  -- TODO

  _ = ((Function.uncurry fun a r ↦ (a, f a r)) '' ⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      {r ∈ Set.Ico 0 (1 : ℝ) | ∃ k : ℤ, f a r = k}).ncard := by
    refine (Set.ncard_image_of_injOn ?_).symm
    rw [Set.InjOn]
    simp only [Prod.forall]
    simp only [Function.uncurry_apply_pair]
    simp only [Prod.mk.injEq]
    -- simp [Set.InjOn, -Set.mem_Ico]
    intro a₁ r₁ har₁ a₂ r₂ har₂ ⟨h_fst, h_snd⟩
    simp [-Set.mem_Ico] at har₁ har₂
    have ⟨⟨hr₁, _⟩, ha₁⟩ : (r₁ ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, f a₁ r₁ = ↑k) ∧ a₁ ∈ Set.Ico 1 ↑n := by
      simpa using har₁
    have ⟨⟨hr₂, _⟩, ha₂⟩ : (r₂ ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, f a₂ r₂ = ↑k) ∧ a₂ ∈ Set.Ico 1 ↑n := by
      simpa using har₂
    constructor
    · exact h_fst
    · exact (hf_inj ha₁.1).mono Set.Ico_subset_Ici_self hr₁ hr₂ (h_fst ▸ h_snd)

  _ = (⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      (f a '' {r ∈ Set.Ico 0 (1 : ℝ) | ∃ k : ℤ, f a r = k})).ncard := by
    simp [Set.image_iUnion, Set.image_image]

  _ = (⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      (Int.cast '' (Set.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)) : Set ℝ)).ncard := by
    congr
    refine Set.iUnion₂_congr fun a ha ↦ ?_
    refine congrArg _ ?_
    exact lemma_4 ha.1

  _ = (Prod.map id (Int.cast : ℤ → ℝ) '' ⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      Set.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).ncard := by
    simp [Set.image_iUnion, Set.image_image]

  _ = (⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) '' Set.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).ncard := by
    refine Set.ncard_image_of_injective _ ?_
    rw [Prod.map_injective]
    exact ⟨Function.injective_id, Int.cast_injective⟩

  _ = ((Finset.Ico 1 (n : ℤ)).biUnion fun a ↦
      (Finset.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).image fun k ↦ (a, k)).toSet.ncard := by
    simp

  _ = ((Finset.Ico 1 (n : ℤ)).biUnion fun a ↦
      (Finset.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).image (a, ·)).card :=
    Set.ncard_coe_Finset _

  _ = ∑ a ∈ Finset.Ico 1 (n : ℤ), ((Finset.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).image (a, ·)).card := by
    rw [Finset.card_biUnion]
    intro a ha b hb hab
    suffices ∀ {s t : Finset ℤ}, Disjoint (s.image (a, ·)) (t.image (b, ·)) from this
    simp [Finset.disjoint_iff_ne, hab]

  _ = ∑ a ∈ Finset.Ico 1 (n : ℤ), (Finset.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).card := by
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    refine Finset.card_image_of_injective _ ?_
    exact Prod.mk.inj_left a

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

  -- TODO: extract as lemma?
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
    -- -- This is easy to prove for `n + 1` using `ring`.
    -- have : n * (n + 1) * (2 * n + 1) + n * (n + 1) * 3 = n * (n + 1) * (n + 2) * 2 := by ring

    -- This is easy to prove in `ℤ` using `ring`.
    have : (n - 1) * n * (2 * n - 1) + n * (n - 1) * 3 = ((n^3 - n) * 2 : ℤ) := by ring
    rw [← @Nat.cast_inj ℤ]
    -- Provide necessary conditions for `Nat.cast_sub`.
    have h₁ : 1 ≤ n := hn
    have h₂ : 1 ≤ 2 * n := by linarith
    have h₃ : n ≤ n^3 := Nat.le_self_pow three_ne_zero n
    simpa [h₁, h₂, h₃] using this
  _ = n^3 - n := by simp
