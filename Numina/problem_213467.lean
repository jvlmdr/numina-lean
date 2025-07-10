-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9z0020ueaxjchnxxp7

import Mathlib

/- $n$ is a positive integer. Try to determine how many real numbers $x$ satisfy
$1 \le x < n$ and $x^{3} - [x^{3}] = (x - [x])^{3}$. -/

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

lemma sum_range_sq (n : ℕ) :
    ∑ k ∈ Finset.range n, k^2 = (n - 1) * n * (2 * n - 1) / 6 :=
  Nat.eq_div_of_mul_eq_left (by norm_num) (sum_range_sq_mul_six n)

lemma sum_range_succ_mul_two (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), k) * 2 = n * (n + 1) := by
  rw [Finset.sum_range_id_mul_two, add_tsub_cancel_right]
  ring

lemma lemma_1 (p : ℝ → Prop) : (∃ x, p x) ↔ (∃ (a : ℤ) (r : ℝ), r ∈ Set.Ico 0 1 ∧ p (a + r)) := by
  calc _
  _ ↔ ∃ (x : ℝ), (∃ (a : ℤ) (r : ℝ), a + r = x ∧ r ∈ Set.Ico 0 1) ∧ p x := by
    refine exists_congr fun x ↦ ?_
    rw [iff_and_self]
    intro hx
    use ⌊x⌋, Int.fract x
    simp [Int.fract_lt_one]
  _ ↔ ∃ (x : ℝ) (a : ℤ) (r : ℝ), (a + r = x ∧ r ∈ Set.Ico 0 1) ∧ p x := by simp
  _ ↔ ∃ (x : ℝ) (a : ℤ) (r : ℝ), a + r = x ∧ r ∈ Set.Ico 0 1 ∧ p x := by simp [and_assoc]
  _ ↔ ∃ (a : ℤ) (r : ℝ) (x : ℝ), a + r = x ∧ r ∈ Set.Ico 0 1 ∧ p x := by
    rw [exists_comm]
    refine exists_congr fun a ↦ ?_
    rw [exists_comm]
  _ ↔ _ := by simp


lemma injOn_int_add_real_Ico :
    Set.InjOn (fun m : ℤ × ℝ ↦ m.1 + m.2) {(_, r) : ℤ × ℝ | r ∈ Set.Ico 0 1} := by
  intro u hu v hv h
  simp only [Set.mem_setOf_eq, Set.mem_Ico] at hu hv
  ext
  · simpa [Int.floor_eq_zero_iff.mpr, hu, hv] using congrArg Int.floor h
  · simpa [Int.fract_eq_self.mpr, hu, hv] using congrArg Int.fract h

-- TODO: keep? remove?
lemma injOn_nat_add_real_Ico :
    Set.InjOn (fun m : ℕ × ℝ ↦ m.1 + m.2) {(_, r) : ℕ × ℝ | r ∈ Set.Ico 0 1} := by
  intro u hu v hv h
  simp only [Set.mem_setOf_eq, Set.mem_Ico] at hu hv
  ext
  · simpa [Int.floor_eq_zero_iff.mpr, hu, hv] using congrArg Int.floor h
  · simpa [Int.fract_eq_self.mpr, hu, hv] using congrArg Int.fract h

lemma lemma_1' (p : ℝ → Prop) :
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

-- -- The number of integers/nats in the range
-- lemma lemma_2 (a : ℕ) :
--     {n : ℕ | ∃ r ∈ Set.Ico 0 (1 : ℝ), a^3 + 3*a^2 * r + 3 * a * r^2 = n}.ncard =
--       3 * a^2 + 3 * a := by
--   calc _
--   _ = (Finset.Ico (a^3) (a^3 + 3*a^2 + 3 * a)).card := by
--     sorry
--   _ = _ := by simp [add_assoc]

lemma preimage_natCast_Ico (a b : ℕ) : Nat.cast ⁻¹' Set.Ico (a : ℝ) (b : ℝ) = Set.Ico a b := by
  simp

example (a b : ℕ) : Set.Ico (a : ℝ) (b : ℝ) ∩ Set.range Nat.cast = Nat.cast '' Set.Ico a b := by
  have := Set.image_preimage_eq_inter_range (f := (Nat.cast : ℕ → ℝ)) (t := Set.Ico (a : ℝ) (b : ℝ))
  rw [← this]
  refine congrArg _ ?_
  simp

lemma lemma_3 (a : ℕ) (r : ℝ) (hr : r ∈ Set.Ico 0 1) :
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

lemma lemma_3' (a : ℤ) (r : ℝ) (hr : r ∈ Set.Ico 0 1) :
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


lemma lemma_4 (a : ℤ) :
    {r : ℝ | r ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a^3 + 3*a^2*r + 3*a*r^2 = k} =
    Int.cast '' (Set.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)) := by
  sorry


theorem algebra_213467 (n : ℕ) (hn : 0 < n) :
    {x : ℝ | x ∈ Set.Ico 1 ↑n ∧ x^3 - ⌊x^3⌋ = (x - ⌊x⌋)^3}.ncard = n^3 - n := by

  calc _
  _ = {x : ℝ | ⌊x⌋ ∈ Set.Ico 1 (n : ℤ) ∧
      (⌊x⌋ + Int.fract x)^3 - ⌊(⌊x⌋ + Int.fract x)^3⌋ = Int.fract x^3}.ncard := by
    simp [Int.le_floor, Int.floor_lt]

  _ = {(a, r) : ℤ × ℝ | r ∈ Set.Ico 0 1 ∧ a ∈ Set.Ico 1 (n : ℤ) ∧
      (a + r)^3 - ⌊(a + r)^3⌋ = r^3}.ncard := by
    rw [lemma_1']
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
    exact lemma_3' a r hr

  _ = (⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      {r : ℝ | r ∈ Set.Ico 0 1 ∧ ∃ k : ℤ, a^3 + 3*a^2*r + 3*a*r^2 = k}).ncard := by
    congr
    ext ⟨a, r⟩
    simp [-Set.mem_Ico]
    -- just reordering
    sorry

  _ = (⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) ''
      (Int.cast '' Set.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a) : Set ℝ)).ncard := by
    simp only [lemma_4]

  _ = (Prod.map id (Int.cast : ℤ → ℝ) ''
      ⋃ a ∈ Set.Ico 1 (n : ℤ), (a, ·) '' Set.Ico (a ^ 3) (a^3 + 3*a^2 + 3*a)).ncard := by
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
