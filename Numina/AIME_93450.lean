-- https://cloud.kili-technology.com/label/projects/label/cm7eni5b90021zz87cs9o2p28
-- https://artofproblemsolving.com/wiki/index.php/2007_AIME_I_Problems/Problem_5

import Mathlib

open scoped Finset

/- The formula for converting Fahrenheit temperature F to the corresponding
Celsius temperature C is C = 5 / 9 * (F - 32).
An integer Fahrenheit temperature is converted to Celsius, rounded to the nearest integer,
converted back to Fahrenheit, and again rounded to the nearest integer.
For how many integer Fahrenheit temperatures between 32 and 1000 inclusive does
the original temperature equal the final temperature? -/

theorem algebra_93450 {toC toF : ℝ → ℝ} (h_toC : ∀ x, toC x = 5 / 9 * (x - 32))
    (h_toF : ∀ x, toF x = 9 / 5 * x + 32) :
    {x : ℤ | 32 ≤ x ∧ x ≤ 1000 ∧ round (toF (round (toC x))) = x}.ncard = 539 := by
  -- 32 F corresponds to 0 C.
  -- An increase of 9 F corresponds to an increase of 5 F.
  -- Therefore, the error after rounding is periodic with period 9.
  have h_round_toC_add (x : ℤ) : round (toC (x + 9)) = round (toC x) + 5 := by
    simp only [h_toC]
    calc _
    _ = round (5 / 9 * (x - 32) + 5 : ℝ) := by congr; ring
    _ = _ := round_add_ofNat _ 5
  have h_round_toF_add (x : ℤ) : round (toF (x + 5)) = round (toF x) + 9 := by
    simp only [h_toF]
    calc _
    _ = round (9 / 5 * x + 32 + 9 : ℝ) := by congr 1; ring
    _ = _ := round_add_ofNat _ 9
  -- Prove that the difference is periodic.
  have h_periodic_sub : Function.Periodic (fun x : ℤ ↦ round (toF (round (toC x))) - x) 9 := by
    intro f
    simp only [Int.cast_add, Int.cast_ofNat]
    rw [h_round_toC_add]
    simp only [Int.cast_add, Int.cast_ofNat, sub_add_eq_sub_sub, round_sub_ofNat, round_sub_int]
    rw [h_round_toF_add]
    ring
  -- Express the two quantities being equal as a periodic (decidable) predicate.
  have h_periodic_eq : Function.Periodic (fun x : ℤ ↦ round (toF (round (toC x))) = x) 9 := by
    intro f
    refine eq_iff_iff.mpr ?_
    refine (iff_congr sub_eq_zero sub_eq_zero).mp ?_
    exact Eq.congr_left (h_periodic_sub f)

  -- Since the difference is periodic, we will divide the range [32, 1000] into periods of 9:
  -- 1001 - 32 = 107 * 9 + 6
  -- Within each period of 9, the rounded result is correct for [0, 2, 4, 5, 7].
  have h_count_period :
      Nat.count (fun x : ℕ ↦ round (toF (round (toC (32 + x)))) = 32 + x) 9 = 5 := by
    simp only [round_eq, h_toC, h_toF, Nat.count_succ]
    norm_num
  -- For the remainder [0, 6), there are 4 additional correct values: [0, 2, 4, 5].
  have h_count_rest :
      Nat.count (fun x : ℕ ↦ round (toF (round (toC (32 + x)))) = 32 + x) 6 = 4 := by
    simp only [round_eq, h_toC, h_toF, Nat.count_succ]
    norm_num

  -- Establish the sum of a periodic function over a range of consecutive integers.
  -- (Unable to find a suitable lemma in Mathlib. The most relevant ones seemed to be
  -- `Nat.filter_Ico_card_eq_of_periodic` and `Nat.count_modEq_card`.)
  -- Prove for sum first, then use these to obtain same for card ∘ filter.
  -- First consider whole periods using induction.
  have h_sum_range_mul {α : Type} [AddCommMonoid α] {f : ℕ → α} {c : ℕ} (hf : f.Periodic c)
      (m : ℕ) : ∑ i in .range (m * c), f i = m • ∑ i in .range c, f i := by
    induction m with
    | zero => simp
    | succ m IH =>
      rw [add_mul, Finset.sum_range_add, IH, add_smul]
      simp only [one_mul, one_smul]
      congr 1
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      calc _
      _ = f ((m * c + i) % c) := by rw [hf.map_mod_nat _]
      _ = _ := by rw [Nat.mul_add_mod_of_lt (by simpa using hi)]
  -- Now consider the remainder.
  have h_sum_range_mul_add {α : Type} [AddCommMonoid α] {f : ℕ → α} {c : ℕ} (hf : f.Periodic c)
      (m k : ℕ) :
      ∑ i in .map (addLeftEmbedding (m * c)) (.range k), f i = ∑ i in .range k, f i := by
    rw [Finset.sum_map]
    congr
    ext i
    calc _
    _ = f ((m * c + i) % c) := (hf.map_mod_nat _).symm
    _ = f (i % c) := congrArg f (Nat.mul_add_mod' m c i)
    _ = _ := hf.map_mod_nat i
  -- And establish the same results for card ∘ filter with a periodic predicate.
  have h_card_filter_range_mul {p : ℕ → Prop} [DecidablePred p] {c : ℕ} (hp : p.Periodic c)
      (m : ℕ) : #(.filter p (.range (m * c))) = m * #(.filter p (.range c)) := by
    simpa only [Finset.card_filter] using h_sum_range_mul (fun x ↦ by simp only [hp x]) _
  have h_card_filter_range_mul_add {p : ℕ → Prop} [DecidablePred p] {c : ℕ} (hp : p.Periodic c)
      (m k : ℕ) :
      #(.filter p (.map (addLeftEmbedding (m * c)) (.range k))) = #(.filter p (.range k)) := by
    simpa only [Finset.card_filter] using h_sum_range_mul_add (fun x ↦ by simp only [hp x]) _ _

  -- Now we're ready to put it all together.
  calc _
  -- Since we know the set is finite, switch to Finset.
  _ = #(.filter (fun x : ℤ ↦ round (toF (round (toC x))) = x) (.Icc 32 1000)) := by
    rw [← Set.ncard_coe_Finset]
    simp [and_assoc]
  -- Switch to naturals to later use Finset.range and count.
  _ = #(.filter (fun x : ℤ ↦ round (toF (round (toC x))) = x) (.Ico 32 1001)) := rfl
  _ = #(.filter (fun x : ℤ ↦ round (toF (round (toC x))) = x)
      (.map Nat.castEmbedding (.Ico 32 1001))) := by
    refine congrArg _ (congrArg _ ?_)
    suffices ∀ a b : ℕ, Finset.Ico (a : ℤ) b = Finset.map Nat.castEmbedding (Finset.Ico a b) from
      this 32 1001
    intro a b
    ext i
    simp only [Finset.mem_Ico, Finset.mem_map, Nat.castEmbedding_apply]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have hi : i.toNat = i := Int.toNat_of_nonneg <| (Int.ofNat_zero_le a).trans h.1
      rw [← hi] at h
      refine ⟨i.toNat, ?_, hi⟩
      simpa only [Nat.cast_le, Nat.cast_lt] using h
    · rcases h with ⟨x, hx, hi⟩
      rw [← hi]
      simpa using hx
  _ = #(.filter ((fun x : ℤ ↦ round (toF (round (toC x))) = x) ∘ Nat.castEmbedding)
      (.Ico 32 1001)) := by
    rw [Finset.filter_map, Finset.card_map]
  _ = #(.filter (fun x : ℕ ↦ round (toF (round (toC x))) = x) (.Ico 32 1001)) := rfl
  -- Move the offset into the function and use Finset.range.
  _ = #(.filter (fun x : ℕ ↦ round (toF (round (toC (32 + x)))) = 32 + x)
      (.range (1001 - 32))) := by
    rw [Finset.card_filter, Finset.sum_Ico_eq_sum_range]
    simp
  -- Split into two separate terms.
  _ = 107 * 5 + 4 := by
    have hq : 1001 - 32 = 107 * 9 + 6 := by norm_num
    rw [hq, Finset.range_add, Finset.filter_union]
    rw [Finset.card_union_of_disjoint]
    swap
    · refine .mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) ?_
      exact Finset.disjoint_range_addLeftEmbedding _ _
    have : Function.Periodic (fun x : ℕ ↦ round (toF (round (toC (32 + x)))) = 32 + x) 9 :=
      fun x ↦ by simpa [add_assoc] using h_periodic_eq (32 + x)
    refine congrArg₂ _ ?_ ?_
    · rw [h_card_filter_range_mul this]
      rw [← Nat.count_eq_card_filter_range, h_count_period]
    · rw [h_card_filter_range_mul_add this]
      rw [← Nat.count_eq_card_filter_range, h_count_rest]
  _ = _ := by norm_num
