-- https://cloud.kili-technology.com/label/projects/label/cm92t1t8l00384ev5q1rpmzxa

import Mathlib

/- Given that the sum of several positive integers is 2019.
Find the maximum value of their product. -/

theorem number_theory_152633 :
    IsGreatest (Multiset.prod '' {s | s.sum = 2019}) (3 ^ 673) := by

  suffices IsGreatest (Multiset.prod '' {s | s.sum = 2019}) (Multiset.replicate 673 3).prod by
    simpa only [Multiset.prod_replicate] using this

  -- TODO: Should not be possible to use `n ≥ 1` here.
  suffices ∀ n ≥ 2, ∃ a b, a < 3 ∧ 2 * a + 3 * b = n ∧
      IsGreatest (Multiset.prod '' {s | s.sum = n}) (2 ^ a * 3 ^ b) by
    specialize this 2019 (by norm_num)
    rcases this with ⟨a, b, ha, h_sum, h_prod⟩
    -- The desired result can be obtained by showing that `a = 0`.
    suffices ha : a = 0 by
      replace h_sum : 3 * b = 2019 := by simpa [ha] using h_sum
      have hb : b = 673 := (Nat.mul_right_inj three_ne_zero).mp h_sum
      rw [← hb]
      simpa [ha] using h_prod
    -- We can determine that `a = 0` since `3 ∣ 2019` and `a < 3`.
    refine Nat.eq_zero_of_dvd_of_lt ?_ ha
    refine Nat.dvd_of_mod_eq_zero ?_
    suffices 2 * a ≡ 2 * 0 [MOD 3] from Nat.ModEq.cancel_left_of_coprime (by norm_num) this
    suffices 2 * a % 3 = 0 by simpa using this
    have := congrArg (· % 3) h_sum
    simpa using this

  intro n hn
  suffices ∃ s : Multiset ℕ, s.toFinset ⊆ {2, 3} ∧ s.sum = n ∧
      IsGreatest (Multiset.prod '' {s | s.sum = n}) s.prod by
    rcases this with ⟨s, hs_elem, hs_sum, hs_prod⟩
    use s.count 2, s.count 3
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · convert hs_sum
      rw [Finset.sum_multiset_count_of_subset _ _ hs_elem]
      simp [mul_comm (s.count _)]
    · convert hs_prod
      rw [Finset.prod_multiset_count_of_subset _ _ hs_elem]
      simp
    rcases hs_prod with ⟨_, hs_max⟩  -- TODO?
    contrapose hs_max with hs2
    rw [not_lt] at hs2
    suffices ∃ t : Multiset ℕ, t.sum = n ∧ s.prod < t.prod by simpa [mem_upperBounds] using this
    obtain ⟨t, rfl⟩ : ∃ t, s = t + Multiset.replicate 3 2 := by
      refine le_iff_exists_add'.mp ?_
      exact Multiset.le_count_iff_replicate_le.mp hs2
    use t + Multiset.replicate 2 3
    refine ⟨?_, ?_⟩
    · convert hs_sum using 1
      simp only [Multiset.sum_add]
      simp
    · simp only [Multiset.prod_add]
      gcongr
      · -- TODO: Might be an easier way to implement this?
        refine Nat.zero_lt_of_ne_zero ?_
        suffices 0 ∉ t.toFinset by simpa using this
        have ht_elem : t.toFinset ⊆ {2, 3} := by
          rw [Multiset.toFinset_add] at hs_elem
          exact Finset.union_subset_left hs_elem
        suffices 0 ∉ ({2, 3} : Finset ℕ) from fun h ↦ this (ht_elem h)
        norm_num
      · -- `2 ^ 3 < 3 ^ 2`
        norm_num

  -- Any 4 can be replaced with 2s; same sum, same product.
  suffices ∃ s : Multiset ℕ, s.toFinset ⊆ {2, 3, 4} ∧ s.sum = n ∧
      IsGreatest (Multiset.prod '' {s | s.sum = n}) s.prod by
    rcases this with ⟨s, hs_elem, hs_sum, hs_prod⟩
    use Multiset.replicate (s.count 2 + 2 * s.count 4) 2 + Multiset.replicate (s.count 3) 3
    refine ⟨?_, ?_⟩
    · -- TODO: Use Multiset subset?
      suffices Multiset.replicate (s.count 2 + 2 * s.count 4) 2 +
          Multiset.replicate (s.count 3) 3 ⊆ {2, 3} by
        rw [← Multiset.toFinset_subset] at this
        simpa using this
      rw [Multiset.subset_iff]
      intro x hx
      rw [Multiset.mem_add] at hx
      simpa using hx.imp Multiset.eq_of_mem_replicate Multiset.eq_of_mem_replicate

    refine ⟨?_, ?_⟩
    · convert hs_sum using 1
      calc _
      _ = (s.count 2 + 2 * s.count 4) * 2 + s.count 3 * 3 := by simp
      _ = s.count 2 * 2 + s.count 3 * 3 + s.count 4 * 4 := by ring
      _ = ∑ x ∈ {2, 3, 4}, s.count x * x := by simp [add_assoc]
      _ = _ := (Finset.sum_multiset_count_of_subset _ _ hs_elem).symm
    · convert hs_prod using 1
      calc _
      _ = 2 ^ s.count 2 * 4 ^ s.count 4 * 3 ^ s.count 3 := by simp [pow_add, pow_mul]
      _ = 2 ^ s.count 2 * 3 ^ s.count 3 * 4 ^ s.count 4 := by ring
      _ = ∏ x ∈ {2, 3, 4}, x ^ s.count x := by simp [mul_assoc]
      _ = _ := (Finset.prod_multiset_count_of_subset _ _ hs_elem).symm

  -- Now it suffices to show that any solution must use only {2, 3, 4},
  -- since it can be demonstrated that there is a greatest element.
  suffices ∀ s : Multiset ℕ, s.sum = n → IsGreatest (Multiset.prod '' {s | s.sum = n}) s.prod →
      s.toFinset ⊆ {2, 3, 4} by
    suffices ∃ y, IsGreatest (Multiset.prod '' {s | s.sum = n}) y by
      rcases this with ⟨y, hy⟩
      obtain ⟨t, ⟨ht_sum, rfl⟩⟩ : ∃ s : Multiset ℕ, s.sum = n ∧ s.prod = y := by simpa using hy.1
      have h : ∀ s : Multiset ℕ, s.sum = n → s.prod ≤ t.prod := by
        simpa [mem_upperBounds] using hy.2
      use t
      exact ⟨this t ht_sum hy, ht_sum, hy⟩

    -- Establish existence of a maximum using boundedness and that sets are not empty.
    refine BddAbove.exists_isGreatest_of_nonempty ?_ ?_
    · refine bddAbove_def.mpr ?_
      use n ^ n
      suffices ∀ s : Multiset ℕ, s.sum = n → s.prod ≤ n ^ n by simpa using this
      intro s hs_sum
      by_cases hs_zero : 0 ∈ s
      · simp [Multiset.prod_eq_zero hs_zero]
      · calc _
        _ ≤ n ^ s.card := by
          refine Multiset.prod_le_pow_card s n fun x hx ↦ ?_
          refine le_of_le_of_eq ?_ hs_sum
          exact Multiset.le_sum_of_mem hx
        _ ≤ n ^ n := by
          suffices s.card ≤ n by
            refine Nat.pow_le_pow_right ?_ this
            exact Nat.zero_lt_of_lt hn
          suffices ∀ x ∈ s, 1 ≤ x by
            refine le_of_le_of_eq ?_ hs_sum
            simpa using Multiset.card_nsmul_le_sum this
          intro x hx
          refine Nat.one_le_iff_ne_zero.mpr ?_
          exact ne_of_mem_of_not_mem hx hs_zero
    · refine .image Multiset.prod ?_
      exact Set.nonempty_of_mem (by simp : {n} ∈ _)

  -- TODO: Avoid re-proving `0 ∉ s`? (Is it being proved twice?)
  intro s hs_sum hs_max
  -- TODO: Unpack this?
  -- rcases hs with ⟨hs_elem, hs_max⟩
  have h_zero : 0 ∉ s := by
    have : ∀ (t : Multiset ℕ), t.sum = n → t.prod ≤ s.prod := by
      simpa [mem_upperBounds] using hs_max.2
    have : n ≤ s.prod := by simpa using this {n} rfl
    refine mt (fun h ↦ ?_) (Nat.not_lt.mpr this)
    rw [Multiset.prod_eq_zero h]
    exact Nat.zero_lt_of_lt hn

  intro x hx_mem
  rw [Multiset.mem_toFinset] at hx_mem
  change x ∈ Finset.Icc 2 4
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  -- We already know that there cannot be a 0 in the set.
  -- Furthermore, for `n > 1`, there cannot be a 1 in the set, since the product
  -- could be increased by adding 1 to one of the other numbers in the set.
  · suffices x ≠ 1 by
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨?_, this⟩
      exact ne_of_mem_of_not_mem hx_mem h_zero

    have hs_max := hs_max.2
    simp [mem_upperBounds] at hs_max  -- TODO

    suffices x = 1 → ∃ (t : Multiset ℕ), t.sum = n ∧ s.prod < t.prod by
      refine mt this ?_
      simpa using hs_max
    -- Substitute `x = 1`.
    rintro rfl
    -- Obtain any another element of the multiset `s`.
    obtain ⟨y, hy⟩ : ∃ y, y ∈ s.erase 1 := by
      refine Multiset.exists_mem_of_ne_zero ?_
      suffices (s.erase 1).sum ≠ 0 from mt (fun h ↦ h ▸ Multiset.sum_zero) this
      rw [← Multiset.sum_erase hx_mem] at hs_sum
      linarith
    -- Combine with 1 to obtain a greater product.
    use (1 + y) ::ₘ (s.erase 1).erase y
    refine ⟨?_, ?_⟩
    · refine .trans ?_ hs_sum
      rw [Multiset.sum_cons, add_assoc, Multiset.sum_erase hy, Multiset.sum_erase hx_mem]
    · rw [Multiset.prod_cons, ← Multiset.prod_erase hx_mem, ← Multiset.prod_erase hy, ← mul_assoc]
      gcongr
      · -- Requires that product non-zero.
        refine Nat.pos_of_ne_zero ?_
        refine Multiset.prod_ne_zero ?_
        refine mt (fun h ↦ ?_) h_zero
        exact Multiset.mem_of_mem_erase <| Multiset.mem_of_mem_erase h
      · simp

  -- Finally, there cannot be a number greater than or equal to 5 in the set,
  -- since it could be split `(2 + x) * (3 + y) < 2 * 3 * x * y`.
  · refine Nat.ge_of_not_lt fun hx ↦ ?_
    -- TODO: Find a way to move outside?
    suffices ∃ t : Multiset ℕ, t.sum = n ∧ s.prod < t.prod by
      refine not_exists.mpr ?_ this
      simp only [not_and, not_lt]
      intro t ht_sum
      refine mem_upperBounds.mp hs_max.2 t.prod ?_
      exact Set.mem_image_of_mem Multiset.prod ht_sum

    -- Split into two elements with that are at least 2 and 3.
    obtain ⟨a, b, ha, hb, rfl⟩ : ∃ a b : ℕ, 2 ≤ a ∧ 3 ≤ b ∧ a + b = x := by
      use 2, x - 2, le_rfl
      refine ⟨?_, ?_⟩
      · refine Nat.le_sub_of_add_le ?_
        exact hx
      · refine Nat.add_sub_cancel' ?_
        linarith
    -- Use that `a + b < a * b` for `2 ≤ a` and `3 ≤ b`.
    -- Note that we have equality for `a = b = 2`.
    use {a, b} + s.erase (a + b), ?_, ?_
    · refine Eq.trans ?_ hs_sum
      rw [Multiset.sum_add, Multiset.sum_pair, Multiset.sum_erase hx_mem]
    · rw [Multiset.prod_add, Multiset.prod_pair]
      rw [← Multiset.prod_erase hx_mem]
      gcongr
      · -- Requires non-zero.
        refine Nat.pos_of_ne_zero ?_
        refine Multiset.prod_ne_zero ?_
        refine mt (fun h ↦ ?_) h_zero
        exact Multiset.mem_of_mem_erase h
      · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ha
        obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
        calc _
        _ = 5 + a + b := by ring
        _ < 6 + 3 * a + 2 * b + a * b := by
          refine Nat.lt_add_right (a * b) ?_
          refine add_lt_add_of_lt_of_le ?_ (Nat.le_mul_of_pos_left b two_pos)
          refine add_lt_add_of_lt_of_le ?_ (Nat.le_mul_of_pos_left a three_pos)
          norm_num
        _ = _ := by ring

  -- -- To establish finiteness, need to exclude zeros from the multisets.
  -- have h_finite (n : ℕ) : {s : Multiset ℕ | 0 ∉ s ∧ s.sum = n}.Finite := by
  --   induction n using Nat.case_strong_induction_on with
  --   | hz =>
  --     suffices {s : Multiset ℕ | 0 ∉ s ∧ s.sum = 0} = {0} by simp [this]
  --     ext s
  --     simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  --     refine ⟨?_, fun hx ↦ by simp [hx]⟩
  --     intro ⟨hs_zero, hs_sum⟩
  --     rw [Multiset.sum_eq_zero_iff] at hs_sum
  --     refine Multiset.eq_zero_of_forall_not_mem fun x ↦ ?_
  --     refine mt (fun hx ↦ ?_) hs_zero
  --     exact hs_sum x hx ▸ hx  -- TODO: Feels strange using hx twice?
  --   | hi n IH =>
  --     suffices {s : Multiset ℕ | 0 ∉ s ∧ s.sum = n + 1} = ⋃ i : Set.Icc 1 (n + 1),
  --         (i.val ::ₘ ·) '' {t : Multiset ℕ | 0 ∉ t ∧ t.sum = (n + 1) - i.val} by
  --       rw [this]
  --       refine Set.finite_iUnion ?_
  --       simp only [Subtype.forall, Set.mem_Icc]
  --       refine fun i hi ↦ .image _ (IH _ ?_)
  --       refine Nat.sub_le_of_le_add ?_
  --       exact Nat.add_le_add_left hi.1 n
  --     ext s
  --     simp only [Set.mem_setOf_eq, Set.iUnion_coe_set, Set.mem_iUnion, Set.mem_image, exists_prop]
  --     refine ⟨?_, ?_⟩
  --     · simp only [Set.mem_Icc, and_imp]
  --       intro hs_zero hs_sum
  --       obtain ⟨x, hx⟩ : ∃ x, x ∈ s := by
  --         refine Multiset.exists_mem_of_ne_zero fun h ↦ ?_
  --         simp [h] at hs_sum
  --       obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hx
  --       rw [Multiset.sum_cons] at hs_sum
  --       use x
  --       refine ⟨?_, ?_⟩
  --       · refine ⟨?_, ?_⟩
  --         · suffices x ≠ 0 from Nat.one_le_iff_ne_zero.mpr this
  --           exact ne_of_mem_of_not_mem hx hs_zero
  --         · exact Nat.le.intro hs_sum
  --       use t
  --       refine ⟨⟨?_, ?_⟩, rfl⟩
  --       · refine mt (fun h ↦ ?_) hs_zero
  --         exact Multiset.mem_cons_of_mem h
  --       · exact Nat.eq_sub_of_add_eq' hs_sum

  --     · simp only [Set.mem_Icc, forall_exists_index, and_imp]
  --       intro x hx_zero hx_le t ht_zero ht_sum hs
  --       refine ⟨?_, ?_⟩
  --       · rw [← hs]
  --         simp only [Multiset.mem_cons, not_or]
  --         exact ⟨Nat.ne_of_lt hx_zero, ht_zero⟩
  --       · rw [← hs, Multiset.sum_cons]
  --         symm
  --         exact (Nat.sub_eq_iff_eq_add' hx_le).mp ht_sum.symm

  -- -- have : (Multiset.prod '' {s | s.sum = n}).Finite := Set.Finite.image Multiset.prod this

  -- -- have : ∃ u, IsGreatest (Multiset.prod '' {s | s.sum = n}) u := by
  -- --   sorry

  -- have h_nonempty (n : ℕ) : {s : Multiset ℕ | 0 ∉ s ∧ s.sum = n}.Nonempty := by
  --   cases n with
  --   | zero =>
  --     refine Set.nonempty_of_mem (x := 0) ?_
  --     simp
  --   | succ n =>
  --     refine Set.nonempty_of_mem (x := {n + 1}) ?_
  --     simp

  -- have _ : Nonempty {s : Multiset ℕ // 0 ∉ s ∧ s.sum = n} := nonempty_subtype.mpr (h_nonempty n)
  -- have _ : Finite {s : Multiset ℕ // 0 ∉ s ∧ s.sum = n} := h_finite n

  -- have := exists_eq_ciSup_of_finite (ι := {s : Multiset ℕ // 0 ∉ s ∧ s.sum = n})
  --   (f := Multiset.prod ∘ Subtype.val)
  -- simp at this






  -- -- Just come up with a trivial bound.
  -- have h_bdd : BddAbove (Multiset.prod '' {s | s.sum = n}) := by
  --   refine bddAbove_def.mpr ?_
  --   use n ^ n
  --   suffices ∀ s : Multiset ℕ, s.sum = n → s.prod ≤ n ^ n by simpa using this
  --   intro s hs_sum
  --   by_cases hs_zero : 0 ∈ s
  --   · simp [Multiset.prod_eq_zero hs_zero]
  --   · calc _
  --     _ ≤ n ^ s.card := by
  --       refine Multiset.prod_le_pow_card s n fun x hx ↦ ?_
  --       refine le_of_le_of_eq ?_ hs_sum
  --       exact Multiset.le_sum_of_mem hx
  --     _ ≤ n ^ n := by
  --       suffices s.card ≤ n by
  --         refine Nat.pow_le_pow_right ?_ this
  --         exact Nat.zero_lt_of_lt hn
  --       suffices ∀ x ∈ s, 1 ≤ x by
  --         refine le_of_le_of_eq ?_ hs_sum
  --         simpa using Multiset.card_nsmul_le_sum this
  --       intro x hx
  --       refine Nat.one_le_iff_ne_zero.mpr ?_
  --       exact ne_of_mem_of_not_mem hx hs_zero

  -- -- have (s) := le_ciSup_set h_bdd (c := s)
  -- have h_nonempty : {s : Multiset ℕ | s.sum = n}.Nonempty :=
  --   Set.nonempty_of_mem (by simp : {n} ∈ _)

  -- have := BddAbove.exists_isGreatest_of_nonempty h_bdd (h_nonempty.image Multiset.prod)

  -- rcases this with ⟨y, hy⟩
  -- obtain ⟨s, hs⟩ : ∃ s : Multiset ℕ, s.sum = n ∧ s.prod = y := by simpa using hy.1
  -- have hy : ∀ s : Multiset ℕ, s.sum = n → s.prod ≤ y := by simpa [mem_upperBounds] using hy.2



  -- change IsGreatest (Multiset.prod '' {s : Multiset ℕ | s.sum = 673 * 3}) (3 ^ 673)
  -- -- Replace 673 with a symbol to avoid unnecessary recusion.
  -- generalize hk : 673 = k
  -- suffices IsGreatest (Multiset.prod '' {s | s.sum = k * 3}) (Multiset.replicate k 3).prod by
  --   simpa using this

  -- refine ⟨?_, ?_⟩
  -- · refine Set.mem_image_of_mem Multiset.prod ?_
  --   simp

  -- generalize hn : k * 3 = n
  -- simp only [mem_upperBounds, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
  --   forall_apply_eq_imp_iff₂]
  -- intro s hs



  -- generalize 2019 = n
  -- generalize 3 ^ 673 = y

  -- suffices IsGreatest (Multiset.prod '' {s : Multiset ℕ | s.sum = 2019})
  --     (Multiset.replicate 673 3).prod by
  --   rw [Multiset.prod_replicate] at this
  --   exact this

  -- It suffices to show that all elements are either 2 or 3,
  -- and that the nearest multiple of 6 is obtained using 3s.



  -- have h_zero (n : ℕ) (s : Multiset ℕ) (hn : 2 ≤ n) (hs_sum : s.sum = n) :
  --     IsGreatest (Multiset.prod '' {s : Multiset ℕ | s.sum = n}) s.prod →
  --     ∀ x ∈ s, x ≠ 0 := by
  --   intro hs_max x hx_mem hx
  --   -- TODO: Find a way to move outside?
  --   suffices ∃ t : Multiset ℕ, t.sum = n ∧ s.prod < t.prod by
  --     refine not_exists.mpr ?_ this
  --     simp only [not_and, not_lt]
  --     intro t ht_sum
  --     refine mem_upperBounds.mp hs_max.2 t.prod ?_
  --     exact Set.mem_image_of_mem Multiset.prod ht_sum

  --   rcases hx with rfl
  --   rw [Multiset.prod_eq_zero_iff.mpr hx_mem]
  --   use {n}
  --   refine ⟨by simp, ?_⟩
  --   rw [Multiset.prod_singleton]
  --   linarith

  -- have h_one (n : ℕ) (s : Multiset ℕ) (hn : 2 ≤ n) (hs_sum : s.sum = n) :
  --     IsGreatest (Multiset.prod '' {s : Multiset ℕ | s.sum = n}) s.prod →
  --     ∀ x ∈ s, x ≠ 1 := by
  --   intro hs_max x hx_mem hx
  --   -- TODO: Find a way to move outside?
  --   suffices ∃ t : Multiset ℕ, t.sum = n ∧ s.prod < t.prod by
  --     refine not_exists.mpr ?_ this
  --     simp only [not_and, not_lt]
  --     intro t ht_sum
  --     refine mem_upperBounds.mp hs_max.2 t.prod ?_
  --     exact Set.mem_image_of_mem Multiset.prod ht_sum

  --   -- Combine the 1 with another element to obtain a greater product.
  --   obtain ⟨y, hy⟩ : ∃ y, y ∈ s.erase x := by
  --     refine Multiset.exists_mem_of_ne_zero ?_
  --     suffices (s.erase x).sum ≠ 0 from mt (fun h ↦ h ▸ Multiset.sum_zero) this
  --     refine ne_of_gt ?_
  --     rw [← Multiset.sum_erase hx_mem] at hs_sum
  --     linarith
  --   use (x + y) ::ₘ (s.erase x).erase y
  --   refine ⟨?_, ?_⟩
  --   · refine .trans ?_ hs_sum
  --     rw [Multiset.sum_cons, add_assoc, Multiset.sum_erase hy, Multiset.sum_erase hx_mem]
  --   · rw [Multiset.prod_cons, ← Multiset.prod_erase hx_mem, ← Multiset.prod_erase hy, ← mul_assoc]
  --     gcongr
  --     · -- Requires non-zero.
  --       refine Multiset.prod_pos fun z hz ↦ Nat.zero_lt_of_ne_zero ?_
  --       refine h_zero n s hn hs_sum hs_max z ?_
  --       exact Multiset.mem_of_mem_erase <| Multiset.mem_of_mem_erase hz
  --     · simp [hx]

  -- have h_four (n : ℕ) (s : Multiset ℕ) (hn : 2 ≤ n) (hs_sum : s.sum = n)
  --     (hs_max : IsGreatest (Multiset.prod '' {s : Multiset ℕ | s.sum = n}) s.prod) :
  --     ∀ x ∈ s, x ≤ 4 := by
  --   intro x hx_mem
  --   refine Nat.ge_of_not_lt fun hx ↦ ?_
  --   -- TODO: Find a way to move outside?
  --   suffices ∃ t : Multiset ℕ, t.sum = n ∧ s.prod < t.prod by
  --     refine not_exists.mpr ?_ this
  --     simp only [not_and, not_lt]
  --     intro t ht_sum
  --     refine mem_upperBounds.mp hs_max.2 t.prod ?_
  --     exact Set.mem_image_of_mem Multiset.prod ht_sum

  --   -- Split into two elements with that are at least 2 and 3.
  --   obtain ⟨a, b, ha, hb, rfl⟩ : ∃ a b : ℕ, 2 ≤ a ∧ 3 ≤ b ∧ a + b = x := by
  --     use 2, x - 2, le_rfl
  --     refine ⟨?_, ?_⟩
  --     · refine Nat.le_sub_of_add_le ?_
  --       exact hx
  --     · refine Nat.add_sub_cancel' ?_
  --       linarith
  --   -- Use that `a + b < a * b` for `2 ≤ a` and `3 ≤ b`.
  --   -- Note that we have equality for `a = b = 2`.
  --   use {a, b} + s.erase (a + b), ?_, ?_
  --   · refine Eq.trans ?_ hs_sum
  --     rw [Multiset.sum_add, Multiset.sum_pair, Multiset.sum_erase hx_mem]
  --   · rw [Multiset.prod_add, Multiset.prod_pair]
  --     rw [← Multiset.prod_erase hx_mem]
  --     gcongr
  --     · -- Requires non-zero.
  --       refine Multiset.prod_pos fun z hz ↦ Nat.zero_lt_of_ne_zero ?_
  --       refine h_zero n s hn hs_sum hs_max z ?_
  --       exact Multiset.mem_of_mem_erase hz
  --     · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ha
  --       obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
  --       calc _
  --       _ = 5 + a + b := by ring
  --       _ < 6 + 3 * a + 2 * b + a * b := by
  --         refine Nat.lt_add_right (a * b) ?_
  --         refine add_lt_add_of_lt_of_le ?_ (Nat.le_mul_of_pos_left b two_pos)
  --         refine add_lt_add_of_lt_of_le ?_ (Nat.le_mul_of_pos_left a three_pos)
  --         norm_num
  --       _ = _ := by ring

  -- -- The maximum can always be obtained using 2s and 3s (no 4s)
  -- have h_sans_four (n : ℕ) (s : Multiset ℕ) (hn : 2 ≤ n) (hs_sum : s.sum = n)
  --     (hs_max : IsGreatest (Multiset.prod '' {s : Multiset ℕ | s.sum = n}) s.prod) :
  --     ∃ t ⊆ ({2, 3} : Multiset ℕ), t.sum = n ∧
  --       IsGreatest (Multiset.prod '' {s : Multiset ℕ | s.sum = n}) t.prod := by
  --   use Multiset.replicate (s.count 2 + 2 * s.count 4) 2 + Multiset.replicate (s.count 3) 3
  --   refine ⟨?_, ?_⟩
  --   · rw [Multiset.subset_iff]
  --     intro x hx
  --     rw [Multiset.mem_add] at hx
  --     simpa using hx.imp Multiset.eq_of_mem_replicate Multiset.eq_of_mem_replicate
  --   have h234 : s.toFinset ⊆ {2, 3, 4} := by
  --     intro x hx
  --     rw [Multiset.mem_toFinset] at hx
  --     suffices x ∈ Finset.Icc 2 4 from this
  --     rw [Finset.mem_Icc]
  --     refine ⟨?_, ?_⟩
  --     · suffices x ∉ Finset.Iio 2 by simpa using this
  --       change x ∉ ({0, 1} : Finset ℕ)
  --       suffices x ≠ 0 ∧ x ≠ 1 by simpa using this
  --       refine ⟨?_, ?_⟩
  --       · exact h_zero n s hn hs_sum hs_max x hx
  --       · exact h_one n s hn hs_sum hs_max x hx
  --     · exact h_four n s hn hs_sum hs_max x hx
  --   refine ⟨?_, ?_⟩
  --   · convert hs_sum using 1
  --     calc _
  --     _ = (s.count 2 + 2 * s.count 4) * 2 + s.count 3 * 3 := by simp
  --     _ = s.count 2 * 2 + s.count 3 * 3 + s.count 4 * 4 := by ring
  --     _ = ∑ x ∈ {2, 3, 4}, s.count x * x := by simp [add_assoc]
  --     _ = _ := (Finset.sum_multiset_count_of_subset _ _ h234).symm
  --   · convert hs_max using 1
  --     calc _
  --     _ = 2 ^ s.count 2 * 4 ^ s.count 4 * 3 ^ s.count 3 := by simp [pow_add, pow_mul]
  --     _ = 2 ^ s.count 2 * 3 ^ s.count 3 * 4 ^ s.count 4 := by ring
  --     _ = ∏ x ∈ {2, 3, 4}, x ^ s.count x := by simp [mul_assoc]
  --     _ = _ := (Finset.prod_multiset_count_of_subset _ _ h234).symm

  -- -- If the number is divisible by 3, then we use all 3s.
  -- -- Otherwise, we use 2s (or a 4) to reach a multiple of 3.

  -- -- let rec f : ℕ → Multiset ℕ := fun
  -- --   | 0 => ∅
  -- --   | 1 => {1}
  -- --   | 2 => {2}
  -- --   | n + 3 => if 3 ∣ n then 3 ::ₘ f n else 2 ::ₘ f (n + 1)

  -- -- let f (n : ℕ) : Multiset ℕ :=
  -- --   if n % 6 = 4 then 2 ::ₘ 2 ::ₘ Multiset.replicate (n / 3 - 1) 3
  -- --   else if n % 3 = 2 then 2 ::ₘ Multiset.replicate (n / 3) 3
  -- --   else Multiset.replicate (n / 3) 3

  -- let f (n : ℕ) : Multiset ℕ :=
  --   match Nat.divModEquiv 3 n with
  --   | (k, 0) => Multiset.replicate k 3
  --   | (k, 2) => 2 ::ₘ Multiset.replicate (k) 3
  --   | (0, 1) => {1}
  --   | (k + 1, 1) => 2 ::ₘ 2 ::ₘ Multiset.replicate k 3

  -- have hf_zero : f 0 = ∅ := by simp [f]
  -- have hf_one : f 1 = {1} := by simp [f]
  -- have hf_two : f 2 = {2} := by simp [f]
  -- have hf_three (k : ℕ) : f (3 * k) = Multiset.replicate k 3 := by simp [f]


  -- suffices ∀ k ≥ 1, IsGreatest (Multiset.prod '' {s | s.sum = 3 * k}) (3 ^ k) from
  --   this 673 (by norm_num)

  -- suffices ∀ n ≥ 3, IsGreatest (Multiset.prod '' {s | s.sum = n}) (f n).prod by
  --   intro k
  --   convert this (3 * k) using 1
  --   · simp
  --   · unfold f
  --     simp


  -- intro n hn

  -- suffices ∃ a b : ℕ, a < 3 ∧ 2 * a + 3 * b = n ∧
  --     IsGreatest (Multiset.prod '' {s | s.sum = n}) (2 ^ a * 3 ^ b) by
  --   rcases this with ⟨a, b, ha, h_sum, h_prod⟩

  --   sorry

  -- -- unfold f
  -- -- intro n


  -- -- Prove the recursive property
  -- have hf_rec (n : ℕ) : f (n + 3) = if 3 ∣ n then 3 ::ₘ f n else 2 ::ₘ f (n + 1) := by
  --   -- revert n
  --   -- suffices ∀ (k : ℕ) (r : Fin 3), k ≠ 0 →
  --   --     f (3 * k + r) = if r = 0 then 3 ::ₘ f (3 * ) else 2 ::ₘ f (n - 2) by
  --   --   sorry
  --   unfold f
  --   obtain ⟨k, m, rfl⟩ : ∃ (k : ℕ) (m : Fin 3), (Nat.divModEquiv 3).symm (k, m) = n := by
  --     use n / 3, n % 3
  --     simpa using Nat.div_add_mod' n 3

  --   have : (Nat.divModEquiv 3).symm (k, m) + 3 = (Nat.divModEquiv 3).symm (k + 1, m) := by
  --     simp only [Nat.divModEquiv_symm_apply]
  --     ring

  --   simp only [this, Equiv.apply_symm_apply]

  --   cases k with
  --   | zero =>
  --     -- TODO: Cleanup
  --     simp
  --     sorry
  --     -- have : (m : ℕ) < 3 := m.isLt
  --     -- have : ¬3 ≤ (m : ℕ) := Nat.not_le_of_lt this
  --     -- simp [this] at hn
  --   | succ k =>

  --   sorry

  --   -- have : 3 ∣ (Nat.divModEquiv 3).symm (k + 1, m) ↔ m = 0 := by sorry
  --   -- simp only [this]

  --   -- have : (Nat.divModEquiv 3).symm (k + 1, m) = (Nat.divModEquiv 3).symm (k, m) + 3 := by sorry
  --   -- simp only [this]

  --   -- simp [-Nat.divModEquiv_symm_apply, -Nat.divModEquiv_apply]

  --   -- cases m using Fin.cases with
  --   -- | zero => simp
  --   -- | succ m =>
  --   --   cases m using Fin.cases with
  --   --   | zero =>
  --   --     suffices (k * 3 + 1 + 1) / 3 = (k * 3 + 1) / 3 by simp [this]
  --   --     refine Nat.add_div_eq_of_add_mod_lt ?_
  --   --     simp [Nat.add_mod]
  --   --   | succ m =>
  --   --     suffices (k * 3 + 2 + 1) / 3 = (k * 3 + 2) / 3 + 1 by simp [Fin.succ_ne_zero, this]
  --   --     refine Nat.add_div_eq_of_le_mod_add_mod ?_ three_pos
  --   --     simp [Nat.add_mod]


  -- have hf_dvd (n : ℕ) (hn : 3 ∣ n) : (f n).prod = 3 ^ (n / 3) := by
  --   rcases hn with ⟨k, rfl⟩
  --   rw [mul_div_cancel_left₀ _ (by norm_num)]
  --   cases k with
  --   | zero =>
  --     simp
  --     sorry
  --   | succ k =>

  --     sorry

  -- have h_three (n : ℕ) (s : Multiset ℕ) (hn : 2 ≤ n) (hs_sum : s.sum = n) (hs_subset : s ⊆ {2, 3})
  --     (hs_max : IsGreatest (Multiset.prod '' {s : Multiset ℕ | s.sum = n}) s.prod) :
  --   s = f n := by
  --   refine n.strong_induction_on fun n m ↦ ?_


  --   sorry
  --   -- induction s using Multiset.induction generalizing n with
  --   -- | empty =>
  --   --   rcases hs_sum with rfl
  --   --   simp at hn  -- Contradiction.
  --   -- | cons x s IH =>
  --   --   simp only [Multiset.sum_cons] at hs_sum
  --   --   simp only [Multiset.prod_cons] at hs_max
  --   --   refine Fin.cases ?_ ?_ (n : Fin 3)
  --   --   · simp
  --   --     sorry
  --   --   · sorry


  -- -- have h_three_dvd (n : ℕ) (s : Multiset ℕ) (hn : 2 ≤ n) (hn_dvd : 3 ∣ n) (hs_sum : s.sum = n) :
  -- --     IsGreatest (Multiset.prod '' {s : Multiset ℕ | s.sum = n}) s.prod →
  -- --     ∀ x ∈ s, x = 3 := by
  -- --   intro hs_max x hx_mem
  -- --   suffices ¬x ≠ 3 by simpa using this
  -- --   intro hx
  -- --   -- TODO: Find a way to move outside?
  -- --   suffices ∃ t : Multiset ℕ, t.sum = n ∧ s.prod < t.prod by
  -- --     refine not_exists.mpr ?_ this
  -- --     simp only [not_and, not_lt]
  -- --     intro t ht_sum
  -- --     refine mem_upperBounds.mp hs_max.2 t.prod ?_
  -- --     exact Set.mem_image_of_mem Multiset.prod ht_sum
  -- --   sorry


  -- suffices ∀ (s : Multiset ℕ), s.sum = 2019 → s.prod ≤ (3 ^ 673) by
  --   refine ⟨?_, ?_⟩
  --   · sorry
  --   rw [mem_upperBounds]
  --   -- TODO: Don't need `suffices`?
  --   generalize 673 = b at this ⊢
  --   simpa using this

  -- suffices ∀ (n: ℕ) (s : Multiset ℕ), 1 < n → s.sum = n →
  --     IsGreatest (Multiset.prod '' {s : Multiset ℕ | s.sum = n}) s.prod →
  --     s ⊆ {2, 3} ∧ s.count 2 < 3 by

  --   specialize this 2019 (Multiset.replicate 673 3) (by norm_num) (by
  --     rw [Multiset.sum_replicate]
  --     norm_num)

  --   sorry

  -- sorry

  -- -- refine ⟨?_, ?_⟩
  -- -- · refine Set.mem_image_of_mem _ ?_
  -- --   rw [Set.mem_setOf_eq, Multiset.sum_replicate]
  -- --   norm_num

  -- -- -- generalize 673 = p
  -- -- rw [mem_upperBounds]
  -- -- simp only [Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
  -- --   forall_apply_eq_imp_iff₂]
  -- -- intro s hs
  -- -- rw [Multiset.prod_replicate]


  -- -- induction s using Multiset.induction with
  -- -- | empty => simp at hs  -- Contradiction.
  -- -- | cons x s IH =>
  -- --   rw [Multiset.sum_cons] at hs
  -- --   rw [Multiset.prod_cons]

  -- --   sorry
