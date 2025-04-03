-- https://cloud.kili-technology.com/label/projects/label/cm84mpwv701xiiev518ak3u3v
-- https://artofproblemsolving.com/wiki/index.php/2024_AIME_II_Problems/Problem_14

import Mathlib

open Real

def is_bBeautiful (b : ℕ) (n : ℕ) :=
  n > 0 ∧ (Nat.digits b n).length = 2 ∧ (Nat.digits b n).sum = sqrt n

/- Let $b\ge 2$ be an integer.
Call a positive integer $n$ $b$-eautiful if it has exactly two digits
when expressed in base $b$ and these two digits sum to $\sqrt n$.
For example, $81$ is $13$-eatiful because $81 = 63_{13}$ and $6 + 3 = \sqrt{81}$.
Find the least integer $b \ge 2$ for which there are more than ten $b$-eautiful integers. -/

theorem number_theory_93241 :
    IsLeast {b | 2 ≤ b ∧ {n | is_bBeautiful b n}.encard > 10} 211 := by

  simp only [gt_iff_lt]

  suffices IsLeast {b | 2 ≤ b ∧ 10 < {z | z ∈ Set.Ico 2 b ∧ b - 1 ∣ z * (z - 1)}.encard} 211 by
    convert this using 3 with b
    refine and_congr_right fun hb ↦ ?_
    suffices {n | is_bBeautiful b n}.encard = {z | z ∈ Set.Ico 2 b ∧ b - 1 ∣ z * (z - 1)}.encard by
      rw [this]

    have hb_neZero : NeZero b := .of_gt hb  -- For `Nat.divModEquiv b`.
    calc _
    -- Rewrite condition on Nat.digits using arithmetic.
    _ = Set.encard {n : ℕ | ∃ x ∈ Set.Ico 1 b, ∃ y < b, (x + y) ^ 2 = n ∧ x * b + y = n} := by
      -- TODO: Fuck around with `Nat.digits`.
      sorry

    -- Use `y : Fin b` rather than `y < b` to enable use of `Nat.divModEquiv b`.
    _ = Set.encard ((Nat.divModEquiv b).symm ''
        {(x, y) : ℕ × Fin b | x ∈ Set.Ico 1 b ∧ (x + y) ^ 2 = x * b + y}) := by
      refine congrArg Set.encard ?_
      ext n
      simp only [and_assoc, Set.mem_setOf_eq, Set.mem_image, Prod.exists, exists_and_left]
      refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
      simp only [Fin.exists_iff, Nat.divModEquiv_symm_apply, exists_prop, Set.mem_Iio]
      refine exists_congr fun y ↦ and_congr_right fun hy ↦ ?_
      exact and_congr_left fun hn ↦ Eq.congr_right hn.symm
    _ = Set.encard {(x, y) : ℕ × Fin b | x ∈ Set.Ico 1 b ∧ (x + y) ^ 2 = x * b + y} :=
      (Equiv.injective _).injOn.encard_image
    -- Return to `y : ℕ` with `y < b` for the remainder of the proof.
    _ = Set.encard ((Prod.map id Fin.val) ''
        {(x, y) : ℕ × Fin b | x ∈ Set.Ico 1 b ∧ (x + y) ^ 2 = x * b + y}) := by
      refine (Function.Injective.injOn ?_).encard_image.symm
      exact Prod.map_injective.mpr ⟨Function.injective_id, Fin.val_injective⟩
    _ = Set.encard {(x, y) : ℕ × ℕ | x ∈ Set.Ico 1 b ∧ (x + y) ^ 2 = x * b + y ∧ y < b} := by
      congr
      ext ⟨x, y⟩
      simp [Fin.exists_iff, ← and_assoc]
    _ = Set.encard {(x, y) : ℕ × ℕ | x ∈ Set.Ico 1 b ∧ y < b ∧ (x + y) ^ 2 = x * b + y} := by
      simp only [and_comm]

    -- _ = Set.encard ((fun (x, y) ↦ x * b + y) ''
    --     {(x, y) : ℕ × ℕ | x ∈ Set.Ico 1 b ∧ y < b ∧ (x + y) ^ 2 = x * b + y}) := by
    --   refine congrArg Set.encard ?_
    --   ext n
    --   simp only [and_assoc, Set.mem_setOf_eq, Set.mem_image, Prod.exists, exists_and_left]
    --   refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
    --   refine exists_congr fun y ↦ and_congr_right fun hy ↦ ?_
    --   exact and_congr_left fun hn ↦ Eq.congr_right hn.symm
    -- _ = {(x, y) : ℕ × ℕ | x ∈ Set.Ico 1 b ∧ y < b ∧ (x + y) ^ 2 = x * b + y}.encard := by
    --   refine Set.InjOn.encard_image ?_
    --   -- Suffices to consider arbitrary `x` and `y < b`.
    --   suffices Set.InjOn (fun m : ℕ × ℕ ↦ m.1 * b + m.2) (Set.univ ×ˢ Set.Iio b) from
    --     this.mono fun m ⟨_, hy, _⟩ ↦ by simpa using hy
    --   intro ⟨x, y⟩ hy ⟨x', y'⟩ hy'
    --   simp only [Set.mem_prod, Set.mem_univ, Set.mem_Iio, true_and] at hy hy'
    --   simp only [Prod.mk.injEq]
    --   refine fun h ↦ ⟨?_, ?_⟩
    --   · simp only [mul_comm _ b] at h
    --     simpa [Nat.mul_add_div (Nat.zero_lt_of_lt hb), Nat.div_eq_of_lt hy, Nat.div_eq_of_lt hy']
    --       using congrArg (· / b) h
    --   · simpa [Nat.mul_add_mod_of_lt hy, Nat.mul_add_mod_of_lt hy'] using congrArg (· % b) h

    _ = Set.encard ((fun m : ℕ × ℕ ↦ (m.1, m.1 + m.2)) ''
        {(x, y) : ℕ × ℕ | x ∈ Set.Ico 1 b ∧ y < b ∧ (x + y) ^ 2 = x * b + y}) := by
      refine (Function.Injective.encard_image ?_ _).symm
      simp only [Function.Injective, Prod.mk.injEq, and_imp, Prod.forall]
      exact fun x y x' y' hx hz ↦ ⟨hx, Nat.add_left_cancel (hx ▸ hz)⟩

    _ = Set.encard {(x, z) : ℕ × ℕ |
        x ∈ Set.Ico 1 b ∧ ∃ y < b, (x + y) ^ 2 = x * b + y ∧ z = x + y} := by
      congr
      ext ⟨x, z⟩
      simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists, Prod.mk.injEq]
      simp only [and_left_comm (b := _ = x), eq_comm (b := z)]
      simp [and_assoc]

    _ = Set.encard {(x, z) : ℕ × ℕ |
        x ∈ Set.Ico 1 b ∧ z ∈ Set.Ico 2 b ∧ z * (z - 1) = x * (b - 1)} := by
      congr
      ext ⟨x, z⟩
      simp only [Set.mem_setOf_eq]
      refine and_congr_right fun hx ↦ ?_
      refine ⟨?_, ?_⟩
      · intro ⟨y, hy, h, hz⟩
        rw [hz]
        refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · -- Cannot have `x + y = 1` as it implies `1 ^ 2 = x * b + y` with `x ≠ 0` and `1 < b`.
            suffices 1 ^ 2 < (x + y) ^ 2 from lt_of_pow_lt_pow_left' 2 this
            suffices 2 ≤ x * b + y by simpa [h] using this
            refine Nat.le_add_right_of_le ?_
            exact le_mul_of_one_le_of_le hx.1 hb
          · -- Must have `x + y < b` since `(x + y) ^ 2 = x * b + y < b ^ 2` (two-digit numbers).
            suffices (x + y) ^ 2 < b ^ 2 from lt_of_pow_lt_pow_left' 2 this
            calc (x + y) ^ 2
            _ = x * b + y := h
            _ ≤ (b - 1) * b + (b - 1) := by
              refine add_le_add (Nat.mul_le_mul_right b ?_) ?_
              · exact Nat.le_sub_one_of_lt hx.2
              · exact Nat.le_sub_one_of_lt hy
            _ = (b + 1) * (b - 1) := by ring
            _ = b ^ 2 - 1 := (Nat.sq_sub_sq b 1).symm
            _ < b ^ 2 := by
              refine Nat.sub_lt ?_ one_pos
              exact Nat.pow_pos (Nat.zero_lt_of_lt hb)
        · calc _
          _ = (x + y) ^ 2 - (x + y) := by simp [sq, mul_tsub]
          _ = x * b + y - (x + y) := by rw [h]
          _ = x * b + y - y - x := by rw [Nat.sub_sub, add_comm x y]
          _ = _ := by simp [mul_tsub]
      · intro ⟨hz, h⟩
        cases lt_or_le z x with
        | inl hzx =>
          -- Contradiction: Cannot have z (z - 1) = x (b - 1) since z < x and z < b.
          refine h.not_lt.elim ?_
          refine Nat.mul_lt_mul'' hzx ?_
          exact Nat.sub_lt_sub_right (one_le_two.trans hz.1) hz.2
        | inr hxz =>
          use z - x
          refine ⟨tsub_lt_of_lt hz.2, ?_, (add_tsub_cancel_of_le hxz).symm⟩
          · calc _
            _ = z ^ 2 := by rw [Nat.add_sub_cancel' hxz]
            _ = z * (z - 1 + 1) := by rw [sq, Nat.sub_add_cancel (Nat.one_le_of_lt hz.1)]
            _ = x * b - x + z := by simp [h, mul_add, mul_tsub]
            _ = x * b + z - x := by
              refine (Nat.sub_add_comm ?_).symm
              exact Nat.le_mul_of_pos_right x (Nat.zero_lt_of_lt hb)
            _ = _ := Nat.add_sub_assoc hxz (x * b)

    -- Eliminate the constraint on `x`.
    -- TODO: Move into above?
    _ = Set.encard {(x, z) : ℕ × ℕ | z ∈ Set.Ico 2 b ∧ z * (z - 1) = x * (b - 1)} := by
      congr
      ext ⟨x, z⟩
      simp only [Set.mem_setOf_eq, and_iff_right_iff_imp, and_imp]
      intro hz h
      rw [Set.mem_Ico] at hz ⊢
      refine ⟨?_, ?_⟩
      · suffices x ≠ 0 from Nat.one_le_iff_ne_zero.mpr this
        intro hx
        revert h
        simp [hx]
        omega  -- TODO
      · suffices x * (b - 1) < b * (b - 1) from Nat.lt_of_mul_lt_mul_right this
        rw [← h]
        refine mul_lt_mul ?_ ?_ ?_ ?_
        · exact hz.2
        · omega  -- TODO
        · omega  -- TODO
        · exact Nat.zero_le b

    _ = Set.encard ((fun z ↦ (z * (z - 1) / (b - 1), z)) ''
        {z | z ∈ Set.Ico 2 b ∧ b - 1 ∣ z * (z - 1)}) := by
      congr
      ext ⟨x, z⟩
      simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq, exists_eq_right_right]
      simp only [and_assoc, and_congr_right_iff]
      intro hz
      refine ⟨?_, ?_⟩
      · intro h
        refine ⟨?_, ?_⟩
        · exact Dvd.intro_left x h.symm
        · refine (Nat.eq_div_of_mul_eq_left ?_ h.symm).symm
          exact (Nat.zero_lt_sub_of_lt hb).ne'
      · intro ⟨h, hx⟩
        exact Nat.eq_mul_of_div_eq_left h hx

    _ = Set.encard {z | z ∈ Set.Ico 2 b ∧ b - 1 ∣ z * (z - 1)} :=
      Function.Injective.encard_image (fun z z' ↦ by simp) _


  refine ⟨?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Nat.reduceLeDiff, Nat.add_one_sub_one, true_and]
    -- TODO: Rewrite `Finset.filter` as below?
    calc _
    _ = {z ∈ Finset.Ico 2 211 | 210 ∣ z * (z - 1)}.toSet.encard := by simp
    _ > 10 := by
      -- Convert to cardinality of a `Finset.filter`, which is decidable.
      simp only [Set.encard_coe_eq_coe_finsetCard, Nat.ofNat_lt_cast]
      decide

  rw [mem_lowerBounds]
  simp only [Set.mem_setOf_eq, and_imp]

  intro b hb
  suffices b < 211 → {z | z ∈ Set.Ico 2 b ∧ b - 1 ∣ z * (z - 1)}.encard ≤ 10 by simpa using mt this
  intro hb_lt


  calc _
  _ ≤ Set.encard ((fun (z, m, n) ↦ z) '' {(z, m, n) : ℕ × ℕ × ℕ | z ∈ Set.Ico 2 b ∧
      b - 1 = m * n ∧ m.Coprime n ∧ m ∣ z ∧ n ∣ z - 1}) := by
    refine Set.encard_le_card fun z ↦ ?_
    simp only [Set.mem_setOf_eq, Set.mem_image, Prod.exists, exists_and_right, exists_and_left,
      exists_eq_right, and_imp]
    refine fun hz h ↦ ⟨hz, ?_⟩  -- TODO: Avoid need for this?
    rw [Set.mem_Ico] at hz
    rw [dvd_mul] at h
    rcases h with ⟨m, n, hm, hn, h⟩
    use m, n
    refine ⟨h, ?_, hm, hn⟩
    refine Nat.Coprime.of_dvd hm hn ?_
    refine (Nat.coprime_self_sub_right ?_).mpr ?_
    · linarith
    · exact Nat.coprime_one_right z

  _ ≤ Set.encard {(z, m, n) : ℕ × ℕ × ℕ | z ∈ Set.Ico 2 b ∧
      b - 1 = m * n ∧ m.Coprime n ∧ m ∣ z ∧ n ∣ z - 1} :=
    Set.encard_image_le _ _

  _ = Set.encard ((fun (z, m, n) ↦ m) '' {(z, m, n) : ℕ × ℕ × ℕ | z ∈ Set.Ico 2 b ∧
      b - 1 = m * n ∧ m.Coprime n ∧ m ∣ z ∧ n ∣ z - 1}) := by
    refine (Set.InjOn.encard_image ?_).symm
    intro ⟨z, m, n⟩
    simp only [Set.mem_setOf_eq, and_imp, Prod.forall, Prod.mk.injEq]
    intro hz h_mul h_coprime hm hn z' m' n' hz' h_mul' h_coprime' hm' hn' hm_eq
    have hm_pos : 0 < m := by
      suffices 0 < m * n from Nat.pos_of_mul_pos_right this
      exact h_mul ▸ Nat.zero_lt_sub_of_lt hb
    have hn_eq : n = n' := by
      rw [← Nat.mul_right_inj hm_pos.ne', ← h_mul]
      rw [h_mul', hm_eq]
    refine ⟨?_, hm_eq, hn_eq⟩
    -- Eliminate m' and n'.
    simp only [← hm_eq, ← hn_eq] at hm' hn'
    clear h_mul' h_coprime' hm_eq hn_eq m' n'
    -- Without loss of generality, assume `z ≤ z'`.
    wlog h_le : z ≤ z' generalizing z z'
    · symm
      exact this z' hz' hm' hn' z hz hm hn (Nat.le_of_not_ge h_le)
    -- Since `m ∣ z' - z`, `n ∣ z' - z` and `m.Coprime n`, we know `b - 1 = m * n ∣ z' - z`.
    have h_dvd : b - 1 ∣ z' - z := by
      rw [h_mul]
      refine h_coprime.mul_dvd_of_dvd_of_dvd ?_ ?_
      · exact Nat.dvd_sub' hm' hm
      · convert Nat.dvd_sub' hn' hn using 1
        refine (Nat.sub_sub_sub_cancel_right ?_).symm
        exact Nat.one_le_of_lt hz.1
    obtain ⟨k, hk⟩ := h_dvd
    replace hk : z' = z + (b - 1) * k := (Nat.sub_eq_iff_eq_add' h_le).mp hk
    -- Now we can prove that `k = 0` using `z < b`.
    cases k with
    | zero => simpa using hk.symm
    | succ k =>
      exfalso
      revert hz'
      suffices b ≤ z' from mt And.right this.not_lt
      calc _
      _ = 1 + (b - 1) := by omega
      _ ≤ z + (b - 1) * k.succ := by
        refine add_le_add ?_ ?_
        · exact Nat.one_le_of_lt hz.1
        · exact Nat.le_mul_of_pos_right (b - 1) (Nat.succ_pos k)
      _ = z' := hk.symm

  _ ≤ Set.encard {m : ℕ | ∃ n, b - 1 = m * n ∧ m.Coprime n} := by
    refine Set.encard_le_card fun m ↦ ?_
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists, exists_and_right, exists_and_left,
      exists_eq_right, forall_exists_index, and_imp]
    exact fun z _ n h_mul h_coprime _ _ ↦ ⟨n, h_mul, h_coprime⟩

  _ ≤ Set.encard {m : ℕ | ∃ a ⊆ (b - 1).primeFactors,
      ∏ p in a, p ^ (b - 1).factorization p = m} := by
    refine Set.encard_le_card fun m ↦ ?_
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro n h_mul h_coprime
    rw [h_mul]
    use m.primeFactors
    have h_pos : 0 < m * n := h_mul ▸ Nat.zero_lt_sub_of_lt hb
    refine ⟨Nat.primeFactors_mono (Nat.dvd_mul_right m n) h_pos.ne', ?_⟩
    calc _
    _ = ∏ p ∈ m.primeFactors, p ^ m.factorization p := by
      refine Finset.prod_congr rfl fun p hp ↦ ?_
      congr 1
      refine Nat.factorization_eq_of_coprime_left h_coprime ?_
      simpa using hp
    _ = _ := by
      refine Nat.factorization_prod_pow_eq_self ?_
      exact (Nat.pos_of_mul_pos_right h_pos).ne'

  -- TODO: Use directly above?
  _ = Set.encard ((fun a ↦ ∏ p in a, p ^ (b - 1).factorization p) ''
      {a | a ⊆ (b - 1).primeFactors}) :=
    rfl

  _ ≤ Set.encard {a | a ⊆ (b - 1).primeFactors} := Set.encard_image_le _ _

  _ = Set.encard {a | a ∈ (b - 1).primeFactors.powerset} := by simp

  -- _ = (b - 1).primeFactors.powerset.toSet.encard := rfl

  _ = (b - 1).primeFactors.powerset.card := Set.encard_coe_eq_coe_finsetCard _
  _ = 2 ^ (b - 1).primeFactors.card := by simp

  _ ≤ 2 ^ 3 := by
    refine pow_le_pow_right₀ one_le_two ?_
    -- Now we need to show that any number less than 2 * 3 * 5 * 7 has less than 4 prime factors.
    suffices (b - 1).primeFactors.card < 4 from Nat.le_of_lt_succ this
    replace hb_lt : b - 1 < 210 := Nat.sub_lt_left_of_lt_add (Nat.one_le_of_lt hb) hb_lt
    revert hb_lt
    suffices 4 ≤ (b - 1).primeFactors.card → 210 ≤ b - 1 by simpa using mt this
    intro h_card

    -- It will be cleaner to prove a more general proposition.
    -- Any set of `n` (distinct) elements that satisfy a predicate `p` will have a product
    -- greater or equal to that of the `n` smallest elements satisfying the predicate.
    suffices ∀ (p : ℕ → Prop) [DecidablePred p] (s : Finset ℕ), (∀ x ∈ s, p x) →
        (setOf p).Infinite → ∏ x in .filter p (.range (Nat.nth p s.card)), x ≤ ∏ x in s, x from
      calc _
      -- 210 is equal to the product of the first 4 primes, i.e. the primes less than 11.
      _ = ∏ p in .filter Nat.Prime (.range 11), p := rfl
      _ = ∏ p in .filter Nat.Prime (.range (Nat.nth Nat.Prime 4)), p := by
        suffices Nat.nth Nat.Prime 4 = 11 by rw [this]
        exact Nat.nth_count (by decide : Nat.Prime 11)
      _ ≤ ∏ p in .filter Nat.Prime (.range (Nat.nth Nat.Prime (b - 1).primeFactors.card)), p := by
        refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
        · gcongr
          exact Nat.nth_monotone Nat.infinite_setOf_prime h_card
        · exact fun p hp _ ↦ (Nat.prime_of_mem_primesBelow hp).one_le
      -- Apply the general proposition to `(b - 1).primeFactors`.
      _ ≤ ∏ p in (b - 1).primeFactors, p :=
        this Nat.Prime (b - 1).primeFactors (fun _ ↦ Nat.prime_of_mem_primeFactors)
          Nat.infinite_setOf_prime
      _ ≤ ∏ p in (b - 1).primeFactors, p ^ (b - 1).factorization p := by
        refine Finset.prod_le_prod' fun p hp ↦ Nat.le_self_pow ?_ p
        exact Finsupp.mem_support_iff.mp hp
      _ = _ := Nat.factorization_prod_pow_eq_self (Nat.zero_lt_sub_of_lt hb).ne'


    -- Perform induction on the size of the set.
    -- We will remove the largest element from each set and recurse on the remainder.
    intro p _ s hs hp
    generalize hn : s.card = n
    induction n generalizing s with
    | zero =>
      -- Both sides are products over empty sets.
      have h_left : Finset.filter p (.range (Nat.nth p 0)) = ∅ := by
        refine Finset.card_eq_zero.mp ?_
        rw [← Nat.count_eq_card_filter_range]
        exact Nat.count_nth_zero p
      have h_right : s = ∅ := Finset.card_eq_zero.mp hn
      simp [h_left, h_right]
    | succ n IH =>
      -- Split the maximum element from the product on the left.
      rw [Nat.filter_range_nth_eq_insert_of_infinite hp n]
      rw [Finset.prod_insert (by simp)]
      -- Split the maximum element from the product on the right.
      have hs_ne : s.Nonempty := Finset.card_pos.mp (hn ▸ Nat.zero_lt_succ n)
      rw [← Finset.insert_erase (Finset.max'_mem s hs_ne)]
      rw [Finset.prod_insert (s.not_mem_erase _)]
      refine Nat.mul_le_mul ?_ ?_
      · -- Use `Nat.lt_nth_iff_count_lt` to rewrite `nth` as `count`.
        -- Then use `Nat.count_eq_card_filter_range` to rewrite `count` as `card`.
        -- Then show that `s` is a subset of `range`.
        suffices Nat.nth p n < s.max' hs_ne + 1 from Nat.le_of_lt_succ this
        rw [← Nat.lt_nth_iff_count_lt hp]
        suffices n + 1 ≤ Nat.count p (s.max' hs_ne + 1) from Nat.lt_of_succ_le this
        rw [← hn, Nat.count_eq_card_filter_range]
        refine Finset.card_le_card fun x hx ↦ ?_
        simpa [Nat.lt_succ] using ⟨s.le_max' x hx, hs x hx⟩
      · -- Use induction for the products over all other elements.
        refine IH (s.erase (s.max' hs_ne)) ?_ ?_
        · simpa using fun x _ ↦ hs x
        · rw [Finset.card_erase_of_mem (Finset.max'_mem s hs_ne)]
          exact Nat.sub_eq_of_eq_add hn

  2 ^ 3 ≤ 10 := by norm_num
