-- https://cloud.kili-technology.com/label/projects/label/cm84mpwv701xiiev518ak3u3v
-- https://artofproblemsolving.com/wiki/index.php/2024_AIME_II_Problems/Problem_14

import Mathlib

open Real

/- Let $b\ge 2$ be an integer.
Call a positive integer $n$ $b$-eautiful if it has exactly two digits
when expressed in base $b$ and these two digits sum to $\sqrt n$.
For example, $81$ is $13$-eautiful because $81 = 63_{13}$ and $6 + 3 = \sqrt{81}$.
Find the least integer $b \ge 2$ for which there are more than ten $b$-eautiful integers. -/

theorem number_theory_93241 :
    IsLeast {b | 2 ≤ b ∧
      {n | (Nat.digits b n).length = 2 ∧ (Nat.digits b n).sum = sqrt n}.encard > 10} 211 := by
  suffices IsLeast {b | 2 ≤ b ∧ 10 < {z | z ∈ Set.Ico 2 b ∧ b - 1 ∣ z * (z - 1)}.encard} 211 by
    convert this using 3 with b
    refine and_congr_right fun hb ↦ ?_
    suffices {n | (Nat.digits b n).length = 2 ∧ (Nat.digits b n).sum = sqrt n}.encard =
        {z | z ∈ Set.Ico 2 b ∧ b - 1 ∣ z * (z - 1)}.encard by
      rw [this]

    calc _
    -- Parameterize using digits `x, y`.
    _ = Set.encard ((fun (x, y) ↦ Nat.ofDigits b [y, x]) ''
        {(x, y) : ℕ × ℕ | x ∈ Set.Ico 1 b ∧ y < b ∧ (x + y) ^ 2 = x * b + y}) := by
      congr
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_image, Prod.exists]
      calc _
      -- Move square root constraint from `ℝ` to `ℕ`.
      _ ↔ (Nat.digits b n).length = 2 ∧ (Nat.digits b n).sum ^ 2 = n := by
        suffices ∀ (u v : ℕ), u = √v ↔ u ^2 = v by simp only [this]
        intro u v
        calc _
        _ ↔ √v = u := eq_comm
        _ ↔ (v : ℝ) = u ^ 2 := sqrt_eq_iff_eq_sq (Nat.cast_nonneg' v) (Nat.cast_nonneg' u)
        _ ↔ (v : ℝ) = ↑(u ^ 2) := by simp
        _ ↔ v = u ^ 2 := Nat.cast_inj
        _ ↔ _ := eq_comm

      -- Obtain the two elements in the list explicitly.
      _ ↔ ∃ y x, (y + x) ^ 2 = n ∧ Nat.digits b n = [y, x] := by
        generalize hl : b.digits n = l
        cases l with
        | nil => simp  -- Contradiction on both sides: length is not 0.
        | cons y l =>
          simp only [List.cons.injEq, and_assoc, exists_and_left, exists_eq_left']
          cases l with
          | nil => simp  -- Contradiction on both sides: length is not 1.
          | cons x l =>
            simp only [List.cons.injEq, and_assoc, exists_and_left, exists_eq_left']
            cases l with
            | cons w l => simp  -- Contradiction on both sides: length is not 3.
            | nil => simp

      -- Parameterize by the digits (x, y) rather than the number n.
      _ ↔ ∃ y x, (y + x) ^ 2 = n ∧ y < b ∧ x < b ∧ x ≠ 0 ∧ Nat.ofDigits b [y, x] = n := by
        refine exists_congr fun y ↦ exists_congr fun x ↦ and_congr_right fun _ ↦ ?_
        refine Iff.intro ?_ ?_
        · intro h
          refine ⟨?_, ?_, ?_, ?_⟩
          · suffices y ∈ b.digits n from Nat.digits_lt_base hb this
            simp [h]
          · suffices x ∈ b.digits n from Nat.digits_lt_base hb this
            simp [h]
          · convert Nat.getLast_digit_ne_zero b (?_ : n ≠ 0)
            · simp [h]
            · suffices b.digits n ≠ [] from Nat.digits_ne_nil_iff_ne_zero.mp this
              simp [h]
          · exact h ▸ Nat.ofDigits_digits b n
        · intro ⟨hy, hx, hx_ne, hn⟩
          rw [← hn]
          refine Nat.digits_ofDigits b hb _ ?_ ?_
          · simpa using ⟨hy, hx⟩
          · simpa using hx_ne

      -- Put everything in its final form.
      _ ↔ _ := by
        rw [exists_comm]
        refine exists_congr fun x ↦ exists_congr fun y ↦ ?_
        simp only [← and_assoc (c := _ = n)]
        refine and_congr_left fun hn ↦ ?_
        -- Normalize the forms of the constraints.
        replace hn : x * b + y = n :=
          calc _
          _ = y + b * x := by ring
          _ = Nat.ofDigits b [y, x] := by simp [Nat.ofDigits_cons]
          _ = _ := hn
        simp only [add_comm y x, hn, Set.mem_Ico, Nat.one_le_iff_ne_zero]
        refine ⟨?_, ?_⟩
        · exact fun ⟨h_sq, hy, hx, hx_ne⟩ ↦ ⟨⟨hx_ne, hx⟩, hy, h_sq⟩
        · exact fun ⟨⟨hx_ne, hx⟩, hy, h_sq⟩ ↦ ⟨h_sq, hy, hx, hx_ne⟩

    -- Use injectivity of `Nat.ofDigits` to eliminate the image.
    _ = Set.encard {(x, y) : ℕ × ℕ | x ∈ Set.Ico 1 b ∧ y < b ∧ (x + y) ^ 2 = x * b + y} := by
      refine Set.InjOn.encard_image ?_
      -- Note: More recent versions of Mathlib have `Nat.ofDigits_inj_of_len_eq`.
      simp only [Set.InjOn, Set.mem_setOf_eq, and_imp, Prod.forall, Prod.mk.injEq]
      intro x y _ hy hxy x' y' _ hy' _
      simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero]
      intro h
      -- Use `ℕ × Fin b` from `Nat.divModEquiv`.
      suffices (x, (⟨y, hy⟩ : Fin b)) = (x', ⟨y', hy'⟩) by simpa using this
      have _ : NeZero b := .of_gt hb
      refine (Nat.divModEquiv b).symm.injective ?_
      simp only [Nat.divModEquiv_symm_apply]
      refine (Eq.congr ?_ ?_).mpr h <;> ring

    -- Consider the set of `(x, x + y)` rather than that of `(x, y)`.
    -- Cardinality is preserved by injectivity.
    _ = Set.encard ((fun m ↦ (m.1, m.1 + m.2)) ''
        {(x, y) : ℕ × ℕ | x ∈ Set.Ico 1 b ∧ y < b ∧ (x + y) ^ 2 = x * b + y}) := by
      refine (Function.Injective.encard_image ?_ _).symm
      simp only [Function.Injective, Prod.mk.injEq, and_imp, Prod.forall]
      exact fun x y x' y' hx hz ↦ ⟨hx, Nat.add_left_cancel (hx ▸ hz)⟩

    -- Remove the explicit constraints on the range of `x`.
    _ = Set.encard {(x, z) : ℕ × ℕ | z ∈ Set.Ico 2 b ∧ z * (z - 1) = x * (b - 1)} := by
      congr
      ext ⟨x, z⟩
      simp only [Set.mem_image, Set.mem_setOf_eq, Prod.mk.injEq, Prod.exists]
      simp only [and_left_comm (b := _ = x), exists_and_left, exists_eq_left]
      simp only [and_assoc, exists_and_left]
      simp only [Set.mem_Ico]
      -- The b-eautiful condition is equivalent to `z (z - 1) = x (b - 1)` with `z = x + y`.
      have h_beautifful (y) : (x + y) ^ 2 = x * b + y ↔ (x + y) * (x + y - 1) = x * (b - 1) := by
        calc _
        _ ↔ (x + y) ^ 2 = x * b - x + x + y := by
          rw [Nat.sub_add_cancel]
          refine Nat.le_mul_of_pos_right x ?_
          linarith
        _ ↔ (x + y) ^ 2 = x * b - x + (x + y) := by simp [add_assoc]
        _ ↔ (x + y) ^ 2 - (x + y) = x * b - x := by
          refine (Nat.sub_eq_iff_eq_add ?_).symm
          refine Nat.le_self_pow ?_ _
          norm_num
        _ ↔ (x + y) * (x + y - 1) = x * (b - 1) := by simp [mul_tsub, sq]
      refine Iff.intro ?_ ?_
      · intro ⟨hx, y, hy, h_eq, hz⟩
        rw [← hz]
        refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · -- Cannot have `x + y = 1` as it implies `1 ^ 2 = x * b + y` with `x ≠ 0` and `1 < b`.
            suffices 1 ^ 2 < (x + y) ^ 2 from lt_of_pow_lt_pow_left' 2 this
            suffices 2 ≤ x * b + y by simpa [h_eq] using this
            refine Nat.le_add_right_of_le ?_
            exact le_mul_of_one_le_of_le hx.1 hb
          · -- Must have `x + y < b` since `(x + y) ^ 2 = x * b + y < b ^ 2` (two-digit numbers).
            suffices (x + y) ^ 2 < b ^ 2 from lt_of_pow_lt_pow_left' 2 this
            calc (x + y) ^ 2
            _ = x * b + y := h_eq
            _ ≤ (b - 1) * b + (b - 1) := by
              refine add_le_add (Nat.mul_le_mul_right b ?_) ?_
              · exact Nat.le_sub_one_of_lt hx.2
              · exact Nat.le_sub_one_of_lt hy
            _ = (b + 1) * (b - 1) := by ring
            _ = b ^ 2 - 1 := (Nat.sq_sub_sq b 1).symm
            _ < b ^ 2 := by
              refine Nat.sub_lt ?_ one_pos
              exact Nat.pow_pos (Nat.zero_lt_of_lt hb)
        · exact (h_beautifful y).mp h_eq
      · intro ⟨hz, h_eq⟩
        -- Must have `x ≤ z = x + y`.
        cases lt_or_le z x with
        | inl hzx =>
          exfalso
          refine h_eq.not_lt ?_
          refine Nat.mul_lt_mul'' hzx ?_
          refine Nat.sub_lt_sub_right ?_ ?_ <;> linarith
        | inr hxz =>
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · suffices 0 < x * (b - 1) from Nat.pos_of_mul_pos_right this
            rw [← h_eq]
            refine Nat.mul_pos ?_ (Nat.zero_lt_sub_of_lt ?_) <;> linarith
          · linarith
          use z - x
          refine ⟨tsub_lt_of_lt hz.2, ?_, Nat.add_sub_of_le hxz⟩
          refine (h_beautifful (z - x)).mpr ?_
          simpa [Nat.add_sub_of_le hxz] using h_eq

    -- Suffices to consider `z` since `x` is determined by `z`.
    _ = Set.encard (Prod.snd ''
        {(x, z) : ℕ × ℕ | z ∈ Set.Ico 2 b ∧ z * (z - 1) = x * (b - 1)}) := by
      refine (Set.InjOn.encard_image ?_).symm
      simp only [Set.InjOn, Set.mem_setOf_eq, and_imp, Prod.forall, Prod.mk.injEq]
      intro x z hz h_eq x' z' hz' h_eq'
      refine fun h ↦ ⟨?_, h⟩
      suffices x * (b - 1) = x' * (b - 1) by
        refine Nat.eq_of_mul_eq_mul_right ?_ this
        exact Nat.zero_lt_sub_of_lt hb
      rw [← h_eq, ← h_eq', ← h]

    -- Replace the existence of some `x` with divisibility.
    _ = Set.encard {z | z ∈ Set.Ico 2 b ∧ b - 1 ∣ z * (z - 1)} := by
      congr
      ext z
      simp [dvd_iff_exists_eq_mul_left]

  refine ⟨?_, ?_⟩
  · -- As will be shown below, it suffices to consider `z = c * m` and `z - 1 = d * m`
    -- where `m` and `n` are coprime and `b - 1 = m * n`.
    -- That is, `m` and `n` correspond to a partition of the prime factors of `b - 1`.
    -- To find `c` and `d`, we require `1 = c * m - d * n` with `0 ≤ c, d`.
    -- Since `m` and `n` are coprime, the extended Euclidean algorithm can be used.
    -- Here, we simply check all `z` in the range `2 ≤ z < b` exhaustively.
    simp only [Set.mem_setOf_eq]
    refine ⟨by norm_num, ?_⟩
    calc _
    _ = {z ∈ Finset.Ico 2 211 | 210 ∣ z * (z - 1)}.toSet.encard := by simp
    _ > 10 := by
      -- Convert to cardinality of a `Finset.filter`, which is decidable.
      simp only [Set.encard_coe_eq_coe_finsetCard, Nat.ofNat_lt_cast]
      decide

  rw [mem_lowerBounds]
  simp only [Set.mem_setOf_eq, and_imp]
  intro b hb
  -- Prove the contrapositive.
  suffices b < 211 → {z | z ∈ Set.Ico 2 b ∧ b - 1 ∣ z * (z - 1)}.encard ≤ 10 by simpa using mt this
  intro hb_lt

  calc _
  -- Consider explicit factors `m * n = b - 1`.
  _ = Set.encard ((fun (z, m, n) ↦ z) '' {(z, m, n) : ℕ × ℕ × ℕ | z ∈ Set.Ico 2 b ∧
      m.Coprime n ∧ m ∣ z ∧ n ∣ z - 1 ∧ b - 1 = m * n}) := by
    congr
    ext z
    simp only [Set.mem_Ico, Set.mem_setOf_eq, Set.mem_image, Prod.exists, exists_and_right,
      exists_and_left, exists_eq_right, and_congr_right_iff]
    intro hz
    rw [dvd_mul]
    refine exists_congr fun m ↦ ?_
    refine exists_congr fun n ↦ ?_
    simp only [iff_and_self, and_imp]
    intro hm hn h_mul
    refine Nat.Coprime.of_dvd hm hn ?_
    refine (Nat.coprime_self_sub_right ?_).mpr ?_
    · linarith
    · exact Nat.coprime_one_right z
  _ ≤ Set.encard {(z, m, n) : ℕ × ℕ × ℕ | z ∈ Set.Ico 2 b ∧
      m.Coprime n ∧ m ∣ z ∧ n ∣ z - 1 ∧ b - 1 = m * n} :=
    Set.encard_image_le _ _
  -- It suffices to consider the unique `(m, n)`, since there is at most one `z` for each.
  _ = Set.encard ((fun (z, m, n) ↦ (m, n)) '' {(z, m, n) : ℕ × ℕ × ℕ | z ∈ Set.Ico 2 b ∧
      m.Coprime n ∧ m ∣ z ∧ n ∣ z - 1 ∧ b - 1 = m * n}) := by
    refine (Set.InjOn.encard_image ?_).symm
    intro ⟨z, m, n⟩
    simp only [Set.mem_setOf_eq, and_imp, Prod.forall, Prod.mk.injEq]
    intro hz h_coprime hm hn h_mul z' m' n' hz' h_coprime' hm' hn' h_mul' hm_eq hn_eq
    refine ⟨?_, hm_eq, hn_eq⟩
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
  -- Ignore the existence of `z` to obtain an upper bound.
  _ ≤ Set.encard {(m, n) : ℕ × ℕ | m.Coprime n ∧ b - 1 = m * n} := by
    refine Set.encard_le_card fun ⟨m, n⟩ ↦ ?_
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists, exists_eq_right, forall_exists_index]
    exact fun z ⟨_, h_coprime, _, _, h_mul⟩ ↦ ⟨h_coprime, h_mul⟩
  -- We can easily compute `n` from `m`.
  _ ≤ Set.encard ((fun m ↦ (m, (b - 1) / m)) '' {m | ∃ n, m.Coprime n ∧ b - 1 = m * n}) := by
    refine Set.encard_le_card fun ⟨m, n⟩ ↦ ?_
    simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq, and_left_comm, exists_eq_left]
    intro ⟨h_coprime, h_mul⟩
    refine ⟨⟨n, h_coprime, h_mul⟩, ?_⟩
    refine Nat.div_eq_of_eq_mul_right ?_ h_mul
    suffices 0 < m * n from Nat.pos_of_mul_pos_right this
    exact h_mul ▸ Nat.zero_lt_sub_of_lt hb
  _ ≤ Set.encard {m | ∃ n, m.Coprime n ∧ b - 1 = m * n} := Set.encard_image_le _ _
  -- It suffices to consider partitions of the prime factors of (b - 1).
  _ ≤ Set.encard ((fun a ↦ ∏ p in a, p ^ (b - 1).factorization p) ''
      {a | a ⊆ (b - 1).primeFactors}) := by
    refine Set.encard_le_card fun m ↦ ?_
    simp only [Set.mem_setOf_eq, Set.mem_image, forall_exists_index, and_imp]
    intro n h_coprime h_mul
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
  -- This provides a simple upper bound using the size of the powerset (2 ^ card).
  _ ≤ Set.encard {a | a ⊆ (b - 1).primeFactors} := Set.encard_image_le _ _
  _ = Set.encard {a | a ∈ (b - 1).primeFactors.powerset} := by simp
  _ = (b - 1).primeFactors.powerset.card := Set.encard_coe_eq_coe_finsetCard _
  _ = 2 ^ (b - 1).primeFactors.card := by simp
  _ ≤ 2 ^ 3 := by
    refine pow_le_pow_right₀ one_le_two ?_
    -- We must now show that any number less than 2 * 3 * 5 * 7 has less than 4 prime factors.
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
