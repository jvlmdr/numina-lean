-- https://cloud.kili-technology.com/label/projects/review/cm84mpwv601vyiev5u7vtl93e
-- https://artofproblemsolving.com/wiki/index.php/2012_AIME_I_Problems/Problem_10

import Mathlib

open scoped Pointwise

/- Let S be the set of all perfect squares whose rightmost three digits in base 10 are 256.
Let T be the set of all numbers of the form $\frac{x - 256}{1000}$, where $x$ is in S.
In other words, T is the set of numbers that result when the last three digits
of each number in S are truncated.
Find the remainder when the tenth smallest element of T is divided by $1000$. -/

theorem number_theory_30933 (s t : Set ℕ)
    (hs : s = {m : ℕ | m % 1000 = 256 ∧ ∃ k, m = k ^ 2})
    (ht : t = {n : ℕ | ∃ m ∈ s, n = m / 1000}) :
    Nat.nth (· ∈ t) 9 % 1000 = 170 := by

  -- Every `m ∈ s` can be written as `1000 * n + 256`.
  -- This means we can write `s = {m | (∃ n, m = 1000 * n + 256) ∧ ∃ k, m = k ^ 2}` with
  -- `t = {n | ∃ k, 1000 * n + 256 = k ^ 2}` and `u = {k | ∃ n, 1000 * n + 256 = k ^ 2}`.
  -- Or equivalently, `s = Set.range (1000 * · + 256) ∩ Set.range (· ^ 2)` with
  -- `t = (1000 * · + 256) ⁻¹' s` and `u = (· ^ 2) ⁻¹' s`.

  generalize hu : {k | ∃ n, 1000 * n + 256 = k ^ 2} = u
  replace hu := hu.symm

  -- TODO: Better to obtain this using new definition of `s`?
  -- First obtain `t` using old definition of `s` with modulo.
  replace ht : t = {n | ∃ k, 1000 * n + 256 = k ^ 2} := by
    refine ht.trans ?_
    rw [hs]
    simp only [Set.mem_setOf_eq, and_right_comm]
    -- Re-arrange to use `Nat.div_mod_unique`.
    simp only [and_comm, eq_comm (b := (_ / 1000 : ℕ))]
    simp only [Nat.div_mod_unique (by norm_num : 0 < 1000)]
    simp only [add_comm]  -- TODO: Use `256 + 1000 * n` instead?
    norm_num

  -- TODO: Some way to avoid this definition?
  have h_mod_eq_of_lt (m : ℕ) {r d : ℕ} (hr : r < d) : m % d = r ↔ ∃ n, m = d * n + r := by
    suffices r ≤ m → (m % d = r ↔ ∃ n, m = d * n + r) by
      refine (iff_congr ?_ ?_).mpr (and_congr_right this)
      · refine iff_and_self.mpr fun h ↦ ?_
        simpa only [← h] using Nat.mod_le m d
      · refine iff_and_self.mpr fun h ↦ ?_
        rcases h with ⟨n, hn⟩
        simpa only [hn] using Nat.le_add_left r _
    intro hrm
    calc _
    _ ↔ m % d = r % d := by rw [Nat.mod_eq_of_lt hr]
    _ ↔ r ≡ m [MOD d] := Nat.ModEq.comm
    _ ↔ d ∣ m - r := Nat.modEq_iff_dvd' hrm
    _ ↔ ∃ n, m - r = d * n := dvd_iff_exists_eq_mul_right
    _ ↔ _ := exists_congr fun n ↦ Nat.sub_eq_iff_eq_add hrm

  replace hs : s = {m | (∃ n, m = 1000 * n + 256) ∧ ∃ k, m = k ^ 2} := by
    refine hs.trans ?_
    simp only [h_mod_eq_of_lt _ (by norm_num : 256 < 1000)]

  -- Now we have `s, t, u` in standard form.
  -- We can write `s = f '' t = g '' u` with `f, g` strict monotone.
  have hf_mono : StrictMono (fun n ↦ 1000 * n + 256) :=
    .add_const (.const_mul strictMono_id (by norm_num)) _
  have hg_mono : StrictMono (fun k : ℕ ↦ k ^ 2) := Nat.pow_left_strictMono two_ne_zero
  have hst : s = (1000 * · + 256) '' t := by
    rw [hs, ht]
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_image]
    simp only [← exists_and_right, ← exists_and_left, eq_comm (b := m)]
    rw [exists_comm]
    refine exists_congr fun n ↦ ?_
    refine exists_congr fun k ↦ ?_
    rw [and_comm]
    refine and_congr_left fun hm ↦ ?_
    rw [hm]
  have hsu : s = (· ^ 2) '' u := by
    rw [hs, hu]
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_image]
    simp only [← exists_and_right, ← exists_and_left, eq_comm (a := m)]
    refine exists_congr fun k ↦ ?_
    refine exists_congr fun n ↦ ?_
    refine and_congr_left fun hm ↦ ?_
    rw [hm]

  -- Examine the condition for `k ∈ u`: `∃ n, 1000 * n + 256 = k ^ 2`.
  -- Since 256 = 16 ^ 2, we can rewrite this as `1000 ∣ (k + 16) * (k - 16)` with `16 ≤ k`.
  -- Note that `1000 = (2 * 5) ^ 3` and the gap on the right is `(k + 16) - (k - 16) = 32`.
  -- We can consider the primes separately, meaning both 2 ^ 3 and 5 ^ 3 divide the product.
  -- Since `2 ^ k ∣ 32` for all `k ≤ 5`, we must have `2 ^ 2 ∣ k + 16` and `2 ^ 2 ∣ k - 16`.
  -- Since `¬5 ∣ 32`, exact one of `k + 16` and `k - 16` must be divisible by 5 ^ 3.
  -- Putting this together gives `k = 500n ± 16`, or `k % 500 ∈ {16, 484}`.

  -- A coprime product divides a number iff each factor divides the number.
  -- This will be needed several times.
  have h_coprime_mul_dvd_iff {a b : ℕ} (hab : a.Coprime b) (x : ℕ) :
      a * b ∣ x ↔ a ∣ x ∧ b ∣ x := by
    constructor
    · exact fun h ↦ ⟨dvd_of_mul_right_dvd h, dvd_of_mul_left_dvd h⟩
    · exact fun ⟨ha, hb⟩ ↦ hab.mul_dvd_of_dvd_of_dvd ha hb

  -- A prime power divides a product iff both factors are prime powers.
  -- TODO: Excessive. Can this be obtained using `IsPrimePow` or `Nat.factorization`?
  have h_prime_pow_dvd_iff {x y p k : ℕ} (hp : p.Prime) :
      p ^ k ∣ x * y ↔ ∃ a b, p ^ a ∣ x ∧ p ^ b ∣ y ∧ k = a + b := by
    cases eq_or_ne x 0 with
    | inl hx =>
      simp only [hx, zero_mul, dvd_zero, true_and, true_iff]
      exact ⟨k, 0, by simp⟩
    | inr hx =>
      cases eq_or_ne y 0 with
      | inl hy =>
        simp only [hy, mul_zero, dvd_zero, true_and, true_iff]
        exact ⟨0, k, by simp⟩
      | inr hy =>
        calc p ^ k ∣ x * y
        _ ↔ k ≤ (x * y).factorization p := by
          rw [hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero hx hy)]
        _ ↔ k ≤ x.factorization p + y.factorization p := by
          simp [Nat.factorization_mul hx hy]
        _ ↔ ∃ a b, a ≤ x.factorization p ∧ b ≤ y.factorization p ∧ k = a + b := by
          constructor
          · intro hk
            refine ⟨k ⊓ x.factorization p, k - k ⊓ x.factorization p, ?_, ?_, ?_⟩
            · simp
            · rw [tsub_le_iff_left, ← Nat.add_min_add_right]
              simp [hk]
            · simp
          · simp only [exists_and_left, forall_exists_index, and_imp]
            intro a ha b hb hk
            rw [hk]
            gcongr
        _ ↔ _ := by
          refine exists_congr fun a ↦ exists_congr fun b ↦ ?_
          refine and_congr (hp.pow_dvd_iff_le_factorization hx).symm ?_
          refine and_congr (hp.pow_dvd_iff_le_factorization hy).symm ?_
          rfl

  -- If a prime power divides a product, and the gap is not divisible by the prime,
  -- then the prime power divides one or the other.
  -- TODO: Excessive. Can this be obtained more easily?
  have h_prime_pow_dvd_mul_add_of_not_dvd (x r k : ℕ) {p : ℕ} (hp : p.Prime) (hr : ¬p ∣ r) :
      p ^ k ∣ x * (x + r) ↔ p ^ k ∣ x ∨ p ^ k ∣ x + r := by
    cases k.eq_zero_or_pos with
    | inl hk => simp [hk]
    | inr hk =>
      refine ⟨?_, fun h ↦ h.elim (fun h ↦ h.mul_right (x + r)) (fun h ↦ h.mul_left x)⟩
      rw [h_prime_pow_dvd_iff hp]
      simp only [forall_exists_index, and_imp]
      intro a b hx hy hab
      cases a.eq_zero_or_pos with
      | inl ha => simp [hab, ha, hy]
      | inr ha =>
        cases b.eq_zero_or_pos with
        | inl hb => simp [hab, hb, hx]
        | inr hb =>
          refine (hr ?_).elim
          replace hx : p ∣ x := Nat.dvd_of_pow_dvd ha hx
          replace hy : p ∣ x + r := Nat.dvd_of_pow_dvd hb hy
          exact (Nat.dvd_add_iff_right hx).mpr hy

  have h_iff_mod (k) : (∃ n, 1000 * n + 256 = k ^ 2) ↔ k % 500 = 16 ∨ k % 500 = 484 := by
    -- Introduce the assumption that `16 ≤ k` by showing that it follows from both sides.
    suffices 16 ≤ k → ((∃ n, 1000 * n + 256 = k ^ 2) ↔ k % 500 = 16 ∨ k % 500 = 484) by
      refine (iff_congr ?_ ?_).mp (and_congr_right this)
      · refine and_iff_right_of_imp ?_
        simp only [and_iff_right_iff_imp, forall_exists_index]
        intro n hn
        rw [← hg_mono.le_iff_le, ← hn]
        simp
      · simp only [and_iff_right_iff_imp]
        refine fun h ↦ h.elim (fun h ↦ ?_) fun h ↦ ?_
        · refine le_trans (by simp [h]) (Nat.mod_le k 500)
        · refine le_trans (by simp [h]) (Nat.mod_le k 500)

    intro hk
    have hk_sub_add : k - 16 + 32 = k + 16 := by
      rw [← Nat.sub_add_comm hk, Nat.add_sub_assoc (by norm_num)]

    -- Establish the results for 2 ^ 3 and 5 ^ 3 as divisors.
    have h2_iff_of_le (m) (hm : m ≤ 5) : 2 ^ m ∣ k - 16 ↔ 2 ^ m ∣ k + 16 := by
      rw [← hk_sub_add]
      exact Nat.dvd_add_iff_left (Nat.pow_dvd_pow_iff_le_right'.mpr hm)
    have h2 : 2 ^ 3 ∣ (k - 16) * (k + 16) ↔ 2 ^ 2 ∣ k - 16 ∧ 2 ^ 2 ∣ k + 16 := by
      -- The reverse direction is trivial.
      refine ⟨?_, fun ⟨hx, hy⟩ ↦ .trans (by norm_num) (Nat.mul_dvd_mul hx hy)⟩
      rw [h2_iff_of_le 2 (by norm_num), and_self]
      rw [h_prime_pow_dvd_iff Nat.prime_two]
      simp only [forall_exists_index, and_imp]
      intro a b hx hy hab
      have ha : a = 3 - b := Nat.eq_sub_of_add_eq hab.symm
      rw [ha, h2_iff_of_le (3 - b) (by linarith)] at hx
      cases le_or_lt 2 b with
      | inl hb => exact .trans (Nat.pow_dvd_pow 2 hb) hy
      | inr hb => exact .trans (Nat.pow_dvd_pow 2 (by linarith)) hx
    have h5 : 5 ^ 3 ∣ (k - 16) * (k + 16) ↔ 5 ^ 3 ∣ k - 16 ∨ 5 ^ 3 ∣ k + 16 := by
      rw [← hk_sub_add]
      rw [h_prime_pow_dvd_mul_add_of_not_dvd _ _ _ Nat.prime_five (by norm_num)]

    calc _
    _ ↔ ∃ n, 1000 * n = k ^ 2 - 16 ^ 2 := by
      refine exists_congr fun n ↦ ?_
      rw [eq_tsub_iff_add_eq_of_le (Nat.pow_le_pow_of_le_left hk 2)]
    _ ↔ 1000 ∣ (k - 16) * (k + 16) := by
      refine exists_congr fun n ↦ ?_
      rw [Nat.sq_sub_sq, eq_comm, mul_comm]
    _ ↔ 2 ^ 3 * 5 ^ 3 ∣ (k - 16) * (k + 16) := Iff.rfl
    _ ↔ 2 ^ 3 ∣ (k - 16) * (k + 16) ∧ 5 ^ 3 ∣ (k - 16) * (k + 16) := by
      rw [h_coprime_mul_dvd_iff (by norm_num)]
    _ ↔ _ := by
      rw [h2, h5, and_or_left]
      refine or_congr ?_ ?_
      · rw [← h2_iff_of_le 2 (by norm_num), and_self]
        calc _
        _ ↔ 2 ^ 2 * 5 ^ 3 ∣ k - 16 := by rw [h_coprime_mul_dvd_iff (by norm_num)]
        _ ↔ 500 ∣ k - 16 := by norm_num
        _ ↔ k ≡ 16 [MOD 500] := by rw [Nat.ModEq.comm, Nat.modEq_iff_dvd' hk]
        _ ↔ _ := Iff.rfl
      · rw [h2_iff_of_le 2 (by norm_num), and_self]
        -- Pass via ℤ to get `500 ∣ k + 16 ↔ 500 ∣ k - 484` and use `Nat.modEq_iff_dvd`.
        calc _
        _ ↔ 2 ^ 2 * 5 ^ 3 ∣ k + 16 := by rw [h_coprime_mul_dvd_iff (by norm_num)]
        _ ↔ 500 ∣ k + 16 := by norm_num
        _ ↔ Nat.cast 500 ∣ (↑(k + 16) : ℤ) := by rw [Int.natCast_dvd, Int.natAbs_ofNat]
        _ ↔ 500 ∣ (k : ℤ) + 16 - 500 := by simp
        _ ↔ 500 ∣ (k : ℤ) - 484 := by
          rw [add_sub_right_comm, sub_add]
          simp only [Int.reduceSub]
        _ ↔ k ≡ 484 [MOD 500] := by
          rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
          simp only [Nat.cast_ofNat]
        _ ↔ _ := Iff.rfl

  -- Use this to provide an alternative definition of `u`.
  have hu' : u = {k | k % 500 = 16 ∨ k % 500 = 484} := by simp_rw [hu, h_iff_mod]

  -- To use `Nat.nth_comp_of_strictMono`, we need to prove that `s` has enough elements.
  -- Use the alternate definition to show `u.Infinite`, then use this to show `s.Infinite`.
  have hu_infinite : u.Infinite := by
    rw [hu']
    refine Set.infinite_iff_exists_gt.mpr fun a ↦ ?_
    refine ⟨500 * (a / 500 + 1) + 16, ?_, ?_⟩
    · exact .inl (Nat.mul_add_mod _ _ _)
    · refine lt_trans ?_ (b := 500 * (a / 500 + 1)) (by norm_num)
      rw [mul_add]
      refine lt_of_eq_of_lt (Nat.div_add_mod a 500).symm ?_
      simp [Nat.mod_lt]
  have hs_infinite : s.Infinite := by
    rw [hsu]
    exact hu_infinite.image hg_mono.injective.injOn
  -- Now we can relate the nth elements of s, u, t.
  have hsu_nth (i) : Nat.nth (· ∈ u) i ^ 2 = Nat.nth (· ∈ s) i := by
    convert Nat.nth_comp_of_strictMono hg_mono ?_ ?_ using 1
    · simp [hsu]
    · simp [hsu]
    · exact fun h ↦ False.elim (hs_infinite h)
  have hst_nth (i) : 1000 * Nat.nth (· ∈ t) i + 256 = Nat.nth (· ∈ s) i := by
    convert Nat.nth_comp_of_strictMono hf_mono ?_ ?_ using 1
    · simp [hst]
    · simp [hst]
    · exact fun h ↦ False.elim (hs_infinite h)

  -- Now the problem can be reduced to finding the 10th element of `u`.
  -- This will be `k = 4 * 500 + 484 = 2484`, corresponding to `n = 6170256` and `m = 6170`.
  suffices Nat.nth (· ∈ t) 9 = 6170 by rw [this]
  suffices 1000 * Nat.nth (· ∈ t) 9 + 256 = 1000 * 6170 + 256 from
    mul_right_injective₀ (by norm_num) (add_left_injective _ this)
  suffices Nat.nth (· ∈ s) 9 = 6170256 by rw [hst_nth, this]
  suffices Nat.nth (· ∈ u) 9 = 2484 by simp [← hsu_nth, this]

  -- Use `Nat.count_injective` to rewrite `Nat.nth` in terms of `Nat.count`.
  -- This requires our alternative definition of `u` as it provides `DecidablePred`.
  simp_rw [hu', Set.mem_setOf_eq]
  suffices Nat.count (fun x ↦ x % 500 = 16 ∨ x % 500 = 484) 2484 = 9 from
    Nat.count_injective (Nat.nth_mem_of_infinite (hu' ▸ hu_infinite) 9) (by norm_num)
      (Eq.trans (Nat.count_nth_of_infinite (hu' ▸ hu_infinite) 9) this.symm)
  -- Rewrite the `or` as membership of a `Finset` to simplify counting.
  suffices Nat.count (· % 500 ∈ ({16, 484} : Finset ℕ)) 2484 = 9 by simpa

  -- The predicate is clearly periodic.
  have h_periodic : Function.Periodic (· % 500 ∈ ({16, 484} : Finset ℕ)) 500 :=
    (Nat.periodic_mod 500).comp _
  -- Use `Nat.filter_Ico_card_eq_of_periodic` to eliminate the 4 whole periods of 500.
  have h_count_add_of_periodic {p : ℕ → Prop} [DecidablePred p]
      {c : ℕ} (hp : p.Periodic c) (n : ℕ) :
      (n + c).count p = n.count p + c.count p := by
    rw [Nat.count_add]
    congr 1
    calc _
    _ = (Finset.filter p (.map (addLeftEmbedding n) (.range c))).card := by
      rw [Nat.count_eq_card_filter_range, Finset.filter_map, Finset.card_map]
      rfl
    _ = (Finset.filter p (.Ico n (n + c))).card := by
      simp only [Finset.range_eq_Ico, Finset.map_add_left_Ico, add_zero]
    _ = c.count p := Nat.filter_Ico_card_eq_of_periodic n c p hp
  -- Since there are only 4 periods, simply expand them all.
  simp only [h_count_add_of_periodic h_periodic (_ + 1)]

  -- Remove the modulo when we can.
  have h_filter_mod_mem_of_le {c : ℕ} (s : Finset ℕ) {n : ℕ} (hn : n ≤ c) :
      Finset.filter (· % c ∈ s) (.range n) = Finset.filter (· ∈ s) (.range n) := by
    refine Finset.filter_congr fun x hx ↦ ?_
    rw [Finset.mem_range] at hx
    rw [Nat.mod_eq_of_lt (by linarith)]
  -- Swap the subset condition and the range condition to make it easier to expand.
  have h_card_filter_range (s : Finset ℕ) (n : ℕ) :
      (Finset.filter (· ∈ s) (.range n)).card = (s.filter (· < n)).card := by
    simp only [← Finset.mem_range, Finset.filter_mem_eq_inter]
    rw [Finset.inter_comm]

  -- Count the number in each period and in the remainder.
  have h_whole : Nat.count (fun x ↦ x % 500 ∈ ({16, 484} : Finset ℕ)) 500 = 2 := by
    rw [Nat.count_eq_card_filter_range]
    rw [h_filter_mod_mem_of_le _ (le_refl 500)]
    rw [h_card_filter_range]
    simp [Finset.filter_insert, Finset.filter_singleton]
  have h_rest : Nat.count (fun x ↦ x % 500 ∈ ({16, 484} : Finset ℕ)) 484 = 1 := by
    rw [Nat.count_eq_card_filter_range]
    rw [h_filter_mod_mem_of_le _ (by norm_num)]
    rw [h_card_filter_range]
    simp [Finset.filter_insert, Finset.filter_singleton]

  simp only [h_whole, h_rest]
