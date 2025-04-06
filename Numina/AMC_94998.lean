import Mathlib

/- For $n$ a positive integer, let $R(n)$ be the sum of the remainders when $n$ is divided by
$2$, $3$, $4$, $5$, $6$, $7$, $8$, $9$, and $10$.
For example, $R(15) = 1 + 0 + 3 + 0 + 3 + 1 + 7 + 6 + 5 = 26$.
How many two-digit positive integers $n$ satisfy $R(n) = R(n+1)$?
(A) 0, (B) 1, (C) 2, (D) 3, (E) 4 -/

theorem number_theory_94998 (r : ℕ → ℕ) (hr : ∀ n, r n = ∑ k in .Icc 2 10, n % k) :
    Finset.card {n ∈ .Icc 10 99 | r n = r (n + 1)} = 2 := by
  -- We could obtain this proof directly using `decide`.
  -- However, we prefer to obtain a proof that provides some insight into the problem.

  -- Note that we can add $9$ to $R(n)$ to get $R(n + 1)$, but must subtract $k$ for all $k|n+1$.
  have h_succ (n) : r (n + 1) + ∑ k in .Icc 2 10, (if k ∣ n + 1 then k else 0) = r n + 9 :=
    calc _
    _ = ∑ k ∈ Finset.Icc 2 10, ((n + 1) % k + if k ∣ n + 1 then k else 0) := by
      simp [hr, Finset.sum_add_distrib.symm]
    _ = ∑ k ∈ Finset.Icc 2 10, (n % k + 1) := by
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      -- Rewrite the modulo using division in order to use `Nat.succ_div`, which is
      -- defined in the terms we desire, `if k ∣ n + 1`.
      have hk_mod_succ := (n + 1).mod_add_div k
      rw [Nat.succ_div, mul_add] at hk_mod_succ
      have hk_mod := n.mod_add_div k
      -- Add `k * (n / k)` to both sides to match the form of `Nat.mod_add_div`.
      refine (Nat.add_right_inj (n := k * (n / k))).mp ?_
      -- Add 1 to `hk_mod` to obtain two expressions for `n + 1`.
      convert hk_mod_succ.trans (congrArg (· + 1) hk_mod).symm using 1
      · simp only [mul_ite, mul_one, mul_zero]
        abel
      · abel
    _ = _ := by simp [hr, Finset.sum_add_distrib]

  have h_succ' (n) : r n = r (n + 1) ↔ (∑ k in .Icc 2 10, if k ∣ n + 1 then k else 0) = 9 :=
    calc _
    _ ↔ r (n + 1) + ∑ k in .Icc 2 10, (if k ∣ n + 1 then k else 0) = r (n + 1) + 9 := by
      rw [h_succ, Nat.add_left_inj]
    _ ↔ _ := by
      rw [Nat.add_right_inj]
  simp only [h_succ'] -- TODO: Suffices?

  calc _
  _ = Finset.card {n ∈ .Ico 10 100 | ∑ k ∈ .Icc 2 10, (if k ∣ n + 1 then k else 0) = 9} :=
    rfl  -- TODO: Rephrase earlier to eliminate.
  -- Express in terms of `n + 1` rather than `n`.
  -- TODO: Could happen earlier?
  _ = Finset.card {n ∈ .map (addRightEmbedding 1) (.Ico 10 100) |
      ∑ k ∈ .Icc 2 10, (if k ∣ n then k else 0) = 9} := by
    rw [Finset.filter_map]
    simp [Function.comp_def]
  -- TODO: Merge with above if it doesn't get moved?
  _ = Finset.card {n ∈ .Ioc 10 100 | ∑ k ∈ .Icc 2 10, (if k ∣ n then k else 0) = 9} := by
    simp [Nat.Ico_succ_succ]

  _ = Finset.card {n ∈ .Ioc 10 100 | 2 ∣ n ∧ ¬3 ∣ n ∧ ¬4 ∣ n ∧ ¬5 ∣ n ∧ 7 ∣ n} := by
    congr
    ext n
    -- If `2 ∣ n`, then some subset of [3, 10] must equal 7.
    --   If `3 ∣ n`, then we have `6 ∣ n` and the sum exceeds 7.
    --   If `¬3 ∣ n`, then some subset of {4, 5, 7, 8, 10} must sum to 7.
    --     If `7 ∣ n`, then we require none of the other factors divide `n`.
    --     If `¬7 ∣ n`, then some sum of {4, 5, 8, 10} must equal 7, which is impossible.
    -- If `¬2 ∣ n`, then a subset of {3, 5, 7, 9} must sum to 9.
    --   If `9 ∣ n`, then we have `3 ∣ n` and the sum exceeds 9.
    --   If `¬9 ∣ n`, then some subset of {3, 5, 7} must sum to 9, which is impossible.
    rw [← Finset.sum_filter]
    by_cases h2 : 2 ∣ n
    · -- Extract 2 from the sum.
      suffices ∑ a ∈ .filter (· ∣ n) (.Icc 3 10), a = 7 ↔ ¬3 ∣ n ∧ ¬4 ∣ n ∧ ¬5 ∣ n ∧ 7 ∣ n by
        convert this using 1
        · simp only [Finset.sum_filter]
          rw [Finset.Icc_eq_cons_Ioc (by norm_num), Finset.sum_cons]
          simp [h2, add_comm 2, Nat.Icc_succ_left]
        · simp [h2]
      by_cases h3 : 3 ∣ n
      · -- Extract 3 from the sum. TODO: Combine?
        suffices ∑ a ∈ .filter (· ∣ n) (.Icc 3 10), a ≠ 7 by simpa [h3] using this
        suffices ∑ a ∈ .filter (· ∣ n) (.Icc 4 10), a ≠ 4 by
          rw [Finset.sum_filter] at this ⊢
          rw [Finset.Icc_eq_cons_Ioc (by norm_num), Finset.sum_cons]
          simpa [h3, add_comm 3] using this
        calc _
        -- Extract 6 from the sum.
        _ = ∑ a ∈ insert 6 (.filter (· ∣ n) (.erase (.Icc 4 10) 6)), a := by
          congr 1
          calc _
          _ = .filter (· ∣ n) (insert 6 (.erase (.Icc 4 10) 6)) := by
            rw [Finset.insert_erase]
            norm_num
          _ = _ := by
            rw [Finset.filter_insert]
            have h6 : 6 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl h2 h3
            simp [h6]
        _ ≠ 4 := by simp [add_comm 6]
      · by_cases h7 : 7 ∣ n
        · suffices ∑ a ∈ .filter (fun x ↦ x ∣ n) (.Icc 3 10), a = 7 ↔ ¬3 ∣ n ∧ ¬4 ∣ n ∧ ¬5 ∣ n by
            simpa [h7] using this
          -- Extract 7 from the sum.
          suffices ∑ a ∈ insert 7 (.filter (· ∣ n) (.erase (.Icc 3 10) 7)), a = 7 ↔
              ¬3 ∣ n ∧ ¬4 ∣ n ∧ ¬5 ∣ n by
            convert this using 3
            calc _
            _ = .filter (· ∣ n) (insert 7 (.erase (.Icc 3 10) 7)) := by
              rw [Finset.insert_erase]
              norm_num
            _ = _ := by
              rw [Finset.filter_insert]
              simp [h7]
          suffices ∑ a ∈ .filter (· ∣ n) (.erase (.Icc 3 10) 7), a = 0 ↔
              ¬3 ∣ n ∧ ¬4 ∣ n ∧ ¬5 ∣ n by simpa using this
          change ∑ a ∈ .filter (· ∣ n) (.Icc 3 6 ∪ .Icc 8 10), a = 0 ↔ ¬3 ∣ n ∧ ¬4 ∣ n ∧ ¬5 ∣ n
          rw [Finset.sum_filter]
          rw [Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr rfl)]
          suffices ¬3 ∣ n → ¬4 ∣ n → ¬5 ∣ n → ¬6 ∣ n ∧ ¬8 ∣ n ∧ ¬9 ∣ n ∧ ¬10 ∣ n by
            simpa [Finset.sum_Icc_succ_top (Nat.le_add_left 3 _),
              Finset.sum_Icc_succ_top (Nat.le_add_left 8 _), and_assoc] using this
          intro h3 h4 h5
          refine ⟨?_, ?_, ?_, ?_⟩
          · change ¬2 * 3 ∣ n
            exact mt dvd_of_mul_left_dvd h3
          · change ¬2 * 4 ∣ n
            exact mt dvd_of_mul_left_dvd h4
          · change ¬3 * 3 ∣ n
            exact mt dvd_of_mul_left_dvd h3
          · change ¬2 * 5 ∣ n
            exact mt dvd_of_mul_left_dvd h5
        · suffices ∑ a ∈ .filter (· ∣ n) (.Icc 3 10), a ≠ 7 by simpa [h7] using this
          calc _
          -- Exclude multiples of 3 and 7 from the sum.
          _ = ∑ a ∈ .filter (· ∣ n) (.filter (fun k ↦ ¬3 ∣ k ∧ ¬7 ∣ k) (.Icc 3 10)), a := by
            congr 1
            rw [Finset.filter_filter]
            ext k
            simp only [Finset.mem_filter, and_congr_right_iff, iff_and_self]
            refine fun _ hk ↦ ⟨?_, ?_⟩
            · exact mt (Nat.dvd_trans · hk) h3
            · exact mt (Nat.dvd_trans · hk) h7
          _ = ∑ a ∈ .filter (· ∣ n) {4, 5, 8, 10}, a := rfl
          -- There does not exist a subset of {4, 5, 8, 10} that sums to 7.
          _ ≠ 7 := by
            suffices ∀ s ∈ Finset.powerset {4, 5, 8, 10}, ∑ k ∈ s, k ≠ 7 from this _ (by simp)
            decide

    · suffices ∑ a ∈ .filter (· ∣ n) (.Icc 2 10), a ≠ 9 by simpa [h2] using this
      -- Exclude all k such that `2 ∣ k`.
      suffices ∑ a ∈ .filter (fun k ↦ ¬2 ∣ k ∧ k ∣ n) (.Icc 2 10), a ≠ 9 by
        convert this using 2
        ext k
        simp only [Finset.mem_filter, and_congr_right_iff, iff_and_self]
        exact fun _ hk ↦ mt (fun h2 ↦ h2.trans hk) h2
      -- It now remains to find a subset of {3, 5, 7, 9} whose sum is 9.
      change ∑ a ∈ .filter (fun k ↦ ¬2 ∣ k ∧ k ∣ n) (.Icc 3 9), a ≠ 9
      by_cases h9 : 9 ∣ n
      · -- If `9 ∣ n` then `3 ∣ n` also, and the sum exceeds 9.
        have h3 : 3 ∣ n := .trans (by norm_num) h9
        simp [Finset.sum_filter, Finset.sum_Icc_succ_top (Nat.le_add_left 3 _), h3, h9]
      · -- Eliminate 9 from the sum.
        suffices ∑ a ∈ .filter (fun k ↦ ¬2 ∣ k ∧ k ∣ n) (.Icc 3 7), a ≠ 9 by
          convert this using 2
          ext k
          simp only [Finset.mem_filter, and_congr_left_iff, and_imp]
          intro hk2 hk
          have hk9 : ¬9 ∣ k := mt (fun h9 ↦ h9.trans hk) h9
          simp only [Finset.mem_Icc, and_congr_right_iff]
          intro _
          omega
        rw [← Finset.filter_filter]
        change ∑ a ∈ .filter (fun k ↦ k ∣ n) {3, 5, 7}, a ≠ 9
        -- There does not exist a subset of {3, 5, 7} that sums to 9.
        suffices ∀ s ∈ Finset.powerset {3, 5, 7}, ∑ k ∈ s, k ≠ 9 from this _ (by simp)
        decide

  _ = Finset.card (.image (2 * 7 * ·) {k ∈ .Icc 1 7 | ¬2 ∣ k ∧ ¬3 ∣ k ∧ ¬5 ∣ k}) := by
    refine congrArg Finset.card ?_
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · refine fun ⟨hn, h2, h3, h4, h5, h7⟩ ↦ ?_
      obtain ⟨k, hk⟩ : 2 * 7 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h7
      refine ⟨k, ⟨?_, ?_⟩, hk.symm⟩
      · refine ⟨?_, ?_⟩ <;> linarith
      · refine ⟨?_, ?_, ?_⟩
        · contrapose! h4
          exact hk ▸ Nat.mul_dvd_mul (Nat.dvd_mul_right 2 7) h4
        · contrapose! h3
          exact hk ▸ h3.trans (Nat.dvd_mul_left k _)
        · contrapose! h5
          exact hk ▸ h5.trans (Nat.dvd_mul_left k _)
    · refine fun ⟨k, ⟨hk, ⟨h2, h3, h5⟩⟩, hn⟩ ↦ ⟨?_, ?_⟩
      · rw [← hn]
        refine ⟨?_, ?_⟩ <;> linarith
      · rw [← hn]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · convert Nat.dvd_mul_right 2 (7 * k) using 1
          ring
        · contrapose! h3
          exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3
        · suffices ¬2 ∣ 7 * k by
            contrapose! this
            refine (Nat.mul_dvd_mul_iff_left two_pos).mp ?_
            convert this using 1
            ring
          contrapose! h2
          exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h2
        · contrapose! h5
          exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h5
        · convert Nat.dvd_mul_right 7 (2 * k) using 1
          ring

  --
  _ = Finset.card {k ∈ .Icc 1 7 | ¬2 ∣ k ∧ ¬3 ∣ k ∧ ¬5 ∣ k} := by
    refine Finset.card_image_of_injective _ ?_
    refine mul_right_injective₀ ?_
    norm_num
  --
  _ = Finset.card {1, 7} := by
    refine congrArg Finset.card ?_
    rfl
  _ = 2 := rfl
