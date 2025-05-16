-- https://cloud.kili-technology.com/label/projects/label/cma3ygp4o00oiahaylpxp9vrm

import Mathlib

/- The sequences $\{a_{n}\}$ and $\{b_{n}\}$ are infinite arithmetic and geometric sequences,
respectively. The sum of the first $n$ terms of $\{a_{n}\}$ is $S_{n} = \frac{3 n^2 + 5 n}{2}$.
In the sequence $\{b_{n}\}$, $b_{3}=4$ and $b_{6}=32$. Let $\{c_{n}\}(n \in \mathbf{N}^{+})$ be
the new sequence formed by all common terms of $\{a_{n}\}$ and $\{b_{n}\}$ (in the original order).
Prove that $\{c_{n}\}$ is a geometric sequence. -/

-- Since `4 ≡ 1 [MOD 3]`, we can determine whether `3 ∣ 2 ^ j - 1` using parity of `j`.
lemma three_dvd_two_pow_sub_one (j : ℕ) : 3 ∣ 2 ^ j - 1 ↔ Even j := by
  rw [← Nat.modEq_iff_dvd' Nat.one_le_two_pow, Nat.ModEq.comm]
  by_cases hj : Even j
  · suffices 2 ^ j ≡ 1 [MOD 3] by simpa [hj] using this
    obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := Even.exists_two_nsmul j hj
    suffices 4 ^ m ≡ 1 [MOD 3] by simpa [pow_mul] using this
    suffices 4 ≡ 1 [MOD 3] by simpa using this.pow m
    rfl
  · suffices ¬2 ^ j ≡ 1 [MOD 3] by simpa [hj]
    rw [Nat.not_even_iff_odd] at hj
    obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := hj
    suffices ¬4 ^ m * 2 ≡ 1 [MOD 3] by simpa [pow_add, pow_mul] using this
    suffices 4 ^ m * 2 ≡ 2 [MOD 3] by
      suffices h12 : ¬1 ≡ 2 [MOD 3] by refine fun h ↦ h12 (h.symm.trans this)
      simp [Nat.modEq_iff_dvd' one_le_two]
    suffices 4 ≡ 1 [MOD 3] by simpa using (this.pow m).mul_right 2
    rfl

-- When `j` is even, we can find `i` such that `4 + 3 i = 2 ^ (j + 2)`.
lemma exists_arith_eq_geom (j : ℕ) (h_even : Even j) :
    ∃ i, 3 * i = 4 * (2 ^ j - 1) := by
  -- Eliminate the tsub before performing induction to simplify manipulation.
  suffices ∃ i, 4 + 3 * i = 4 * 2 ^ j by
    refine this.imp fun i hi ↦ ?_
    convert congrArg (· - 4) hi using 1
    · simp
    · simp [mul_tsub]
  -- Holds trivially for `j = 0`. No need to prove for `j = 1`.
  -- Then use induction to prove for `j = 2 + k` given hy[opothesis for `j = k`.
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => contradiction
  | more j IH _ =>
    obtain ⟨i', hi'⟩ := IH (by simpa using h_even.tsub even_two)
    -- Left side: `4 + 3 * i`
    -- Right side: `4 (2 ^ (j + 2)) = 4 (4 * 2 ^ j) = 4 (4 + 3 i) = 4 + 3 (4 + 4 i)`
    use 4 + 4 * i'
    calc _
    _ = 4 * (4 + 3 * i') := by ring
    _ = _ := by rw [hi', pow_add]; ring

theorem algebra_205122 {a b : ℕ → ℝ}
    (ha : ∃ d, ∀ n, a n = a 0 + d * n) (hb : ∃ q, ∀ n, b n = b 0 * q ^ n)
    (hs : ∀ n, ∑ i in Finset.range n, a i = (3 * n ^ 2 + 5 * n : ℝ) / 2)
    (hb2 : b 2 = 4) (hb5 : b 5 = 32) :
    Set.range (fun n ↦ 4 ^ (n + 1)) = Set.range a ∩ Set.range b := by
  -- First determine the explicit form of `a` and `b`.
  -- For `a`, we don't need the hypothesis that it is an arithmetic sequence;
  -- the definition can be derived from the sum.
  clear ha
  have ha : ∀ n, a n = 4 + 3 * n := by
    intro n
    calc _
    _ = ∑ i ∈ Finset.range (n + 1), a i - ∑ i ∈ Finset.range n, a i := by
      simp [Finset.sum_range_succ]
    _ = _ := by
      simp only [hs, Nat.cast_add]
      ring
  -- For `b`, use the two values to determine the constants.
  replace hb : ∀ n, b n = 2 ^ n := by
    rcases hb with ⟨q, hb⟩
    -- Determine the ratio by dividing the equations for `b 5 / b 2`.
    have hq : q = 2 := by
      suffices q ^ 3 = 2 ^ 3 by
        refine (Odd.strictMono_pow ?_).injective.eq_iff.mp this
        exact odd_two_mul_add_one 1
      symm
      convert congrArg₂ (· / ·) (hb 5) (hb 2)
      · rw [hb2, hb5]
        norm_num
      · symm
        calc _
        _ = b 2 * q ^ 3 / b 2 := by rw [hb 2]; ring
        _ = _ := mul_div_cancel_left₀ _ (by simp [hb2])
    -- Determine the initial by dividing the equations for `b 2` by `q ^ 2 = 4`.
    have hb₀ : b 0 = 1 := by
      convert congrArg (· / 4) hb2
      · rw [hb 2, hq]
        norm_num
      · simp
    -- Use the constants to obtain the explicit form of `b`.
    intro n
    simp [hb n, hq, hb₀]

  -- Now we can proceed to proving the main result.
  -- We need to find the set of `i, j` that satisfy `3 i + 4 = 2 ^ j` to make `c k = a i = b j`.
  -- Note that since `c` is a geometric sequence and a subsequence of `b` (also geometric),
  -- we expect `c` to sample `b` at regular intervals.
  -- We can see that `3 i + 4 = 2 ^ j` is not satisfied for `j = 0, 1` and
  -- is equivalent to `3 i = 4 (2 ^ (j - 2) - 1)` for `2 ≤ j`.
  -- Or equivalently, introduce `j = v + 2` and the condition is `3 i = 4 (2 ^ v - 1)`.
  -- This implies that `3 ∣ 2 ^ v - 1`, which is true iff `Even v`. However, it remains
  -- to show that `Even v` implies the existence of `i` such that `3 i = 4 (2 ^ v - 1)`.
  -- This can be proved by induction using
  -- `4 (2^(v + 2) - 1) = 16 (2 ^ v) - 4 = 4 (4 (2 ^ v - 1) + 3) = 4 (3 i) + 4 * 3`

  -- First switch from `ℝ` to `ℕ`.
  suffices (Set.range fun n ↦ 4 ^ (n + 1)) = Set.range (4 + 3 * ·) ∩ Set.range (2 ^ ·) by
    convert congrArg (fun s ↦ (Nat.cast : ℕ → ℝ) '' s) this
    · ext x
      simp
    · rw [Set.image_inter Nat.cast_injective]
      ext x
      simp [ha, hb]

  ext x
  simp only [Set.mem_range, Set.mem_inter_iff]
  symm
  calc _
  -- Exclude the cases `j = 0, 1` and re-parameterize `j = v + 2`.
  _ ↔ (∃ i, 4 + 3 * i = x) ∧ ∃ v, 4 * 2 ^ v = x := by
    simp only [and_congr_right_iff, forall_exists_index]
    intro i hi
    calc ∃ j, 2 ^ j = x
    -- Introduce the condition that `2 ≤ j`.
    _ ↔ ∃ j, 2 ≤ j ∧ 2 ^ j = x := by
      refine exists_congr fun j ↦ ?_
      simp only [iff_and_self]
      intro hj
      suffices 2 ^ 2 ≤ 2 ^ j from (Nat.pow_le_pow_iff_right one_lt_two).mp this
      rw [hj, ← hi]
      simp
    -- Re-parameterize in terms of `j = v + 2`.
    _ ↔ ∃ j v, j = 2 + v ∧ 2 ^ j = x := by simp [le_iff_exists_add]
    _ ↔ ∃ v, 4 * 2 ^ v = x := by
      rw [exists_comm]
      simp [pow_add]

  -- Replace `∃ i, 4 + 3 * i = 4 * 2 ^ v` with `Even v`.
  _ ↔ ∃ v, (∃ i, 4 + 3 * i = x) ∧ 4 * 2 ^ v = x := by simp
  _ ↔ ∃ v, Even v ∧ 4 * 2 ^ v = x := by
    refine exists_congr fun v ↦ and_congr_left fun hv ↦ ?_
    rcases hv with rfl
    calc _
    _ ↔ (∃ i, 3 * i = 4 * (2 ^ v - 1)) := by
      refine exists_congr fun i ↦ ?_
      rw [mul_tsub, eq_tsub_iff_add_eq_of_le (by simpa using Nat.one_le_two_pow)]
      simp [add_comm]
    _ ↔ Even v := by
      -- Apply the two results from above.
      constructor
      -- Divisibility of `4 * (2 ^ v - 1)` by `3` implies `Even v`.
      · intro ⟨i, hi⟩
        refine (three_dvd_two_pow_sub_one v).mp ?_
        -- Since 3 and 4 are coprime, 3 must divide the other factor.
        suffices 3 ∣ 4 * (2 ^ v - 1) from (Nat.Coprime.dvd_mul_left (by norm_num)).mp this
        exact Dvd.intro i hi
      -- `Even v` implies the existence of `i` such that `3 * i = 4 * (2 ^ v - 1)`.
      · intro hv
        exact exists_arith_eq_geom v hv

  -- Finally, show that `4 ^ (k + 1)` corresponds to `2 ^ (v + 2)` iff `Even v`.
  _ ↔ (∃ v k, v = 2 * k ∧ 2 ^ (2 + v) = x) := by
    simp [even_iff_exists_two_mul, pow_add]
  _ ↔ _ := by
    rw [exists_comm]
    refine exists_congr fun k ↦ ?_
    simp only [exists_eq_left]
    suffices 2 ^ (2 + 2 * k) = 4 ^ (k + 1) by rw [this]
    calc _
    _ = 2 ^ (2 * (1 + k)) := by ring
    _ = _ := by rw [pow_mul]; ring
