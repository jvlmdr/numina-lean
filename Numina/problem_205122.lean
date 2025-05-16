-- https://cloud.kili-technology.com/label/projects/label/cma3ygp4o00oiahaylpxp9vrm

import Mathlib

/- The sequences $\{a_{n}\}$ and $\{b_{n}\}$ are infinite arithmetic and geometric sequences,
respectively. The sum of the first $n$ terms of $\{a_{n}\}$ is $S_{n} = \frac{3 n^2 + 5 n}{2}$.
In the sequence $\{b_{n}\}$, $b_{3}=4$ and $b_{6}=32$. Let $\{c_{n}\}(n \in \mathbf{N}^{+})$ be
the new sequence formed by all common terms of $\{a_{n}\}$ and $\{b_{n}\}$ (in the original order).
Prove that $\{c_{n}\}$ is a geometric sequence. -/

lemma exists_arith_eq_geom (j : ℕ) (h_even : Even j) (h_zero : j ≠ 0) :
    ∃ i, 4 + 3 * i = 2 ^ j := by
  cases j with
  | zero => contradiction
  | succ j =>
    -- TODO: Is there a way to avoid `j + 1` everywhere?
    induction j using Nat.twoStepInduction with
    | zero => contradiction
    | one => simp
    | more j IH _ =>
      obtain ⟨i', hi'⟩ := IH (by simpa using h_even.tsub even_two) (by simp)
      -- One the right side, we have `2 ^ (j.succ + 2) = 2 * 4 * 2 ^ j.succ = 4 * (4 + 3 * i')`.
      -- Therefore it will suffice to find some `i` that satsfies `4 + 3 * i = 4 * (4 + 3 * i')`.
      use 4 + 4 * i'
      calc _
      _ = 4 * (4 + 3 * i') := by ring
      _ = 4 * 2 ^ (j + 1) := by rw [hi']
      _ = _ := by ring

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

theorem algebra_205122 {a b : ℕ → ℝ}
    (ha : ∃ d, ∀ n, a n = a 0 + d * n) (hb : ∃ q, ∀ n, b n = b 0 * q ^ n)
    (hs : ∀ n, ∑ i in Finset.range n, a i = (3 * n ^ 2 + 5 * n : ℝ) / 2)
    (hb2 : b 2 = 4) (hb5 : b 5 = 32) :
    Set.range (fun n ↦ 4 ^ (n + 1)) = Set.range a ∩ Set.range b := by

  -- We actually don't need the hypothesis that `a` is an arithmetic sequence.
  -- It can be derived from the sum.
  clear ha
  have ha : ∀ n, a n = 4 + 3 * n := by
    intro n
    calc _
    _ = ∑ i ∈ Finset.range (n + 1), a i - ∑ i ∈ Finset.range n, a i := by
      simp [Finset.sum_range_succ]
    _ = _ := by
      simp only [hs, Nat.cast_add]
      ring

  have hb : ∀ n, b n = 2 ^ n := by
    rcases hb with ⟨q, hb⟩
    have hb_zero : b 0 ≠ 0 ∧ q ≠ 0 := by
      suffices b 0 * q ^ 2 ≠ 0 by simpa using this
      calc _
      _ = b 2 := (hb 2).symm
      _ = 4 := hb2
      _ ≠ 0 := by norm_num

    have hq : q = 2 := by
      suffices q ^ 3 = 2 ^ 3 by
        refine (Odd.strictMono_pow ?_).injective.eq_iff.mp this
        exact odd_two_mul_add_one 1
      calc _
      _ = q ^ (5 - 2) := by norm_num
      _ = q ^ 5 * (q ^ 2)⁻¹ := pow_sub₀ q hb_zero.2 (by norm_num)
      _ = q ^ 5 / q ^ 2 := by ring
      _ = b 5 / b 2 := by
        rw [hb 5, hb 2]
        symm
        refine mul_div_mul_left _ _ hb_zero.1
      _ = _ := by
        rw [hb2, hb5]
        norm_num

    have hb₀ : b 0 = 1 := by
      convert congrArg (· / 4) hb2
      · rw [hb 2, hq]
        norm_num
      · simp

    intro n
    rw [hb]
    simp [hq, hb₀]

  -- Note that since `c` is a geometric sequence and a subsequence of `b` (also geometric),
  -- we expect `c` to sample `b` at regular intervals.
  -- `3 i + 4 = 2 ^ j`
  -- `3 (i + 1) = 2 ^ j - 1`
  -- `3 ∣ 2 ^ j - 1`
  -- This ocurrs `j = 1` and all even `j`.
  -- This can be shown by induction: `2^2 - 1 = 3` and `2^(j + 2) - 1 = 4 * (2^j - 1) + 3`.

  ext x
  simp only [one_mul, Set.mem_range, Set.mem_inter_iff, ha, hb]

  calc _
  _ ↔ ∃ k, 2 ^ (2 * (k + 1)) = x := by
    simp only [pow_mul]
    norm_num
  _ ↔ ∃ j, (j ≠ 0 ∧ Even j) ∧ 2 ^ j = x := by
    constructor
    · intro ⟨k, hk⟩
      use 2 * (k + 1)
      exact ⟨by simp, hk⟩
    · intro ⟨j, ⟨hj_zero, hj_even⟩, hj⟩
      rcases hj_even.two_dvd with ⟨u, rfl⟩
      use u - 1
      convert hj
      refine Nat.succ_pred_eq_of_ne_zero ?_
      simpa using hj_zero

  _ ↔ ∃ j, (∃ i : ℕ, 4 + 3 * i = x) ∧ 2 ^ j = x := by
    refine exists_congr fun j ↦ and_congr_left fun hj ↦ ?_
    rcases hj with rfl
    constructor
    · intro ⟨hj_zero, hj_even⟩
      have := exists_arith_eq_geom j hj_even hj_zero
      refine this.imp fun i hi ↦ ?_
      simpa using congrArg (fun x ↦ x : ℕ → ℝ) hi
    · intro ⟨i, hi⟩
      -- TODO: ugly to encounter Real vs Nat here?
      replace hi : 4 + 3 * i = 2 ^ j := by
        refine (Nat.cast_inj (R := ℝ)).mp ?_
        simpa using hi
      refine ⟨?_, ?_⟩
      · contrapose! hi with hj
        rcases hj with rfl
        suffices 4 + 3 * i ≠ 2 ^ 0 by simpa using this
        linarith
      · cases j with
        | zero => exact even_zero
        | succ j =>
          cases j with
          | zero =>
            contrapose! hi with hj
            suffices 4 + 3 * i ≠ 2 by simpa using this
            linarith
          | succ j =>
            suffices Even j by simpa [Nat.add_assoc] using this.add even_two
            suffices 3 ∣ 2 ^ j - 1 from (three_dvd_two_pow_sub_one j).mp this
            have hi : 3 * i = 4 * (2 ^ j - 1) := by
              rw [mul_tsub]
              refine eq_tsub_of_add_eq ?_
              convert hi using 1 <;> ring
            suffices 3 ∣ 4 * (2 ^ j - 1) from (Nat.Coprime.dvd_mul_left (by norm_num)).mp this
            exact Dvd.intro i hi

  _ ↔ _ := by simp
