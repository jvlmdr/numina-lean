-- https://cloud.kili-technology.com/label/projects/label/cm7eni8oq0073zz87ldlz1jwe
-- https://artofproblemsolving.com/wiki/index.php/2017_AIME_I_Problems/Problem_5

import Mathlib

/- A rational number written in base eight is ab.cd, where all digits are nonzero.
The same number in base twelve is bb.ba.
Find the base-ten number abc. -/
theorem number_theory_97068 {a b c d : ℕ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (ha_lt : a < 8) (hb_lt : b < 8) (hc_lt : c < 8) (hd_lt : d < 8)
    (h : (a * 8 + b + c / 8 + d / 8^2 : ℝ) = b * 12 + b + b / 12 + a / 12^2) :
    a * 100 + b * 10 + c = 321 := by
  suffices a = 3 ∧ b = 2 ∧ c = 1 by simp [this]

  -- Separate the whole and fractional parts of the numbers.
  have h : ((c + d / 8) / 8 : ℝ) + ↑(a * 8 + b) = ((b + a / 12) / 12) + ↑(b * 12 + b) := by
    simp only [Nat.cast_add, Nat.cast_mul]
    refine (Eq.congr ?_ ?_).mpr h <;> ring
  -- Obtain equation for a and b from the whole parts.
  -- First establish that the fractional parts are in [0, 1).
  have h_lhs_fract : ((c + d / 8) / 8 : ℝ) ∈ Set.Ico 0 1 := by
    refine ⟨?_, ?_⟩
    · refine div_nonneg (add_nonneg ?_ (div_nonneg ?_ ?_)) ?_ <;> simp
    · rw [div_lt_one (by norm_num)]
      calc _
      _ < (7 + 1 : ℝ) := by
        refine add_lt_add_of_le_of_lt ?_ ?_
        · simpa using Nat.le_of_lt_succ hc_lt
        · rw [div_lt_one (by norm_num)]
          simpa using hd_lt
      _ = 8 := by norm_num
  have h_rhs_fract : ((b + a / 12) / 12 : ℝ) ∈ Set.Ico 0 1 := by
    refine ⟨?_, ?_⟩
    · refine div_nonneg (add_nonneg ?_ (div_nonneg ?_ ?_)) ?_ <;> simp
    · refine (div_lt_one (by norm_num)).mpr ?_
      calc _
      _ < (11 + 1 : ℝ) := by
        refine add_lt_add_of_le_of_lt ?_ ?_
        · simpa using le_trans hb_lt.le (by norm_num)
        · rw [div_lt_one (by norm_num)]
          simpa using lt_trans ha_lt (by norm_num)
      _ = 12 := by norm_num
  -- Now isolate the whole parts.
  have hab : a * 8 = b * 12 := by
    have h := congrArg (⌊·⌋₊) h
    simp only [Nat.floor_add_nat h_lhs_fract.1, Nat.floor_add_nat h_rhs_fract.1] at h
    simpa [Nat.floor_eq_zero.mpr h_lhs_fract.2, Nat.floor_eq_zero.mpr h_rhs_fract.2] using h
  -- Eliminate common factors.
  replace hab : a * 2 = b * 3 := by
    rw [← Nat.mul_left_inj (a := 4) (by norm_num)]
    refine (Eq.congr ?_ ?_).mpr hab <;> ring
  -- Isolate the fractional parts.
  have hcd : (c / 8 + d / 8^2 : ℝ) = b / 12 + a / 12^2 := by
    have h := congrArg Int.fract h
    simp only [Int.fract_add_nat] at h
    rw [Int.fract_eq_self.mpr h_lhs_fract, Int.fract_eq_self.mpr h_rhs_fract] at h
    refine (Eq.congr ?_ ?_).mpr h <;> ring
  -- Eliminate common factors.
  replace hcd : (d + c * 8) * 9 = (a + b * 12) * 4 := by
    refine Nat.cast_injective (R := ℝ) ?_
    simp only [Nat.cast_mul, Nat.cast_add]
    rw [← div_left_inj' (c := 3^2 * 2^2 * 4^2)]
    refine (Eq.congr ?_ ?_).mpr hcd <;> ring
    norm_num

  -- Consider all constraints on b.
  -- From `3 b = 2 a` and `a < 8` we obtain `b < 5` and `2 ∣ b`.
  replace hb_lt : b < 5 := by
    refine Nat.lt_add_one_of_le ?_
    have : a * 2 ≤ 7 * 2 := Nat.mul_le_mul_right 2 (Nat.le_of_lt_succ ha_lt)
    rw [hab] at this
    rw [← Nat.le_div_iff_mul_le (by norm_num)] at this
    exact le_trans this (by norm_num)
  have hb_dvd : 2 ∣ b := by
    refine Nat.Coprime.dvd_of_dvd_mul_right (by norm_num : Nat.Coprime 2 3) ?_
    simp only [← hab, dvd_mul_left]

  -- Putting this together, we have two possible values.
  have hb_mem : b = 2 ∨ b = 4 := by
    suffices b ∈ ({2, 4} : Finset ℕ) from List.mem_pair.mp this
    suffices {2, 4} = (Finset.range 5).filter (fun b ↦ b ≠ 0 ∧ 2 ∣ b) by
      rw [this, Finset.mem_filter, Finset.mem_range]
      exact ⟨hb_lt, hb0, hb_dvd⟩
    rfl

  -- The value of a is determined by b.
  have ha : a = b * 3 / 2 := (Nat.div_eq_of_eq_mul_left (by norm_num) hab.symm).symm
  have hab : (a = 3 ∧ b = 2) ∨ (a = 6 ∧ b = 4) := by
    refine hb_mem.imp (fun hb ↦ ⟨?_, hb⟩) (fun hb ↦ ⟨?_, hb⟩) <;> simp [ha, hb]

  -- Obtain (c, d) for each candidate and show that one case is invalid.
  have hcd : d + c * 8 = (a + b * 12) * 4 / 9 :=
    (Nat.div_eq_of_eq_mul_left (by norm_num) hcd.symm).symm
  cases hab with
  | inl hab =>
    -- Put in the form required by `Nat.div_mod_unique`.
    replace hcd : d + 8 * c = 12 := by rw [mul_comm, hcd, hab.1, hab.2]
    replace hcd := (Nat.div_mod_unique (by norm_num)).mpr ⟨hcd, hd_lt⟩
    rw [← hcd.1]
    exact ⟨hab.1, hab.2, by norm_num⟩
  | inr hab =>
    exfalso
    -- Put in the form required by `Nat.div_mod_unique`.
    replace hcd : d + 8 * c = 24 := by rw [mul_comm, hcd, hab.1, hab.2]
    replace hcd := (Nat.div_mod_unique (by norm_num)).mpr ⟨hcd, hd_lt⟩
    exfalso
    refine hd0 ?_
    rw [← hcd.2]
