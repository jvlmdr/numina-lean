-- https://cloud.kili-technology.com/label/projects/label/cma3ygp4o00mrahayitdpqiu1

import Mathlib

open Real

/- Find all natural numbers $a$ and $b$ such that $\sqrt{a} - \sqrt{b}$ is a root
of the equation $x^2 + a x - b = 0$. -/

-- If a rational number's square is an integer, then the rational number must be an integer.
lemma den_eq_one_of_den_sq_eq_one (q : ℚ) (hq : (q ^ 2).den = 1) : q.den = 1 := by
  refine Nat.pow_left_injective two_ne_zero ?_
  simpa using hq

-- A rational number is equal to a natural number iff it is non-negative with denominator 1.
lemma exists_nat_iff (q : ℚ) : 0 ≤ q ∧ q.den = 1 ↔ ∃ n : ℕ, n = q := by
  constructor
  · intro ⟨hq, hq_den⟩
    use q.num.natAbs
    calc _
    _ = ((q.num.natAbs : ℤ) : ℚ) := rfl
    _ = (q.num : ℚ) := by simpa using hq
    _ = _ := q.den_eq_one_iff.mp hq_den
  · intro ⟨n, hq⟩
    simp [← hq]

-- If the square root of a natural number is rational, then the root is an integer.
lemma exists_nat_of_sqrt_eq_rat (n : ℕ) (hq : ∃ q : ℚ, √n = q) : ∃ k : ℕ, √n = k := by
  suffices IsSquare n from this.imp fun k hk ↦ by simp [hk]
  suffices ¬Irrational √n by simpa [irrational_sqrt_natCast_iff]
  rcases hq with ⟨q, hq⟩
  exact hq ▸ q.not_irrational

lemma coprime_add_one (n : ℕ) : n.Coprime (n + 1) := by
  refine Nat.coprime_self_add_right.mpr ?_
  exact Nat.gcd_one_right n

theorem algebra_118182 (a b : ℕ) :
    (√a - √b)^2 + a * (√a - √b) - b = 0 ↔ a = 0 ∨ a = 2 ∧ b = 1 := by
  constructor
  -- It's straightforward to confirm that the equation is satisfied for the given solutions.
  swap
  · refine fun h ↦ h.elim (fun ha ↦ ?_) fun ⟨ha, hb⟩ ↦ ?_
    · simp [ha]
    · simp [ha, hb, sub_sq', mul_sub]

  intro h
  -- We can assume that `0 < a` as the other case is trivial.
  refine a.eq_zero_or_pos.imp id fun ha ↦ ?_

  replace h : √a * (√a * (√a + 1) - √b * (√a + 2)) = 0 := by
    symm
    calc _
    _ = (√a - √b) ^ 2 + a * (√a - √b) - b := h.symm
    _ = a + b - 2 * √a * √b + a * (√a - √b) - b := by simp [sub_sq']
    _ = a - 2 * √b * √a + (√a - √b) * a := by ring
    _ = √a ^ 2 - 2 * √b * √a + (√a - √b) * √a ^ 2 := by simp
    _ = _ := by ring

  rw [mul_eq_zero] at h
  replace h := h.resolve_left (by simpa using ha.ne')
  rw [sub_eq_zero] at h

  -- have h_sq := congrArg (· ^ 2) h
  -- simp [mul_pow, add_sq'] at h_sq

  have h_sq : b * (a + 4 + 2 * √a * 2) = a * (a + 1 + 2 * √a) := by
    symm
    convert congrArg (· ^ 2) h using 1
    · simp [mul_pow, add_sq']
    · simp only [mul_pow, add_sq', sq_sqrt (Nat.cast_nonneg _)]
      ring

  -- Subtract `a * (a + 4 + 2 * √a * 2)` from `2 * b * (a + 4 + 2 * √a * 2)`.
  -- TODO: Clean up this block.
  have : (2 * b - a) * (a + 4) + 4 * (2 * b - a) * √a = 2 * a * (a + 1) - a * (a + 4) := by
    convert congrArg (2 * · - a * (a + 4 + 2 * √a * 2)) h_sq using 1 <;> ring
  have : 4 * (2 * b - a) * √a = 2 * a * (a + 1) - a * (a + 4) - (2 * b - a) * (a + 4) :=
    eq_sub_of_add_eq' this
  have : 4 * (2 * b - a) * √a = 2 * a * (a + 1) - 2 * b * (a + 4) := by
    convert this using 1
    ring
  have : 2 * (2 * b - a) * √a = a * (a + 1) - b * (a + 4) := by
    rw [← mul_right_inj' two_ne_zero]
    convert this using 1 <;> ring
  have : ∃ c : ℤ, √a * (2 * (2 * b - a) : ℤ) = c := by
    use a * (a + 1) - b * (a + 4)
    simpa [mul_comm] using this

  -- Therefore either `√a` is an integer or `2 b = a`.
  rcases this with ⟨c, hc⟩

  -- Either `2 b - a = 0` or `√a` is rational.
  have : 2 * b = a ∨ ¬Irrational √a := by
    refine Or.imp id (fun ha ↦ ?_) (eq_or_ne (2 * b) a)
    refine mt (fun h ↦ ?_) (Int.not_irrational c)
    rw [← hc, irrational_mul_int_iff]
    refine ⟨?_, h⟩
    suffices (↑(2 * b) - a : ℤ) ≠ 0 by simpa using this
    refine sub_ne_zero_of_ne ?_
    exact mt Int.ofNat_inj.mp ha

  have : 2 * b = a := by
    refine this.resolve_right ?_
    intro ha_rat
    have hb_rat : ¬Irrational √b := by sorry

    have ha_nat : ∃ u : ℕ, √a = u := by sorry
    have hb_nat : ∃ v : ℕ, √b = v := by sorry
    rcases ha_nat with ⟨u, ha_nat⟩
    rcases hb_nat with ⟨v, hb_nat⟩
    rw [ha_nat, hb_nat] at h
    have h : u * (u + 1) = v * (u + 2) := (Nat.cast_inj (R := ℝ)).mp (by simpa)

    -- TODO: Might be easier not to assume `0 < a` and keep as `∨` in goal?
    have hu : 0 < u := by
      suffices 0 < u ^ 2 from Nat.pos_of_mul_pos_left this
      convert ha.lt
      symm
      suffices (a : ℝ) = ↑(u ^ 2) from Nat.cast_inj.mp this
      have := congrArg (· ^ 2) ha_nat
      simpa using this

    have h_coprime := coprime_add_one (u + 1)
    have h_dvd : u + 2 ∣ u * (u + 1) := Dvd.intro_left v h.symm
    have h_dvd : u + 2 ∣ u := h_coprime.symm.dvd_mul_right.mp h_dvd
    -- This provides a contradiction: `u + 2 ≤ u`
    simpa using Nat.le_of_dvd hu h_dvd

  simp [← this] at h
  simp [← this] at h_sq
  sorry
