-- https://cloud.kili-technology.com/label/projects/label/cma3ygp4o00mrahayitdpqiu1

import Mathlib

open Real

/- Find all natural numbers $a$ and $b$ such that $\sqrt{a} - \sqrt{b}$ is a root
of the equation $x^2 + a x - b = 0$. -/

-- If the square root of a natural number is rational, then the root is an integer.
lemma eq_nat_of_sqrt_eq_rat (n : ℕ) (hq : ∃ q : ℚ, √n = q) : ∃ k : ℕ, √n = k := by
  suffices IsSquare n from this.imp fun k hk ↦ by simp [hk]
  suffices ¬Irrational √n by simpa [irrational_sqrt_natCast_iff]
  rcases hq with ⟨q, hq⟩
  exact hq ▸ q.not_irrational

-- `n` is always coprime to `n + 1`
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
  -- Manipulate to isolate `√b`.
  replace h : √a * (√a * (√a + 1) - √b * (√a + 2)) = 0 := by
    symm
    calc _
    _ = _ := h.symm
    -- Expand the square.
    _ = a + b - 2 * √a * √b + a * (√a - √b) - b := by simp [sub_sq']
    -- Eliminate the `b` term.
    _ = a - 2 * √b * √a + (√a - √b) * a := by ring
    -- Take out a factor of `√a`.
    _ = √a ^ 2 - 2 * √b * √a + (√a - √b) * √a ^ 2 := by simp
    _ = _ := by ring

  rw [mul_eq_zero] at h
  -- Eliminate the case where `a = 0` and we have `√a * (√a + 1) = √b * (√a + 2)`.
  refine h.elim (fun h ↦ .inl (by simpa using h)) fun h ↦ ?_
  rw [sub_eq_zero] at h
  -- Take the square of both sides and expand the squares.
  have h_sq : b * (a + 4 + 4 * √a) = a * (a + 1 + 2 * √a) := by
    symm
    convert congrArg (· ^ 2) h using 1
    · simp [mul_pow, add_sq']
    · simp only [mul_pow, add_sq', Nat.cast_nonneg, sq_sqrt]
      ring

  -- We now have an equation for `b` in terms of `√a`:
  -- `b = a (a + 1 + 2 √a) / (a + 4 + 4 √a)`
  -- Consider `2 b - a` to eliminate the square root from the numerator:
  -- `[2 a (a + 1 + 2 √a) - a (a + 4 + 4 √a)] / (a + 4 + 4 √a)`
  -- `[2 a (a + 1) - a (a + 4)] / (a + 4 + 4 √a)`
  -- This leaves a single `√a` term
  -- `(2 b - a) (a + 4 + 4 √a) = 2 a (a + 1) - a (a + 4)`
  -- `(2 b - a) (a + 4) + 4 (2 b - a) √a = 2 a (a + 1) - a (a + 4)`
  -- from which we deduce that `√a` must be rational.

  -- Rather than convert between division and multiplication,
  -- apply the map `(2 * · - a * (a + 4 + 2 * √a * 2))` to both sides.
  -- Simultaneously gather integer expressions into single coercions.
  have h_sq : ((2 * b - a) * (a + 4) : ℤ) + 4 * ((2 * b - a) * √a) =
      (2 * a * (a + 1) - a * (a + 4) : ℤ) := by
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_add]
    convert congrArg (2 * · - a * (a + 4 + 2 * √a * 2)) h_sq using 1 <;> ring
  -- This shows that `(2 b - a) √a` must be rational.
  have ha_rat : ¬Irrational ((2 * b - a : ℤ) * √a) := by
    suffices ¬Irrational ((4 : ℕ) * ((2 * b - a) * √a)) by
      rw [irrational_nat_mul_iff] at this
      simpa using this
    suffices ¬Irrational (((2 * b - a) * (a + 4) : ℤ) + 4 * ((2 * b - a) * √a)) by
      rw [irrational_int_add_iff] at this
      simpa using this
    rw [h_sq]
    exact Int.not_irrational _

  -- For this product to be rational, either `2 b - a = 0` or `√a` is rational.
  cases eq_or_ne a (2 * b) with
  | inl hab =>
    cases a.eq_zero_or_pos with
    | inl ha => exact .inl ha
    | inr ha =>
      -- Substitute `2 * b` for `a` in the original equation.
      have h : √2 * √b * (√2 * √b + 1) = √b * (√2 * √b + 2) := by simpa [hab] using h
      -- Eliminate the common factor of `√2 √b`.
      have h : √2 * √b + 1 = √b + √2 := by
        -- Multiply by `√2`.
        suffices √2 * (√2 * √b + 1) = √2 * (√b + √2) from (mul_right_inj' (by simp)).mp this
        suffices √2 * (√2 * √b + 1) = √2 * √b + 2 by simpa [mul_add]
        -- Multiply by `√b`.
        suffices √b * (√2 * (√2 * √b + 1)) = √b * (√2 * √b + 2) by
          refine (mul_right_inj' ?_).mp this
          suffices 2 * b ≠ 0 by simpa
          exact hab ▸ ha.ne'
        convert h using 1
        ring
      -- Gather terms to isolate `√b`.
      have h : (√2 - 1) * √b = √2 - 1 := by
        rw [sub_one_mul, sub_eq_sub_iff_add_eq_add]
        convert h using 1
        ring
      refine .inr ?_
      suffices b = 1 by simpa [hab] using this
      simpa [mul_right_eq_self₀, sub_eq_zero] using h

  | inr hab =>
    -- Since `2 b - a` is a non-zero integer, we can deduce that `√a` must be rational.
    have ha_rat : ¬Irrational √a := by
      refine mt (fun h ↦ ?_) ha_rat
      refine irrational_int_mul_iff.mpr ⟨?_, h⟩
      rw [sub_ne_zero]
      suffices (a : ℤ) ≠ ↑(2 * b) by simpa using this.symm
      exact Nat.cast_injective.ne hab
    -- Further, since `√a` is rational, it must be an integer.
    have ha_nat : ∃ u : ℕ, √a = u := by
      refine eq_nat_of_sqrt_eq_rat a ?_
      simpa [Irrational, eq_comm] using ha_rat
    rcases ha_nat with ⟨u, ha_nat⟩

    -- Substitute this integer into our equation for `√b` and gather integer terms.
    -- From this, we observe that `√b` must be rational, and hence also an integer.
    have h : ↑(u * (u + 1)) = √b * ↑(u + 2) := by simpa [ha_nat] using h
    have hb_rat : ¬Irrational √b := by
      suffices ¬Irrational (√b * ↑(u + 2)) by
        rw [irrational_mul_nat_iff] at this
        simpa using this
      rw [← h]
      exact Nat.not_irrational (u * (u + 1))
    have hb_nat : ∃ v : ℕ, √b = v := by
      refine eq_nat_of_sqrt_eq_rat b ?_
      simpa [Irrational, eq_comm] using hb_rat
    rcases hb_nat with ⟨v, hb_nat⟩

    -- We now have an integer equation for `u = √a` and `v = √b`.
    have h : u * (u + 1) = v * (u + 2) := by
      refine (Nat.cast_inj (R := ℝ)).mp ?_
      simpa [hb_nat] using h

    -- If `u = √a = 0`, then we have `0 = 2 v` and hence `a = b = 0`.
    cases u.eq_zero_or_pos with
    | inl hu =>
      refine .inl ?_
      simpa [hu] using ha_nat
    | inr hu =>
      -- We find a contradiction in `u + 2 ∣ u (u + 1)`.
      -- Since `u + 1` and `u + 2` are coprime, we must have `u + 2 ∣ u`.
      -- This is impossible since `u + 2 > u`.
      exfalso
      have h : u + 2 ∣ u * (u + 1) := Dvd.intro_left v h.symm
      have h_coprime : Nat.Coprime (u + 2) (u + 1) := (coprime_add_one (u + 1)).symm
      rw [h_coprime.dvd_mul_right] at h
      simpa using Nat.le_of_dvd hu h
