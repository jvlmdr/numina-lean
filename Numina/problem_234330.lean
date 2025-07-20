-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9z0022ueaxhv05gpa9

import Mathlib

/- Let $\frac{r}{u}$ and $\frac{s}{v}$ be fractions with positive denominators such that
$s u - r v = 1$. It is to be proven:

1) that every fraction whose value lies between $\frac{r}{u}$ and $\frac{s}{v}$
can be written in the form
$$
\frac{l r + m s}{l u + m v}
$$
where $l$ and $m$ are positive integers, and

2) that conversely, the values of fractions of the said form lie between
$\frac{r}{u}$ and $\frac{s}{v}$. -/

theorem number_theory_234330 (r s : ℤ) (u v : ℕ) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : s * u - r * v = 1) :
    (∀ x : ℚ, x ∈ (.uIoo (r / u) (s / v) : Set ℚ) →
      ∃ l m : ℕ, l ≠ 0 ∧ m ≠ 0 ∧ (l * r + m * s) / (l * u + m * v) = x) ∧
    ∀ l m : ℕ, l ≠ 0 → m ≠ 0 →
      ((l * r + m * s) / (l * u + m * v) : ℚ) ∈ (.uIoo (r / u) (s / v) : Set ℚ) := by
  -- First, observe that `s / v = r / u + 1 / (u * v)` and hence `s / v < r / u`.
  have h_sub : (s / v - r / u : ℚ) = 1 / (u * v) := by
    calc _
    _ = (s * u - r * v : ℚ) / (u * v) := by
      rw [div_sub_div _ _ (by simpa) (by simpa)]
      congr 1 <;> ring
    _ = _ := by
      congr
      simpa using congrArg ((↑) : ℤ → ℚ) h

  -- Use this to rewrite `uIcc` as `Icc`.
  have h_lt : r / u < (s / v : ℚ) := by
    rw [← sub_pos, h_sub]
    suffices 0 < (u * v : ℚ)⁻¹ by simpa
    rw [inv_pos]
    refine mul_pos ?_ ?_ <;> simpa [Nat.pos_iff_ne_zero]
  rw [Set.uIoo_of_lt h_lt]

  constructor
  · -- Let `x = p / q` with `r / u < p / q < s / v`.
    intro x hx_mem
    let p := x.num
    let q := x.den
    have hq : q ≠ 0 := x.den_nz
    have hx : p / q = x := Rat.num_div_den x

    -- If we set `m = p * u - q * r` and `l = s * q - v * p`,
    -- then we can show that `l * r + m * s = p` and `l * u + m * v = q`.

    -- From `0 < p / q - r / u`, we see `0 < p * u - r * q = m`.
    let m : ℤ := p * u - q * r
    have hm_pos : 0 < m := by
      have : 0 < (p / q - r / u : ℚ) := by simpa [hx] using hx_mem.1
      rw [div_sub_div _ _ (by simpa) (by simpa)] at this
      have : 0 < (p * u - q * r : ℤ) / (q * u : ℚ) := by simpa
      rw [← @Int.cast_lt ℚ]
      refine (div_pos_iff_of_pos_right ?_).mp this
      refine mul_pos ?_ ?_ <;> simpa [Nat.pos_iff_ne_zero]
    -- Likewise, from `0 < s / v - p / q`, we see `0 < s * q - v * p = l`.
    let l : ℤ := s * q - v * p
    have hl_pos : 0 < l := by
      have : 0 < (s / v - p / q : ℚ) := by simpa [hx] using hx_mem.2
      rw [div_sub_div _ _ (by simpa) (by simpa)] at this
      have : 0 < (s * q - v * p : ℤ) / (v * q : ℚ) := by simpa
      rw [← @Int.cast_lt ℚ]
      refine (div_pos_iff_of_pos_right ?_).mp this
      refine mul_pos ?_ ?_ <;> simpa [Nat.pos_iff_ne_zero]

    refine ⟨l.toNat, m.toNat, by simpa, by simpa, ?_⟩

    -- Replace `(x.toNat : ℚ)` with `(x : ℚ)` where `x` is positive.
    have h_cast_toNat {x : ℤ} (hx : 0 ≤ x) : (x.toNat : ℚ) = x :=
      congrArg Int.cast (Int.toNat_of_nonneg hx)
    rw [h_cast_toNat hl_pos.le, h_cast_toNat hm_pos.le]

    convert hx
    · suffices l * r + m * s = p by simpa [← @Int.cast_inj ℚ]
      calc _
      _ = p * (s * u - r * v) := by ring
      _ = _ := by simp [h]
    · suffices l * u + m * v = q by simpa [← @Int.cast_inj ℚ]
      calc _
      _ = q * (s * u - r * v) := by ring
      _ = _ := by simp [h]

  · intro l m hl hm
    rw [Set.mem_Ioo]
    -- Before cross-multiplying the fractions, establish that the denominator is positive.
    have h_den : 0 < (l * u + m * v : ℚ) := by
      refine add_pos ?_ ?_
      · refine mul_pos ?_ ?_ <;> simpa [Nat.pos_iff_ne_zero]
      · refine mul_pos ?_ ?_ <;> simpa [Nat.pos_iff_ne_zero]
    split_ands
    · -- Cross-multiply and eliminate the common terms from both sides.
      refine (div_lt_div_iff₀ (by simpa [Nat.pos_iff_ne_zero]) h_den).mpr ?_
      suffices r * u * l + r * v * m < (r * u * l + s * u * m : ℚ) by convert this using 1 <;> ring
      suffices r * v * m < (s * u * m : ℚ) by simpa
      -- Eliminate the constant positive factor.
      refine mul_lt_mul_of_pos_right ?_ (by simpa [Nat.pos_iff_ne_zero])
      refine (div_lt_div_iff₀ ?_ ?_).mp h_lt <;> simpa [Nat.pos_iff_ne_zero]
    · -- Cross-multiply and eliminate the common terms from both sides.
      refine (div_lt_div_iff₀ h_den (by simpa [Nat.pos_iff_ne_zero])).mpr ?_
      suffices r * v * l + s * v * m < (s * u * l + s * v * m : ℚ) by convert this using 1 <;> ring
      suffices r * v * l < (s * u * l : ℚ) by simpa
      -- Eliminate the constant positive factor.
      refine mul_lt_mul_of_pos_right ?_ (by simpa [Nat.pos_iff_ne_zero])
      refine (div_lt_div_iff₀ ?_ ?_).mp h_lt <;> simpa [Nat.pos_iff_ne_zero]
