-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9z0022ueaxhv05gpa9

import Mathlib

/- Let $\frac{r}{u}$ and $\frac{s}{v}$ be fractions with positive denominators such that
$s u - r v = 1$. It is to be proven:

1) that every fraction whose value lies between $\frac{r}{u}$ and $\frac{s}{v}$ can be written
in the form
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

  have h_gap : (s / v - r / u : ℚ) = 1 / (u * v) := by
    calc _
    _ = (s * u - r * v : ℚ) / (u * v) := by
      rw [div_sub_div _ _ (by simpa) (by simpa)]
      congr 1 <;> ring
    _ = _ := by
      congr
      simpa using congrArg ((↑) : ℤ → ℚ) h

  have h_lt : r / u < (s / v : ℚ) := by
    rw [← sub_pos, h_gap]
    suffices 0 < (1 / ↑(u * v) : ℚ) by simpa
    refine Nat.one_div_cast_pos ?_
    exact Nat.mul_ne_zero hu hv

  -- Convert `uIcc` to `Icc`.
  rw [Set.uIoo_of_lt h_lt]

  constructor
  · intro x hx
    let p := x.num
    let q := x.den
    have hpq : p / q = x := Rat.num_div_den x

    let m : ℤ := p * u - q * r
    have hm_pos : 0 < m := by
      unfold m
      suffices (0 : ℚ) < p * u - q * r by simpa [← @Int.cast_lt ℚ]
      have : 0 < x - r / u := by simpa using hx.1
      rw [← hpq] at this
      rw [div_sub_div _ _ (by simp [q]) (by simpa)] at this
      refine (div_pos_iff_of_pos_right ?_).mp this
      refine mul_pos ?_ ?_
      · simpa using x.den_pos
      · simpa using Nat.pos_of_ne_zero hu

    let l : ℤ := s * q - v * p
    have hl_pos : 0 < l := by
      unfold l
      suffices 0 < (s * q - v * p : ℚ) by simpa [← @Int.cast_lt ℚ]
      -- suffices (0 : ℚ) < p * u - q * r by simpa [← @Int.cast_lt ℚ]
      have : 0 < s / v - x := by simpa using hx.2
      rw [← hpq] at this
      rw [div_sub_div _ _ (by simpa) (by simp [q])] at this
      refine (div_pos_iff_of_pos_right ?_).mp this
      refine mul_pos ?_ ?_
      · simpa using Nat.pos_of_ne_zero hv
      · simpa using x.den_pos

    refine ⟨l.toNat, m.toNat, by simpa, by simpa, ?_⟩

    have h_cast_toNat {x : ℤ} (hx : 0 ≤ x) : (x.toNat : ℚ) = x :=
      congrArg Int.cast (Int.toNat_of_nonneg hx)
    rw [h_cast_toNat hl_pos.le, h_cast_toNat hm_pos.le]

    convert hpq
    · calc _
      _ = ((s * q - v * p) * r + (p * u - q * r) * s : ℚ) := by simp [l, m]
      _ = (p * (s * u - r * v) : ℚ) := by ring
      _ = (p * (s * u - r * v : ℤ) : ℚ) := by simp
      _ = _ := by simp [h]
    · calc _
      _ = ((s * q - v * p) * u + (p * u - q * r) * v : ℚ) := by simp [l, m]
      _ = (q * (s * u - r * v) : ℚ) := by ring
      _ = (q * (s * u - r * v : ℤ) : ℚ) := by simp
      _ = _ := by simp [h]

  · sorry
