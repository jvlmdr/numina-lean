-- https://cloud.kili-technology.com/label/projects/label/cma3ygf29005uahay4l8rup6c

import Mathlib

open Real

/- Let $f(x)$ and $g(x)$ be odd and even functions defined on $R$, respectively, and
$f(x) + g(x) = 2^x$. If for $x \in [1, 2]$, the inequality $a f(x) + g(2x) \geq 0$ always holds,
then the range of the real number $a$ is? -/

theorem algebra_145653 (f g : ℝ → ℝ) (hf : f.Odd) (hg : g.Even)
    (hfg : ∀ x, f x + g x = 2 ^ x) (a : ℝ) :
    (∀ x ∈ Set.Icc 1 2, 0 ≤ a * f x + g (2 * x)) ↔ -17 / 6 ≤ a := by

  have hfg' (x) : -f x + g x = 2 ^ (-x) := by simpa [hf x, hg x] using hfg (-x)
  have hg (x) : 2 * g x = 2 ^ x + 2 ^ (-x) := by
    convert congrArg₂ (· + ·) (hfg x) (hfg' x) using 1
    ring
  have hf (x) : 2 * f x = 2 ^ x - 2 ^ (-x) := by
    convert congrArg₂ (· - ·) (hfg x) (hfg' x) using 1
    ring

  calc _
  _ ↔ ∀ x : ℝ, x ∈ Set.Icc 1 2 → 0 ≤ 2 * (a * f x + g (2 * x)) := by simp

  _ ↔ ∀ x : ℝ, x ∈ Set.Icc 1 2 → 0 ≤ a * (2 ^ x - 2 ^ (-x)) + ((2 ^ x - 2 ^ (-x)) ^ 2 + 2) := by
    suffices ∀ x, 2 * (a * f x + g (2 * x)) =
        a * (2 ^ x - 2 ^ (-x)) + ((2 ^ x - 2 ^ (-x)) ^ 2 + 2) by
      simp only [this]
    intro x
    calc _
    _ = a * (2 * f x) + 2 * g (2 * x) := by ring
    _ = a * (2 ^ x - 2 ^ (-x)) + (2 ^ (x * 2) + 2 ^ (-x * 2)) := by
      rw [hf, hg]
      congr 3 <;> ring
    _ = a * (2 ^ x - 2 ^ (-x)) + ((2 ^ x) ^ 2 + (2 ^ (-x)) ^ 2) := by simp [rpow_mul, -neg_mul]
    _ = a * (2 ^ x - 2 ^ (-x)) + ((2 ^ x - 2 ^ (-x)) ^ 2 + 2) := by
      congr 1
      rw [sub_sq', ← sub_add_comm]
      refine self_eq_add_left.mpr ?_
      rw [mul_assoc, ← rpow_add two_pos]
      simp

  _ ↔ ∀ x : ℝ, x ∈ Set.Icc 1 2 → -(2 ^ x - 2 ^ (-x) + 2 / (2 ^ x - 2 ^ (-x))) ≤ a := by
    refine forall₂_congr fun x hx ↦ ?_
    rw [Set.mem_Icc] at hx
    calc _
    _ ↔ -((2 ^ x - 2 ^ (-x)) ^ 2 + 2) ≤ a * (2 ^ x - 2 ^ (-x)) := neg_le_iff_add_nonneg.symm
    _ ↔ -((2 ^ x - 2 ^ (-x)) ^ 2 + 2) / (2 ^ x - 2 ^ (-x)) ≤ a := by
      refine (div_le_iff₀ ?_).symm
      suffices 0 < x by simpa using this
      linarith
    _ ↔ _ := by rw [neg_div, add_div, sq, mul_self_div_self]

  _ ↔ ∀ t ∈ (fun x : ℝ ↦ 2 ^ x - 2 ^ (-x)) '' Set.Icc 1 2, -(t + 2 / t) ≤ a := by
    simp only [Set.forall_mem_image]

  _ ↔ ∀ t ∈ Set.Icc (3 / 2 : ℝ) (15 / 4), -(t + 2 / t) ≤ a := by
    suffices (fun x : ℝ ↦ 2 ^ x - 2 ^ (-x)) '' Set.Icc 1 2 = Set.Icc (3 / 2 : ℝ) (15 / 4) by
      rw [this]

    have h_cont : ContinuousOn (fun x ↦ 2 ^ x - 2 ^ (-x) : ℝ → ℝ) (Set.Icc 1 2) := by
      refine ContinuousOn.sub ?_ ?_
      · exact .rpow continuousOn_const (continuousOn_id' _) (by simp)
      · exact .rpow continuousOn_const continuousOn_neg (by simp)
    have h_mono : StrictMono (fun x ↦ 2 ^ x - 2 ^ (-x) : ℝ → ℝ) := by
      refine .add ?_ ?_
      · exact fun x y hxy ↦ by simpa using hxy
      · exact fun x y hxy ↦ by simpa using hxy
    rw [h_cont.image_Icc one_le_two]
    refine congrArg₂ _ ?_ ?_
    · rw [← MonotoneOn.map_csInf_of_continuousWithinAt (h_cont.continuousWithinAt <| by simp)
        (h_mono.monotone.monotoneOn _) (by simp) bddBelow_Icc]
      rw [csInf_Icc one_le_two]
      norm_num
    · rw [← MonotoneOn.map_csSup_of_continuousWithinAt (h_cont.continuousWithinAt <| by simp)
        (h_mono.monotone.monotoneOn _) (by simp) bddAbove_Icc]
      rw [csSup_Icc one_le_two]
      norm_num

  _ ↔ -17 / 6 ≤ a := by

    have h_cont : ContinuousOn (fun t : ℝ ↦ t + 2 / t) (Set.Ioi 0) := by
      refine .add (continuousOn_id' _) ?_
      -- refine .mono ?_ (Set.Ioi_subset_Ioi (sqrt_nonneg 2))
      exact .div₀ continuousOn_const (continuousOn_id' _) fun x hx ↦ ne_of_gt hx

    -- The derivative of `-(t + 2 / t)` is `-1 + 2 / t ^ 2`; negative for `2 < t ^ 2`.
    have h_anti : StrictAntiOn (fun t : ℝ ↦ -(t + 2 / t)) (Set.Ioi √2) := by
      refine StrictMonoOn.neg ?_
      refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioi _) ?_ ?_ ?_
        (f' := fun t ↦ 1 - 2 / t ^ 2)
      · exact h_cont.mono (Set.Ioi_subset_Ioi (sqrt_nonneg 2))
      · simp only [interior_Ioi, Set.mem_Ioi]
        intro x hx
        refine .add (hasDerivWithinAt_id _ _) ?_
        convert (hasDerivWithinAt_inv (?_ : x ≠ 0) (Set.Ioi √2)).const_mul 2 using 1
        · ring
        · exact ne_of_gt <| lt_of_le_of_lt (sqrt_nonneg 2) hx
      · simp only [interior_Ioi, Set.mem_Ioi, sub_pos]
        intro x hx
        replace hx := lt_sq_of_sqrt_lt hx
        exact (div_lt_one (two_pos.trans hx)).mpr hx

    calc _
    _ ↔ sSup ((fun t ↦ -(t + 2 / t)) '' Set.Icc (3 / 2) (15 / 4)) ≤ a := by
      have := csSup_le_iff (α := ℝ) (s := (fun t : ℝ ↦ -(t + 2 / t)) '' Set.Icc (3 / 2) (15 / 4))
        (isCompact_Icc.bddAbove_image sorry) (by simp; norm_num) (a := a)

      rw [this]
      rw [Set.forall_mem_image]

    _ ↔ _ := by
      suffices sSup ((fun t : ℝ ↦ -(t + 2 / t)) '' Set.Icc (3 / 2) (15 / 4)) = -17 / 6 by
        rw [this]
      calc _
      _ = (fun t : ℝ ↦ -(t + 2 / t)) (sInf (Set.Icc (3 / 2) (15 / 4))) := by
        symm
        refine AntitoneOn.map_csInf_of_continuousWithinAt (f := fun t ↦ -(t + 2 / t))
          ?_ ?_ ?_ bddBelow_Icc
        · refine ContinuousOn.continuousWithinAt ?_ ?_
          · refine h_cont.neg.mono fun x hx ↦ ?_
            suffices 0 < (3 / 2 : ℝ) by simpa using this.trans_le hx.1
            norm_num
          · suffices (3 / 2 : ℝ) ≤ 15 / 4 by simp [this]
            norm_num
        · refine h_anti.antitoneOn.mono fun x ↦ ?_
          simp
          sorry  -- easy
        · suffices (3 / 2 : ℝ) ≤ 15 / 4 by simpa using this
          norm_num
      _ = (fun t : ℝ ↦ -(t + 2 / t)) (3 / 2) := by rw [csInf_Icc (by norm_num)]
      _ = _ := by norm_num
