-- https://cloud.kili-technology.com/label/projects/label/cm96qkyi3000y4nayo17ayt0j

import Mathlib

/- Given
$$ a + b + c = 5, $$
$$ a^{2} + b^{2} + c^{2} = 15, $$
$$ a^{3} + b^{3} + c^{3} = 47. $$
Find the value $(a^{2} + a b + b^{2}) (b^{2} + b c + c^{2}) (c^{2} + c a + a^{2})$. -/

theorem algebra_178166 {a b c : ℝ} (h₁ : a + b + c = 5) (h₂ : a^2 + b^2 + c^2 = 15)
    (h₃ : a^3 + b^3 + c^3 = 47) :
    (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) = 625 := by
  -- Obtain `ab + bc + ca` from `a + b + c` and `a^2 + b^2 + c^2`.
  -- Write in symmetric form.
  have h_ab_bc_ca {a b c : ℝ} (h₁ : a + b + c = 5) (h₂ : a^2 + b^2 + c^2 = 15) :
      a * b + b * c + c * a = 5 := by
    suffices 2 * (a * b + b * c + c * a) = 2 * 5 from (mul_right_inj' two_ne_zero).mp this
    calc _
    _ = (a + b + c)^2 - (a^2 + b^2 + c^2) := by ring
    _ = 5^2 - 15 := by rw [h₁, h₂]
    _ = _ := by norm_num

  calc _
  _ = (5 * (4 - c)) * (5 * (4 - a)) * (5 * (4 - b)) := by
    -- Obtain `a^2 + ab + b^2` from `a + b + c` and `a^2 + b^2 + c^2`.
    -- Write in symmetric form.
    suffices ∀ {a b c : ℝ}, a + b + c = 5 → a^2 + b^2 + c^2 = 15 →
        a^2 + a * b + b^2 = 5 * (4 - c) by
      congr
      · exact this h₁ h₂
      · rw [add_rotate] at h₁ h₂
        exact this h₁ h₂
      · rw [add_rotate, add_rotate] at h₁ h₂
        exact this h₁ h₂
    intro a b c h₁ h₂
    calc _
    _ = (a + b) * (a + b + c) - (a * b + b * c + c * a) := by ring
    _ = (a + b + c - c) * (a + b + c) - (a * b + b * c + c * a) := by simp
    _ = (5 - c) * 5 - 5 := by rw [h₁, h_ab_bc_ca h₁ h₂]
    _ = _ := by ring
  _ = 125 * (64 - 16 * (a + b + c) + 4 * (a * b + b * c + c * a) - a * b * c) := by ring
  _ = 125 * (64 - 16 * 5 + 4 * 5 - -1) := by
    -- Make use of the following identity to obtain `a b c`:
    -- `a^3 + b^3 + c^3 - 3 a b c = (a + b + c) * (a^2 + b^2 + c^2 - a b - b c - c a)`
    suffices a * b * c = -1 by rw [h₁, h_ab_bc_ca h₁ h₂, this]
    suffices 3 * (a * b * c) = 3 * (-1) from (mul_right_inj' three_ne_zero).mp this
    calc _
    _ = a^3 + b^3 + c^3 - (a + b + c) * (a^2 + b^2 + c^2 - (a * b + b * c + c * a)) := by ring
    _ = 47 - 5 * (15 - 5) := by rw [h₁, h₂, h₃, h_ab_bc_ca h₁ h₂]
    _ = _ := by norm_num
  _ = _ := by norm_num
