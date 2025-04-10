-- https://cloud.kili-technology.com/label/projects/label/cm91j40cn006pseaytqai8yeg

import Mathlib

/- Given $f(x) = x^2 + c$, and $f(f(x)) = f(x^2 + 1)$.
(1) Let $g(x) = f(f(x))$, find the analytical expression of the function $g(x)$;
(2) Let $\varphi(x) = g(x) - \lambda f(x)$, try to find the value of the real number
$\lambda$ such that $\varphi(x)$ is a decreasing function on $(-\infty,-1]$ and
an increasing function on $[-1,0)$. -/

theorem algebra_117773 {f g : ℝ → ℝ} (hf : ∃ c, ∀ x, f x = x ^ 2 + c)
    (hff : ∀ x, f (f x) = f (x ^ 2 + 1))
    (hg : ∀ x, g x = f (f x)) :
    (∀ x, g x = x ^ 4 + 2 * x ^ 2 + 2) ∧ AntitoneOn (fun x ↦ g x - 4 * f x) (Set.Iic (-1)) ∧
      MonotoneOn (fun x ↦ g x - 4 * f x) (Set.Ico (-1) 0) := by
  -- Determine the value of c from `f (f x) = f (x ^ 2 + 1)`.
  obtain ⟨c, hf⟩ := hf
  have hc : c = 1 := by
    have (x) : 2 * x ^ 2 * c + c ^ 2 = 2 * x ^ 2 + 1 := by
      simpa [hf, add_sq, add_assoc ((x ^ 2) ^ 2)] using hff x
    have (x) : (c + 1) * (c - 1) = -2 * x ^ 2 * (c - 1) :=
      calc _
      _ = c ^ 2 - 1 := by simp [← sq_sub_sq]
      _ = 2 * x ^ 2 * (1 - c) := by
        rw [mul_sub, sub_eq_sub_iff_add_eq_add]
        convert this x using 1 <;> ring
      _ = _ := by ring
    simp only [mul_eq_mul_right_iff] at this
    refine sub_eq_zero.mp ?_
    refine (this 0).elim (fun hc ↦ ?_) id
    refine (this 1).elim (fun hc' ↦ ?_) id
    -- Find a contradiction using different values of x.
    simpa using hc.symm.trans hc'
  -- Adopt the value of c in the definition of f.
  rw [hc] at hf
  clear hc c

  -- First prove the explicit form of g.
  refine ⟨fun x ↦ ?_, ?_⟩
  · simp only [hg, hf]
    ring

  -- Obtain the derivative of `φ = g - r f` in order to prove monotonicity.
  have hf' (x) : HasDerivAt (f ·) (2 * x) x := by
    simp only [hf]
    refine .add_const ?_ 1
    simpa using hasDerivAt_pow 2 x
  have hφ' (r x : ℝ) : HasDerivAt (fun x ↦ g x - r * f x) (2 * x * (2 * (x ^ 2 + 1) - r)) x := by
    suffices HasDerivAt (fun x ↦ g x - r * f x) (2 * (x ^ 2 + 1) * (2 * x) - r * (2 * x)) x by
      convert this using 1
      ring
    refine .sub ?_ ?_
    · rw [funext hg]
      refine .comp x ?_ (hf' x)
      rw [hf x]
      exact hf' (x ^ 2 + 1)
    · exact .const_mul r (hf' x)
  -- Specialize to r = 4.
  -- Here we see that the sign of the derivative depends on the signs of `x` and `x^2 - 1`.
  have hφ' (x : ℝ) : HasDerivAt (fun x ↦ g x - 4 * f x) (4 * x * (x ^ 2 - 1)) x := by
    convert hφ' 4 x using 1
    ring
  -- Use the derivative to complete the proof.
  refine ⟨?_, ?_⟩
  · refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic _) ?_
        (fun x _ ↦ (hφ' x).hasDerivWithinAt) ?_
    · exact HasDerivAt.continuousOn fun x _ ↦ hφ' x
    · intro x hx
      have hx : x < -1 := by simpa using hx
      refine mul_nonpos_of_nonpos_of_nonneg ?_ ?_
      · linarith
      · suffices 1 ≤ |x| by simpa using this
        refine le_abs.mpr (Or.inr ?_)
        linarith
  · refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico _ _) ?_
        (fun x _ ↦ (hφ' x).hasDerivWithinAt) ?_
    · exact HasDerivAt.continuousOn fun x _ ↦ hφ' x
    · intro x hx
      have hx : -1 < x ∧ x < 0 := by simpa using hx
      refine mul_nonneg_of_nonpos_of_nonpos ?_ ?_
      · linarith
      · suffices |x| ≤ 1 by simpa using this
        refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
