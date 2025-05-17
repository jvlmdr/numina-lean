-- https://cloud.kili-technology.com/label/projects/label/cma3ygbn1002pahayrzqk7zjx

import Mathlib

open Polynomial

/- Prove the Intermediate Value Theorem for a quadratic trinomial. -/

theorem algebra_222793 (c₀ c₁ c₂ : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = c₂ * x ^ 2 + c₁ * x + c₀)
    (a b y : ℝ) (hy : y ∈ Set.uIcc (f a) (f b)) :
    ∃ x ∈ Set.uIcc a b, f x = y := by
  -- We already have the intermediate value theorem in Mathlib.
  refine intermediate_value_uIcc ?_ hy
  -- To prove that the quadratic is continuous, we use the fact that it is a Polynomial.
  let p := C c₂ * X ^ 2 + C c₁ * X + C c₀
  suffices f = p.eval by simpa [this] using p.continuousOn_aeval
  unfold p
  funext x
  simpa using hf x
