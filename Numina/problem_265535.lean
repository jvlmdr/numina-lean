-- https://cloud.kili-technology.com/label/projects/label/cma1au4rj00hcthv5nmizgoxd

import Mathlib

/- The function $f(x)$ is defined on $\mathbf{N}$, taking values in $\mathbf{N}$, and is a
strictly increasing function (if for any $x_{1}, x_{2} \in A$, when $x_{1} < x_{2}$, we have
$f(x_{1}) < f(x_{2})$, then $f(x)$ is called a strictly increasing function on $A$),
and satisfies the condition $f(f(k)) = 3 k$. Try to find the value of $f(1) + f(9) + f(96)$. -/

theorem algebra_265535 (f : ℕ → ℕ) (h_mono : StrictMono f) (hf : ∀ k, f (f k) = 3 * k) :
    f 1 + f 9 + f 96 = 197 := by
  -- First consider `f 1`. We can eliminate 0 and 1, and show that `f 1 < 3`.
  have h1 : f 1 = 2 := by
    suffices 1 < f 1 by
      refine Nat.le_antisymm ?_ this
      suffices f 1 < 3 from Nat.le_of_lt_succ this
      -- From strict monotonicity, `1 < f 1` implies `f 1 < f (f 1) = 3`.
      simpa [hf] using h_mono this
    refine (Nat.two_le_iff (f 1)).mpr ⟨?_, ?_⟩
    -- Cannot have `f 1 = 0` because there needs to exist some `f 0` less than `f 1`.
    · exact Nat.not_eq_zero_of_lt (h_mono zero_lt_one)
    -- Cannot have `f 1 = 1` because `f 1 = f (f 1) = 3`, a contradiction.
    · intro h
      specialize hf 1
      rw [h, h] at hf
      contradiction
  -- It follows that `f 2 = f (f 1) = 3`.
  have h2 : f 2 = 3 := h1 ▸ hf 1

  -- Consider `f (f (f k))` and apply the definition to the inner and outer pair.
  have h3k (k) : f (3 * k) = 3 * f k :=
    calc _
    _ = f (f (f k)) := congrArg f (hf k).symm
    _ = _ := hf (f k)
  -- This enables us to obtain several more values of `f`.
  -- In order to obtain `f 96 = f (3 * 32) = 3 * f 32` we require `f 32`.
  have h3 : f 3 = 6 := by simpa [h1] using h3k 1
  have h6 : f 6 = 9 := by simpa [h2] using h3k 2
  have h9 : f 9 = 18 := by simpa [h3] using h3k 3
  have h18 : f 18 = 27 := by simpa [h6] using h3k 6
  have h27 : f 27 = 54 := by simpa [h9] using h3k 9
  have h54 : f 54 = 81 := by simpa [h18] using h3k 18

  -- Observe that `f 54 - f 27 = 27 = 81 - 54`.
  -- Since the function is *strictly* increasing, it must increase in steps of 1.
  -- Hence `f (27 + i) = 54 + i` for `0 ≤ i ≤ 27`, sufficient to conclude the proof.
  suffices ∀ i < 28, f (27 + i) = 54 + i by simp [h1, h9, h3k 32, this 5]
  -- Switch to `Fin 28` to use `StrictMono.range_inj`, which is defined in terms of `Set.range`.
  suffices ∀ (i : Fin 28), f (27 + i.val) = 54 + i.val by simpa [Fin.forall_iff] using this
  refine funext_iff.mp ?_
  refine (StrictMono.range_inj ?_ ?_).mp ?_
  · exact h_mono.comp (Fin.val_strictMono.const_add 27)
  · exact Fin.val_strictMono.const_add 54

  -- Now it remains to prove that the two sets are equal using their cardinality.
  -- Switch back to `Finset ℕ` where finiteness is known and finite intervals have better support.
  suffices Finset.univ.image (f ∘ (27 + ·) ∘ Fin.val : Fin 28 → ℕ) =
      Finset.univ.image ((54 + ·) ∘ Fin.val : Fin 28 → ℕ) by
    simpa using congrArg Finset.toSet this
  -- Definitionally equal to `Finset.Icc`.
  change (Finset.Icc 27 54).image f = Finset.Icc 54 81
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · -- Replace `54` and `81` with `f 27` and `f 54`.
    suffices (Finset.Icc 27 54).image f ⊆ Finset.Icc (f 27) (f 54) by simpa [h27, h54] using this
    -- Switch to `Set ℕ` in order to use `Monotone.image_Icc_subset`.
    refine Finset.coe_subset.mp ?_
    simpa using h_mono.monotone.image_Icc_subset
  · -- Use injectivity of `f` (from strict monotonicity) to show cardinalities are equal.
    simp [Finset.card_image_of_injective _ h_mono.injective]
