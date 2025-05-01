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
  have h3 : f 3 = 6 := by simpa [h1] using h3k 1
  have h6 : f 6 = 9 := by simpa [h2] using h3k 2
  have h9 : f 9 = 18 := by simpa [h3] using h3k 3
  have h18 : f 18 = 27 := by simpa [h6] using h3k 6
  have h27 : f 27 = 54 := by simpa [h9] using h3k 9
  have h54 : f 54 = 81 := by simpa [h18] using h3k 18
  -- Observe that `f 54 - f 27 = 27 = 81 - 54`. By strict monotonicity, this means that
  -- `f (27 + i) = 54 + i` for `i = 0, 1, ..., 27`.
  -- This will enable us to obtain `f 96 = 3 * f 32`.
  suffices ∀ i < 28, f (27 + i) = 54 + i by simp [h1, h9, h3k 32, this 5]
  -- Switch to `Fin 28` to use `StrictMono.range_inj`, which is defined in terms of `Set.range`.
  suffices ∀ (i : Fin 28), f (27 + i.val) = 54 + i.val by simpa [Fin.forall_iff] using this
  refine funext_iff.mp ?_
  refine (StrictMono.range_inj ?_ ?_).mp ?_
  · exact h_mono.comp (Fin.val_strictMono.const_add 27)
  · exact Fin.val_strictMono.const_add 54
  calc _
  _ = Set.range (f ∘ (27 + ·) ∘ Fin.val : Fin 28 → ℕ) := rfl
  _ = Finset.image f (Finset.map (addLeftEmbedding 27)
      (Finset.map Fin.valEmbedding (Finset.univ : Finset (Fin 28)))) := by
    simp [Set.range_comp]
  _ = Finset.image f (Finset.map (addLeftEmbedding 27) (Finset.Iio 28)) := by
    rw [Fin.map_valEmbedding_univ]
  _ = Finset.image f (Finset.map (addLeftEmbedding 27) (Finset.Ico 0 28)) := by simp
  _ = Finset.image f (Finset.Ico 27 55) := by rw [Finset.map_add_left_Ico]
  _ = Finset.image f (Finset.Icc 27 54) := rfl
  _ = Finset.Icc (f 27 ) (f 54) := by
    refine congrArg _ ?_
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · suffices Finset.toSet (Finset.image f (Finset.Icc 27 54)) ⊆
          Finset.toSet (Finset.Icc (f 27) (f 54)) from this
      simp only [Finset.coe_image, Finset.coe_Icc]
      exact h_mono.monotone.image_Icc_subset
    · refine le_of_eq ?_
      calc _
      _ = (Finset.Icc 27 54).card := by simp [h27, h54]
      _ = _ := (Finset.card_image_of_injective _ h_mono.injective).symm
  _ = _ := by
    rw [h27, h54]
    calc _
    _ = Finset.toSet (.map (addLeftEmbedding 54)
        (.map Fin.valEmbedding (.univ : Finset (Fin 28)))) := rfl
    _ = Set.range ((54 + ·) ∘ fun x : Fin 28 ↦ x.val) := by simp [Set.range_comp]
