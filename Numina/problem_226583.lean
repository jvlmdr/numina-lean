-- https://cloud.kili-technology.com/label/projects/label/cmcbosy9y000sueaxwypta4u0

import Mathlib

/- Prove that any natural number $n$ can be uniquely represented in the form
$n = F_{k_{1}} + F_{k_{2}} + \ldots + F_{k_{m}}$, where
$k_{1} > k_{2} + 1, k_{2} > k_{3} + 1, \ldots, k_{m-1} > k_{m} + 1, k_{m} > 1$. -/

theorem number_theory_226583 {n : ℕ} :
    ∃! l : List ℕ, (l.Chain' fun i j ↦ j + 1 < i) ∧ (∀ h : l ≠ [], 1 < l.getLast h) ∧
      (l.map Nat.fib).sum = n := by
  -- This already exists in Mathlib as `Nat.zeckendorf`.
  refine ⟨n.zeckendorf, ?_, ?_⟩
  · have hl : List.Chain' (fun a b ↦ b + 1 < a) (n.zeckendorf ++ [0]) :=
      Nat.isZeckendorfRep_zeckendorf n
    -- Unpack the chain proposition on `l ++ [0]` into separate propositions.
    rw [List.chain'_append] at hl
    rcases hl with ⟨hl_chain, _, hl_last⟩
    split_ands
    · exact hl_chain
    · intro h
      simpa using hl_last _ (List.getLast_mem_getLast? h)
    · exact Nat.sum_zeckendorf_fib n
  · intro l ⟨hl_gap, hl_min, hl_sum⟩
    -- Establish the chain proposition from the separate propositions.
    have hl : l.IsZeckendorfRep := by
      refine hl_gap.append (List.chain'_singleton 0) fun x hx ↦ ?_
      suffices 1 < x by simpa
      have h : l ≠ [] := List.ne_nil_of_mem (List.mem_of_mem_getLast? hx)
      convert hl_min h
      symm
      exact (List.getLast_eq_iff_getLast_eq_some h).mpr hx
    -- Use the `Equiv` to establish uniqueness.
    suffices ⟨l, hl⟩ = Nat.zeckendorfEquiv n from congrArg Subtype.val this
    exact Nat.zeckendorfEquiv.symm_apply_eq.mp hl_sum
