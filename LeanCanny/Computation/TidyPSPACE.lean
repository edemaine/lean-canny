/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceFunctionTidy
public import LeanCanny.Computation.SpaceDeciderFunction
public import LeanCanny.Computation.PSPACERepresentation
public import Complexitylib.Classes.NP.Reduction
public import Complexity.Computability.Complexity.Classes.Space

/-! # PSPACE in the tidy foundation

New space certificates target Complexitylib2's standard machine-based `PSPACE`.
Existing certified deciders transfer through the legacy adapter. Polynomial-time
preprocessing reuses the existing FP proofs and composes functions directly.
-/

@[expose] public section

namespace LeanCanny.Computation.TidyPSPACE

open Turing.MultiTapeTM

theorem of_computable {α : Type} {enc : α ↪ List Bool} {L : Set α} {f : α → Bool}
    (hf : ComputableTidilyInPolySpace f enc encBool) (hL : ∀ x, x ∈ L ↔ f x = true) :
    L ∈ Cslib.Complexity.PSPACE enc := by
  obtain ⟨T, S, hS, c, h, -⟩ := hf
  exact ⟨f, ⟨_, _, (PolyBounded.const c).mul (hS.add (.const 1)),
    h.computableInTimeAndSpace⟩, hL⟩

theorem decider {L : Complexity.Language} (D : SpaceDecider L) :
    L ∈ Cslib.Complexity.PSPACE encBits := by
  classical
  obtain ⟨T, S, hS, h⟩ := D.flagEvaluator.computable
  have hf : ComputableTidilyInPolySpace (fun x => decide (x ∈ L)) encBits encBool :=
    ⟨T, S, hS, h.of_enc_eq fun _ => rfl⟩
  exact of_computable hf fun _ => decide_eq_true_iff.symm

theorem of_legacy {L : Complexity.Language} (hL : L ∈ Complexity.PSPACE) :
    L ∈ Cslib.Complexity.PSPACE encBits :=
  decider (SpaceDecider.ofPSPACE hL)

theorem preimage {f : List Bool → List Bool} {L : Complexity.Language}
    (hf : f ∈ Complexity.FP) (hL : L ∈ Cslib.Complexity.PSPACE encBits) :
    f ⁻¹' L ∈ Cslib.Complexity.PSPACE encBits := by
  obtain ⟨g, ⟨t, s, hs, hg⟩, hL⟩ := hL
  obtain ⟨c, hg⟩ := hg.exists_computableTidilyInTimeAndSpace
  have hspace : ComputableTidilyInPolySpace g encBits encBool := by
    refine ⟨(fun x => 2 * t x + 3 * s x + c), (fun x => c * (s x + 1) + 1),
      ((PolyBounded.const c).mul (hs.add (.const 1))).add (.const 1),
      ComputableTidilyInO.of_bounds hg 1 ?_ ?_ ?_⟩
    · intro x; omega
    · intro x; omega
    · intro x
      simp only [encBool_apply, List.length_singleton, one_mul]
      omega
  exact of_computable (hspace.comp (ComputableTidilyInPolySpace.of_polyTime
    (TidyFP.of_mem_FP hf))) fun x => hL (f x)

theorem of_reduction {L K : Complexity.Language} (h : Complexity.MapReducesPoly L K)
    (hK : K ∈ Cslib.Complexity.PSPACE encBits) : L ∈ Cslib.Complexity.PSPACE encBits := by
  obtain ⟨f, hf, hspec⟩ := h
  have hL : L = f ⁻¹' K := Set.ext hspec
  rw [hL]
  exact preimage hf hK

end LeanCanny.Computation.TidyPSPACE
