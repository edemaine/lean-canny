/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Tactic.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Complexity.Classes.Space

/-! # Polynomial-space decision certificates

The class and machine semantics are Complexitylib2's. A certificate carries only
membership, with no separate transition system or execution clock.
-/

@[expose] public section

namespace LeanCanny
open Turing.MultiTapeTM

abbrev PSPACE : Set LeanCanny.Language := Cslib.Complexity.PSPACE encBits

namespace Computation

structure SpaceDecider (L : LeanCanny.Language) : Prop where
  mem_PSPACE : L ∈ PSPACE

namespace SpaceDecider

theorem of_computable {L : LeanCanny.Language} {f : List Bool → Bool}
    (hf : ComputableTidilyInPolySpace f encBits encBool)
    (hL : ∀ x, x ∈ L ↔ f x = true) : SpaceDecider L := by
  obtain ⟨T, S, hS, c, h, -⟩ := hf
  exact ⟨f, ⟨_, _, (PolyBounded.const c).mul (hS.add (.const 1)),
    h.computableInTimeAndSpace⟩, hL⟩

theorem computable {L : LeanCanny.Language} (D : SpaceDecider L) :
    ComputableTidilyInPolySpace (fun x => @decide (x ∈ L) (Classical.propDecidable _))
      encBits encBool := by
  classical
  obtain ⟨g, ⟨t, s, hs, hg⟩, hL⟩ := D.mem_PSPACE
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
  exact hspace.congr fun x => Bool.eq_iff_iff.mpr (by
    rw [decide_eq_true_eq]
    exact (hL x).symm)

theorem congr {L M : LeanCanny.Language} (D : SpaceDecider L) (h : L = M) : SpaceDecider M :=
  h ▸ D

theorem ofPSPACE {L : LeanCanny.Language} (hL : L ∈ PSPACE) : SpaceDecider L := ⟨hL⟩

end SpaceDecider
end Computation
end LeanCanny
