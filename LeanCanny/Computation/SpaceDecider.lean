/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Tactic.PolyTime
public import LeanCanny.Computation.NativeSpaceClosure

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
    (hL : ∀ x, x ∈ L ↔ f x = true) : SpaceDecider L :=
  ⟨NativeSpace.of_computable hf hL⟩

theorem computable {L : LeanCanny.Language} (D : SpaceDecider L) :
    ComputableTidilyInPolySpace (fun x => @decide (x ∈ L) (Classical.propDecidable _))
      encBits encBool := by
  classical
  obtain ⟨g, hspace, hL⟩ := NativeSpace.mem_iff.mp D.mem_PSPACE
  exact hspace.congr fun x => Bool.eq_iff_iff.mpr (by
    rw [decide_eq_true_eq]
    exact (hL x).symm)

theorem congr {L M : LeanCanny.Language} (D : SpaceDecider L) (h : L = M) : SpaceDecider M :=
  h ▸ D

theorem ofPSPACE {L : LeanCanny.Language} (hL : L ∈ PSPACE) : SpaceDecider L := ⟨hL⟩

end SpaceDecider
end Computation
end LeanCanny
