/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PSPACERepresentation
public import LeanCanny.Computation.PolyTime

/-! # Native PSPACE closure under native polynomial-time reductions -/

@[expose] public section

namespace LeanCanny.Computation
open Turing.MultiTapeTM
open scoped Classical

theorem SpaceDecider.precompose {L : Language} (D : SpaceDecider L)
    (f : List Bool → List Bool) (hf : ComputableTidilyInPolyTime f encBits encBits) :
    SpaceDecider (f ⁻¹' L) :=
  ⟨NativeSpace.preimage hf D.mem_PSPACE⟩

theorem mem_PSPACE_preimage {f : List Bool → List Bool} {L : Language}
    (hf : ComputableTidilyInPolyTime f encBits encBits) (hL : L ∈ PSPACE) : f ⁻¹' L ∈ PSPACE :=
  NativeSpace.preimage hf hL

theorem mem_PSPACE_of_reduction {L K : Language}
    (h : PolyTimeReduces L K) (hK : K ∈ PSPACE) : L ∈ PSPACE :=
  NativeSpace.of_reduction h hK

end LeanCanny.Computation
