/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SpaceDecider

/-! # The decider interface is exactly Complexitylib2 PSPACE membership -/

@[expose] public section

namespace LeanCanny.Computation
open Complexity

theorem nonempty_spaceDecider_of_mem_PSPACE {L : Language} (hL : L ∈ PSPACE) :
    Nonempty (SpaceDecider L) := ⟨⟨hL⟩⟩

theorem mem_PSPACE_iff_nonempty_spaceDecider (L : Language) :
    L ∈ PSPACE ↔ Nonempty (SpaceDecider L) :=
  ⟨nonempty_spaceDecider_of_mem_PSPACE, fun ⟨D⟩ => D.mem_PSPACE⟩

end LeanCanny.Computation
