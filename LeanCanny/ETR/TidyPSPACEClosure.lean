/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.Complexity
public import LeanCanny.Computation.TidyPSPACE

/-! # The Canny target in Complexitylib2's PSPACE

The existing encoded ETR language and reduction class are unchanged. Proving
ETR membership in the tidy foundation suffices for all of the class ∃ℝ.
-/

@[expose] public section

namespace LeanCanny

theorem existsReal_subset_tidyPSPACE_iff :
    ExistsReal ⊆ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits ↔
      ETR.language ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  existsReal_subset_iff (fun h hK => Computation.TidyPSPACE.of_reduction h hK)

end LeanCanny
