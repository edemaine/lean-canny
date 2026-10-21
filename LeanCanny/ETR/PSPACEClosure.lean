/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.Complexity
public import LeanCanny.Computation.PSPACEClosure

/-!
# The PSPACE consequence of an ETR upper bound

PSPACE closure under polynomial-time reductions discharges the class-theoretic
part of `∃ℝ ⊆ PSPACE`. Canny's algorithm must still establish the ETR membership
hypothesis; these conditional results do not assert that unfinished theorem.
-/

@[expose] public section

namespace LeanCanny


theorem existsReal_subset_PSPACE_iff : ExistsReal ⊆ PSPACE ↔ ETR.language ∈ PSPACE :=
  existsReal_subset_iff Computation.mem_PSPACE_of_reduction

theorem existsReal_subset_PSPACE_of_etr (h : ETR.language ∈ PSPACE) : ExistsReal ⊆ PSPACE :=
  existsReal_subset_PSPACE_iff.mpr h

theorem existsReal_subset_PSPACE_iff_complete {L : Language} (hL : ExistsRealComplete L) :
    ExistsReal ⊆ PSPACE ↔ L ∈ PSPACE := by
  constructor
  · exact fun h => h hL.1
  · exact fun h K hK => Computation.mem_PSPACE_of_reduction (hL.2 K hK) h

end LeanCanny
