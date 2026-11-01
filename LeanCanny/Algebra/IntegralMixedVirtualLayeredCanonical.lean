/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualLayeredModel
public import LeanCanny.Algebra.IntegralMixedVirtualLowerCanonical
/-! # Canonical residue witness for the virtual layered matrix entry -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualCanonicalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

theorem productEntry_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedVirtualLayeredBits.productEntry P F q := by
  unfold IntegralMixedVirtualLayeredBits.productEntry
  rw [IntegralMixedVirtualLayeredBits.layered_snapshot]
  exact entryBits_canonical _ _ _
end LeanCanny.Algebra.IntegralMixedVirtualCanonicalBits
