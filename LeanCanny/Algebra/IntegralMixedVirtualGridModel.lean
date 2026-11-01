/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualMonomialSnapshot
/-! # Actual virtual product and masked grid-term values -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualGridBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

noncomputable def product (P : Parameters) (F : Family) (q : List Bool) := (IntegralMixedVirtualMonomialBits.source P F).value q
noncomputable def term (P : Parameters) (F : Family) (q : List Bool) :=
  IntegralClearedCoefficientBits.maskedProgram (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F))
    (IntegralCriticalFlatGridBits.termInput P q)

theorem source_modulus (P : Parameters) (F : Family) (q : List Bool) :
    (IntegralMixedVirtualMonomialBits.source P F).modulus q = modulus P q := by
  change modulus P (pairFst (IntegralCriticalFlatGridBits.termInput P q)) = _
  rw [IntegralCriticalFlatGridBits.termInput_parent]

theorem term_as_product (P : Parameters) (F : Family) (q : List Bool) :
    term P F q = if ClearedCoordinateExponentBits.mask
      (IntegralClearedCoefficientBits.maskLayout (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)))
      (IntegralCriticalFlatGridBits.termInput P q) then product P F q else [] := rfl
end LeanCanny.Algebra.IntegralMixedVirtualGridBits
