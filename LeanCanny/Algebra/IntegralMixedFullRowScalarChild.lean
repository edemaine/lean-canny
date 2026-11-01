/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFullRowNative

/-! # Actual scalar models for the restored original-row child -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullRowScalarChild
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedFullRowTasks
open scoped Classical

theorem original_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedOriginalScaleBits.value P F q =
      residueBits (IntegralMixedVirtualOriginalRows.originalScale F (IntegralMixedVirtualTaskBits.saved P q) : ZMod (modulus P q)) := rfl

theorem leading_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralCriticalLeadingBits.value (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen q =
      residueBits ((IntegralMixedVirtualOriginalRows.originalScale F (IntegralMixedVirtualTaskBits.saved P q) *
        (F.spatial (IntegralMixedVirtualTaskBits.saved P q)).degree : ℤ) : ZMod (modulus P q)) := rfl

theorem scalar_modulus (P : Parameters) (p : Phase) (q : List Bool) :
    modulus P (IntegralMixedRoutineTaskBits.query P (birth P) .scalar p q) = modulus P q := by
  unfold modulus
  rw [IntegralMixedRoutineTaskBits.query_get]
  rfl

theorem original_child (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedOriginalScaleBits.value P F (IntegralMixedOriginalScaleBits.query P q) =
      residueBits (IntegralMixedVirtualOriginalRows.originalScale F (IntegralMixedVirtualTaskBits.saved P q) : ZMod (modulus P q)) := by
  rw [original_snapshot, IntegralMixedOriginalScaleBits.query, IntegralMixedRoutineTaskBits.query_saved]
  exact congrArg (fun m : ℕ => residueBits
    (IntegralMixedVirtualOriginalRows.originalScale F (IntegralMixedVirtualTaskBits.saved P q) : ZMod m))
      (scalar_modulus P .productEntry q)

theorem leading_child (P : Parameters) (F : Family) (q : List Bool) :
    IntegralCriticalLeadingBits.value (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen
      (IntegralMixedScalarQueryBits.commonLeading P q) =
      residueBits ((IntegralMixedVirtualOriginalRows.originalScale F (IntegralMixedVirtualTaskBits.saved P q) *
        (F.spatial (IntegralMixedVirtualTaskBits.saved P q)).degree : ℤ) : ZMod (modulus P q)) := by
  rw [leading_snapshot, IntegralMixedScalarQueryBits.commonLeading, IntegralMixedRoutineTaskBits.query_saved]
  exact congrArg (fun m : ℕ => residueBits
    ((IntegralMixedVirtualOriginalRows.originalScale F (IntegralMixedVirtualTaskBits.saved P q) *
      (F.spatial (IntegralMixedVirtualTaskBits.saved P q)).degree : ℤ) : ZMod m)) (scalar_modulus P .monomialFactor q)

noncomputable def model (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if equation P F q then IntegralMixedOriginalScaleBits.value P F (scalarTask P F q)
  else IntegralCriticalLeadingBits.value (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen (scalarTask P F q)

theorem model_eq (P : Parameters) (F : Family) (q : List Bool) :
    model P F q = residueBits (IntegralMixedFullRowMultiplier.scalar (family P F) (indices P F) q : ZMod (modulus P q)) := by
  unfold model scalarTask IntegralMixedFullRowMultiplier.scalar
  split_ifs
  · exact original_child P F q
  · exact leading_child P F q

end LeanCanny.Algebra.IntegralMixedFullRowScalarChild
