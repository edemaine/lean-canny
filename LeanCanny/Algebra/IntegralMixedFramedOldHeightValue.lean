/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightRootSnapshot
/-! # Literal old-height values equal cofactor-scaled earlier companion entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryScript IntegralMixedHistory
open IntegralMixedOldHeightBits (valid request radix producerBirth index)
open IntegralMixedOldBankCofactorBits (Routing)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem entry_formula (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (q : List Bool) (hv : valid P q) :
    Algebra.leftMulMatrix (state P D F q).sampler.scalarPrefix.basis.finBasis
      (cleared (state P D F q) (bankIndex P D F q hv.1)) (rowIndex P D F q hv.2.1) (colIndex P D F q hv.2.2) =
    cofactor P D F q * (if get P .row q % radix P q = get P .col q % radix P q then companionInteger P D F R q else 0) := by
  let key := IntegralMixedVirtualTaskBits.saved P q
  let i := bankIndex P D F q hv.1
  let r := rowIndex P D F q hv.2.1
  let t := colIndex P D F q hv.2.2
  have H := (IntegralMixedFramedHistoryFamilyBits.origin P D F key i).cleared_matrix
    (IntegralMixedFramedHistoryFamilyBits.family_canonical P D F key) r t
  rw [origin_entry_root P D F key i r t] at H
  rw [cofactor_eq P D F q hv.1, companionInteger_root]
  simpa only [state, bankFamily, IntegralMixedFramedHistoryFamilyBits.family, key, i, r, t, bankIndex, rowIndex, colIndex,
    IntegralMixedFullHistoryFamilyBits.saved_root, IntegralMixedFullHistoryFamilyBits.saved_prefix,
    radix, producerBirth, index, min_eq_left hv.1.le, reframe, cleared] using H

theorem value_request (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (q : List Bool) (hq : request P q) :
    value P D F q = residueBits (cofactor P D F q * companionInteger P D F R q : ZMod (modulus P q)) := by
  rw [value, dite_eq_left hq.1, entry_formula P D F R q hq.1, ite_eq_left hq.2, Int.cast_mul]

theorem value_not_request (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (q : List Bool) (hq : ¬ request P q) : value P D F q = [] := by
  by_cases hv : valid P q
  · have HD : ¬ get P .row q % radix P q = get P .col q % radix P q := fun he => hq ⟨hv, he⟩
    rw [value, dite_eq_left hv, entry_formula P D F R q hv, ite_eq_right HD, mul_zero, Int.cast_zero]
    exact (ArithmeticBits.zero_residueBits _).symm
  · exact value_invalid P D F q hv

end LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
