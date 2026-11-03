/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalAffineCurrent
public import LeanCanny.Algebra.IntegralCoordinatePoweredLocalSpace
/-! # Original affine heights as actual old-bank algebra elements

The family uses the literal saved source, birth and scalar basis. Invalid or
nonphysical contexts have the zero element; no matrix evaluator is postulated.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedOldHeightBits (state bankFamily)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Active (P : Parameters) (q : List Bool) : Prop := IntegralMixedVirtualCaps.valid P q ∧ get P .slot15 q=1

theorem active_FP (P : Parameters) (a : Access P) : FPPred (Active P) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and ((get_binary P a .slot15).eq (BinaryFn.const 1))

noncomputable def family (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    IntegralCoordinateCoefficientBits.Family where
  arity q := (bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q)
  width q := (bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)
  carrier q := (state P D J q).sampler.scalarPrefix.carrier
  ring q := (state P D J q).sampler.scalarPrefix.ring
  basis q := (state P D J q).sampler.scalarPrefix.basis
  element q := if Active P q then
    IntegralMixedHistory.expression (state P D J q) (IntegralMixedFramedScalarCellsBits.affine P D J q) else 0

theorem arity_eq (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    (family P D J).arity q=birth P q := IntegralMixedFramedOldHeightBits.bank_birth P D J q

theorem width_eq (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    (family P D J).width q=P.width (RankedHistoryTask.root q) :=
  (IntegralMixedFramedHistoryFamilyBits.geometry P D J).width q

theorem arity_unary (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (family P D J).arity :=
  (RankedHistoryTask.birth_unary _ (birthCap_unary P a)).of_eq (fun q=>(arity_eq P D J q).symm)

theorem width_unary (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (family P D J).width :=
  (a.width.comp RankedHistoryTask.root_FP).of_eq (fun q=>(width_eq P D J q).symm)

theorem matrix_active (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hq : Active P q)
    (r t : Fin (count ((family P D J).arity q) ((family P D J).width q))) :
    (family P D J).matrix q r t=Algebra.leftMulMatrix (state P D J q).sampler.scalarPrefix.basis.finBasis
      (IntegralMixedHistory.expression (state P D J q) (IntegralMixedFramedScalarCellsBits.affine P D J q)) r t := by
  change Algebra.leftMulMatrix (state P D J q).sampler.scalarPrefix.basis.finBasis
    (if Active P q then IntegralMixedHistory.expression (state P D J q) (IntegralMixedFramedScalarCellsBits.affine P D J q) else 0) r t=_
  rw [ite_eq_left hq]

theorem matrix_inactive (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (hq : ¬Active P q)
    (r t : Fin (count ((family P D J).arity q) ((family P D J).width q))) :
    (family P D J).matrix q r t=0 := by
  change Algebra.leftMulMatrix (state P D J q).sampler.scalarPrefix.basis.finBasis
    (if Active P q then IntegralMixedHistory.expression (state P D J q) (IntegralMixedFramedScalarCellsBits.affine P D J q) else 0) r t=_
  rw [ite_eq_right hq]
  simp only [map_zero,Matrix.zero_apply]

end LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightBits
