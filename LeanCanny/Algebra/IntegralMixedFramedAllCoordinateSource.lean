/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedAllCoordinateBounds
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSource
/-! # Unrestricted coordinate coefficients in the literal parent algebra

The Y degree is checked against the full coordinate degree, independently
of the creating cut's recorded trailing choice. Parameter coefficients
outside the fixed scalar width vanish. All elements use one old bank.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedAllCoordinateSourceBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedCutMatrix.coefficientMatrix

noncomputable def Active (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : Prop :=
  IntegralMixedFramedFullCutProbeBits.Active P q ∧ get P .slot13 q≤P.ambient (RankedHistoryTask.root q)+1 ∧
    get P .slot8 q<IntegralMixedCoordinateCoefficientTasks.choiceBound P (family P D H) q ∧
    get P .slot8 q≤2^P.width (RankedHistoryTask.root q)
theorem active_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H)) : FPPred (Active P D H) :=
  (IntegralMixedFramedFullCutProbeBits.active_FP P a).and
    (((get_binary P a .slot13).le ((BinaryFn.ofUnary (a.ambient.comp RankedHistoryTask.root_FP)).add (BinaryFn.const 1))).and
      (((get_binary P a .slot8).lt (IntegralMixedCoordinateCoefficientTasks.choiceBound_binary P a (family P D H) I)).and
        ((get_binary P a .slot8).le ((BinaryFn.const 2).powUnary (a.width.comp RankedHistoryTask.root_FP)))))

noncomputable def source (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    IntegralCoordinateCoefficientBits.Family where
  arity q := (family P D H).birth (IntegralMixedVirtualTaskBits.saved P q)
  width q := (family P D H).width (IntegralMixedVirtualTaskBits.saved P q)
  carrier q := ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.carrier
  ring q := ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.ring
  basis q := ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.basis
  element q := if Active P D H q then
    (IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))
      ((family P D H).birth_bound _) ((family P D H).rule _)
      (IntegralMixedCoordinateCoefficientSnapshot.kind (family P D H) (IntegralMixedVirtualTaskBits.saved P q)
        (get P .slot13 q) (get P .slot8 q))).coeff (get P .coefficient q)
    else 0

theorem arity (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    (source P D H).arity q=birth P q := (IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth q
theorem width (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    (source P D H).width q=P.width (RankedHistoryTask.root q) := (IntegralMixedFramedHistoryFamilyBits.geometry P D H).width q
theorem arity_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (source P D H).arity := (IntegralMixedOldHeightBits.birth_unary P a).of_eq (fun q=>(arity P D H q).symm)
theorem width_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (source P D H).width := (a.width.comp RankedHistoryTask.root_FP).of_eq (fun q=>(width P D H q).symm)

theorem matrix_active (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (ha : Active P D H q) :
    (source P D H).matrix q=IntegralMixedFramedAllCoordinateBits.coefficient P D H
      (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q) (get P .coefficient q) := by
  unfold IntegralCoordinateCoefficientBits.Family.matrix
  simp only [source,ite_eq_left ha]
  unfold IntegralMixedFramedAllCoordinateBits.coefficient IntegralMixedCutMatrix.coefficientMatrix
  rfl

theorem matrix_inactive (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (ha : ¬Active P D H q) : (source P D H).matrix q=0 := by
  unfold IntegralCoordinateCoefficientBits.Family.matrix
  simp only [source,ite_eq_right ha]
  let := ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.ring
  exact (Algebra.leftMulMatrix ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q)).sampler.scalarPrefix.basis.finBasis).map_zero

theorem matrix_outside (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (hk : 2^P.width (RankedHistoryTask.root q)≤get P .coefficient q) : (source P D H).matrix q=0 := by
  by_cases ha : Active P D H q
  · rw [matrix_active P D H q ha]
    have HX:=IntegralMixedCutNilpotent.coefficient_outside ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))
      ((family P D H).birth_bound _) ((family P D H).rule _)
      (IntegralMixedCoordinateCoefficientSnapshot.kind (family P D H) (IntegralMixedVirtualTaskBits.saved P q)
        (get P .slot13 q) (get P .slot8 q)) ((family P D H).scalar_cap _) (get P .coefficient q) (by
          simpa only [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width q] using hk)
    exact HX
  · exact matrix_inactive P D H q ha

end LeanCanny.Algebra.IntegralMixedFramedAllCoordinateSourceBits
