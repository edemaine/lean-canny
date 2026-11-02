/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullChoiceProbe
public import LeanCanny.Algebra.IntegralMixedFramedChoiceCoefficientTransport
public import LeanCanny.Algebra.IntegralMixedFramedCutCoefficientPolynomial
public import LeanCanny.Algebra.IntegralMixedFramedCutSourceProfile
/-! # Canonical lower-choice coefficients in the actual parent algebra

Only active virtual contexts denote cut queries. All other task words
represent zero. The coefficient algebra and basis are still those of the
literal saved parent; no independently chosen coordinate roots occur.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSourceBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedCutMatrix.coefficientMatrix

noncomputable def source (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    IntegralCoordinateCoefficientBits.Family where
  arity c := (family P D H).birth (IntegralMixedVirtualTaskBits.saved P c)
  width c := (family P D H).width (IntegralMixedVirtualTaskBits.saved P c)
  carrier c := ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.carrier
  ring c := ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.ring
  basis c := ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis
  element c := if IntegralMixedFramedFullCutProbeBits.Active P c then
    (IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
      ((family P D H).birth_bound _) ((family P D H).rule _) (IntegralMixedRelativeCuts.atChoice ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).kind _) (IntegralMixedRawKindChoiceBits.requested P c))).coeff (get P .coefficient c)
    else 0

theorem arity (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
    (source P D H).arity c=birth P c := (IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth c
theorem width (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
    (source P D H).width c=P.width (RankedHistoryTask.root c) := (IntegralMixedFramedHistoryFamilyBits.geometry P D H).width c

theorem arity_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (source P D H).arity := (IntegralMixedOldHeightBits.birth_unary P a).of_eq (fun c=>(arity P D H c).symm)
theorem width_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    UnaryFn (source P D H).width := (a.width.comp RankedHistoryTask.root_FP).of_eq (fun c=>(width P D H c).symm)

theorem matrix_active (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool)
    (ha : IntegralMixedFramedFullCutProbeBits.Active P c) :
    (source P D H).matrix c=IntegralMixedFramedChoiceCoefficientBits.coefficient P D H
      (IntegralMixedVirtualTaskBits.saved P c) (IntegralMixedRawKindChoiceBits.requested P c) (get P .coefficient c) := by
  unfold IntegralCoordinateCoefficientBits.Family.matrix
  simp only [source,ite_eq_left ha]
  unfold IntegralMixedFramedChoiceCoefficientBits.coefficient IntegralMixedCutMatrix.coefficientMatrix
  rfl

theorem matrix_inactive (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool)
    (ha : ¬IntegralMixedFramedFullCutProbeBits.Active P c) : (source P D H).matrix c=0 := by
  unfold IntegralCoordinateCoefficientBits.Family.matrix
  simp only [source,ite_eq_right ha]
  let := ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.ring
  exact (Algebra.leftMulMatrix ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c)).sampler.scalarPrefix.basis.finBasis).map_zero

theorem matrix_outside (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool)
    (hk : 2^P.width (RankedHistoryTask.root c)≤get P .coefficient c) : (source P D H).matrix c=0 := by
  by_cases ha : IntegralMixedFramedFullCutProbeBits.Active P c
  · rw [matrix_active P D H c ha]
    have HX := IntegralMixedCutNilpotent.coefficient_outside
      ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
      ((family P D H).birth_bound (IntegralMixedVirtualTaskBits.saved P c))
      ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c))
      (IntegralMixedRelativeCuts.atChoice ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).kind _) (IntegralMixedRawKindChoiceBits.requested P c))
      ((family P D H).scalar_cap (IntegralMixedVirtualTaskBits.saved P c)) (get P .coefficient c) (by
        simpa only [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width c] using hk)
    unfold IntegralMixedFramedChoiceCoefficientBits.coefficient
    exact HX
  · exact matrix_inactive P D H c ha

end LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSourceBits
