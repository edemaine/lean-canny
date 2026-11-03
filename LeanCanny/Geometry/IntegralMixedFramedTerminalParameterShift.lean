/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedTerminalParameterShift
public import LeanCanny.Geometry.IntegralMixedFramedWindowQuery
/-! # Exact same-terminal semantics and mass of actual parameter-shift tests -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedTerminalParameterShift
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open IntegralMixedFramedCoordinateBivariateBits (nativeWidth)
open IntegralMixedFramedTerminalParameterShiftBits (endpointFamily original compiled original_fit)
open scoped Classical

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d e y : List Bool→ℕ) (index : List Bool→ℕ)

theorem sign (negative : Bool) (c : List Bool) (hi : index c<(atKey P D H (terminal c)).count)
    (z : Fin (atKey P D H (terminal c)).count→ℝ) (δ : ℝ) :
    SignType.sign (((compiled P D H L F C hs parent terminal d e y index negative).polynomial c).eval₂
      (Int.castRingHom ℝ) (Fin.cons δ z))=
      SignType.sign (((IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e c).coeff (y c)).eval₂
        (Int.castRingHom ℝ) (Fin.cons (IntegralMixedCanonicalBankPoint.point
          (IntegralMixedFramedBankTermSign.state P D H (terminal c)) z ⟨index c,hi⟩+
            if negative then -δ else δ) z)) :=by
  exact (RationalMonomialParameterShift.native_sign (endpointFamily P D H L F C hs terminal index) negative
    (nativeWidth P D H parent e) (original P D H L F C hs parent terminal d e y index)
    (original_fit P D H L F C hs parent terminal d e y index) c z hi
    (IntegralMixedFramedBankTermSign.common_ne_zero P D H (terminal c)) δ).trans
      (congrArg (fun a : ℝ=>SignType.sign ((original P D H L F C hs parent terminal d e y index c).eval₂
        (Int.castRingHom ℝ) (Fin.cons (a+if negative then -δ else δ) z)))
        (IntegralMixedFramedWindowQuery.coordinate P D H L F C hs terminal index c hi z))

theorem mass (hF : ∀ root,1≤F root)
    (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (negative : Bool) (c : List Bool) :
    MvMass.mass ((compiled P D H L F C hs parent terminal d e y index negative).polynomial c)≤
      2^(IntegralMixedFramedCoordinatePackedBits.headMassBound P D H L F C parent e c+
        2*RationalMonomialParameterShift.sourceDegree (endpointFamily P D H L F C hs terminal index)
          (nativeWidth P D H parent e) c*(IntegralMixedFramedBankTermBits.coordinateMass P D H L F C (terminal c)+1)) :=
  RationalMonomialParameterShift.source_mass (endpointFamily P D H L F C hs terminal index) negative
    (nativeWidth P D H parent e)
    (RationalMonomialParameterShift.nativeTargetWidth (endpointFamily P D H L F C hs terminal index) (nativeWidth P D H parent e))
    (original P D H L F C hs parent terminal d e y index)
    (original_fit P D H L F C hs parent terminal d e y index) _ c
    (IntegralMixedFramedTerminalCoordinateHeadBits.coefficient_mass P D H L F C hs hF hf parent terminal d e c (y c))

end LeanCanny.Geometry.IntegralMixedFramedTerminalParameterShift
