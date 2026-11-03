/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedMidpoint
public import LeanCanny.Geometry.IntegralMixedFramedWindowQuery
/-! # The sparse midpoint is evaluated at the same actual bank point -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedMidpoint
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open Algebra.IntegralMixedFramedMidpoint (family)
open scoped Classical

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (left right : List Bool→ℕ)

theorem midpoint (q : List Bool) (hl : left q<(atKey P D H (key q)).count)
    (hr : right q<(atKey P D H (key q)).count) (z : Fin (atKey P D H (key q)).count→ℝ) :
    (RationalMonomialMidpoint.numerator (family P D H L F C hs key left right) q).eval₂ (Int.castRingHom ℝ) z/
      (RationalMonomialMidpoint.denominator (family P D H L F C hs key left right) q:ℝ)=
      (IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (key q)) z ⟨left q,hl⟩+
        IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (key q)) z ⟨right q,hr⟩)/2 :=by
  exact (RationalMonomialMidpoint.midpoint (family P D H L F C hs key left right) q z hl hr).trans
    (congrArg₂ (fun x y : ℝ=>(x+y)/2)
      (IntegralMixedFramedWindowQuery.coordinate P D H L F C hs key left q hl z)
      (IntegralMixedFramedWindowQuery.coordinate P D H L F C hs key right q hr z))

end LeanCanny.Geometry.IntegralMixedFramedMidpoint
