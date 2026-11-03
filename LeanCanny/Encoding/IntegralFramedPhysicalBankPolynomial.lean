/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSquarePoint
public import LeanCanny.Algebra.IntegralMixedBankCoordinatePolynomial
/-! # The actual bank annihilator vanishes at the same full joint point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] family point IntegralMixedBankCoordinatePolynomial.polynomial
theorem bank_polynomial_root (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w)
    (i : Fin ((family P D H).birth (key c))) :
    (IntegralMixedBankCoordinatePolynomial.polynomial ((family P D H).state (key c)) i).eval₂ (Int.castRingHom ℝ)
      (point P D H L F C hs key hpos c w hv i)=0 :=by
  obtain ⟨φ,_,Hφ⟩:=exists_interpretation P D H L F C hs key hpos c w hv
  have HE:=congrArg (fun v : ℝ=>(IntegralMixedBankCoordinatePolynomial.polynomial ((family P D H).state (key c)) i).eval₂
    (Int.castRingHom ℝ) v) (Hφ i)
  exact HE.symm.trans (IntegralMixedBankCoordinatePolynomial.quotient_root ((family P D H).state (key c)) φ i)
end LeanCanny.Encoding.IntegralFramedPhysicalSquare
