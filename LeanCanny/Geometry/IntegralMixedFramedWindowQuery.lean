/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedWindowQuery
public import LeanCanny.Algebra.RationalMonomialWindowEvaluation
public import LeanCanny.Geometry.IntegralMixedFramedBankTermSign
/-! # A native window tests the literal actual retained-bank coordinate

All coordinates are read from the same raw tuple. No separate root-lifting
or selected-hom premise is needed for the polynomial identity.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedWindowQuery
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open Algebra.IntegralMixedFramedWindowQuery (family polynomial)
open scoped Classical

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (index : List Bool→ℕ)

theorem weight (q : List Bool) (hi : index q<(atKey P D H (key q)).count) :
    (family P D H L F C hs key index).weight q=
      UniformIntegralPowerSchedule.weights (P.cap (pairFst (key q))+1) (2^P.width (pairFst (key q)))
        (atKey P D H (key q)).count ⟨index q,hi⟩ :=by
  unfold family Algebra.IntegralMixedFramedWindowQuery.weightPacket IntegralMixedFramedBankCoordinateBits.weight
    UniformIntegralPowerSchedule.power UniformIntegralPowerSchedule.age UniformIntegralPowerSchedule.weights
  simp only [IntegralMixedFramedBankSnapshotBits.packet,IntegralMixedFramedBankCoordinateBits.horizon,
    IntegralMixedFramedBankCoordinateBits.scalarDegree,IntegralMixedFramedBankDenominatorBits.count,
    IntegralMixedFramedCompanionQueryBits.root,PaddedIntegralGeneratorSource.base,PaddedIntegralGeneratorSource.row,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  change UniformIntegralPowerSchedule.birth _ _
      ((atKey P D H (key q)).count-1-min (index q) (atKey P D H (key q)).count)=_
  rw [min_eq_left hi.le]

theorem coordinate (q : List Bool) (hi : index q<(atKey P D H (key q)).count)
    (z : Fin (atKey P D H (key q)).count→ℝ) :
    ((family P D H L F C hs key index).scalars.numerator q:ℝ)*
        z ⟨index q,hi⟩^(family P D H L F C hs key index).weight q/
      ((family P D H L F C hs key index).scalars.denominator q:ℝ)=
        IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (key q)) z ⟨index q,hi⟩ :=by
  rw [weight P D H L F C hs key index q hi]
  change (((atKey P D H (key q)).cofactor (index q):ℝ)*
      z ⟨index q,hi⟩^UniformIntegralPowerSchedule.weights (P.cap (pairFst (key q))+1)
        (2^P.width (pairFst (key q))) (atKey P D H (key q)).count ⟨index q,hi⟩)/
      ((atKey P D H (key q)).common:ℝ)=
    z ⟨index q,hi⟩^UniformIntegralPowerSchedule.weights (P.cap (pairFst (key q))+1)
      (2^P.width (pairFst (key q))) (atKey P D H (key q)).count ⟨index q,hi⟩/
      ((atKey P D H (key q)).denominator ⟨index q,hi⟩:ℝ)
  apply (div_eq_div_iff
    (Int.cast_ne_zero.mpr (IntegralMixedFramedBankTermSign.common_ne_zero P D H (key q)))
    (IntegralMixedCanonicalBankPoint.denominator_ne_zero _ _)).mpr
  change (((atKey P D H (key q)).cofactor (index q):ℝ)*_)*
      ((atKey P D H (key q)).denominator ⟨index q,hi⟩:ℝ)=_
  rw [IntegralMixedFramedBankTermSign.snapshot_split (atKey P D H (key q)) ⟨index q,hi⟩,Int.cast_mul]
  ring

theorem sign (negative : Bool) (q : List Bool) (hi : index q<(atKey P D H (key q)).count)
    (z : Fin (atKey P D H (key q)).count→ℝ) (ε u : ℝ) :
    SignType.sign ((polynomial P D H L F C hs key index negative q).eval₂
      (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons ε z)) u)=
      SignType.sign (u-IntegralMixedCanonicalBankPoint.point
        (IntegralMixedFramedBankTermSign.state P D H (key q)) z ⟨index q,hi⟩+
          if negative then -ε else ε) :=by
  exact (RationalMonomialWindowQuery.sign_query (family P D H L F C hs key index) negative q z hi
    (IntegralMixedFramedBankTermSign.common_ne_zero P D H (key q)) ε u).trans
      (congrArg (fun a : ℝ=>SignType.sign (u-a+if negative then -ε else ε))
        (coordinate P D H L F C hs key index q hi z))

end LeanCanny.Geometry.IntegralMixedFramedWindowQuery
