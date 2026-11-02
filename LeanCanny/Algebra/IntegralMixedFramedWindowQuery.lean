/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RationalMonomialWindowReader
public import LeanCanny.Algebra.IntegralMixedFramedBankScalars
/-! # Window queries use actual saved-bank cofactors and current common integer -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedWindowQuery
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey packet)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (index : List Bool→ℕ)

def weightPacket (q : List Bool) :=packet (key q) [] (index q) 0

theorem weightPacket_FP (hk : key∈FP) (hi : BinaryFn index) : weightPacket key index∈FP :=
  mem_FP_pair (mem_FP_pair hk (constFn_mem_FP [])) (mem_FP_pair hi.bits_mem_FP (constFn_mem_FP (BinaryNatCode.encode 0)))

noncomputable def family : RationalMonomialWindowQuery.Family where
  arity q:=(atKey P D H (key q)).count
  index:=index
  weight q:=IntegralMixedFramedBankCoordinateBits.weight P D H (weightPacket key index q)
  scalars:=IntegralMixedFramedBankScalars.scalars P D H L F C hs key index

theorem arity_unary (a : Access P) (hk : key∈FP) : UnaryFn (family P D H L F C hs key index).arity :=
  (IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp hk

theorem weight_binary (a : Access P) (hk : key∈FP) (hi : BinaryFn index) :
    BinaryFn (family P D H L F C hs key index).weight :=
  (IntegralMixedFramedBankCoordinateBits.weight_binary P a D H).comp (weightPacket_FP key index hk hi)

noncomputable def polynomial (negative : Bool) :=
  RationalMonomialWindowQuery.query (family P D H L F C hs key index) negative

noncomputable def nativeReader (a : Access P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hk : key∈FP) (hi : BinaryFn index) (negative : Bool) :
    CertifiedPolynomial.BivariateReader
      (FixedWidthBivariateReader.polynomial (fun q=>(atKey P D H (key q)).count+1)
        (RationalMonomialWindowQuery.nativeWidth (family P D H L F C hs key index))
        (polynomial P D H L F C hs key index negative)) :=
  RationalMonomialWindowQuery.nativeReader (family P D H L F C hs key index) negative
    (arity_unary P D H L F C hs key index a hk) hi (weight_binary P D H L F C hs key index a hk hi)
    (IntegralMixedFramedBankScalars.access P a D H Hnew c hb hL hF hC hs hk hi)

theorem coefficient_degree (negative : Bool) (q : List Bool) (y : ℕ) :
    ((polynomial P D H L F C hs key index negative q).coeff y).totalDegree≤
      (family P D H L F C hs key index).weight q+1 :=
  RationalMonomialWindowQuery.coefficient_degree _ negative q y

theorem coefficient_mass (negative : Bool) (q : List Bool) (y : ℕ) :
    MvMass.mass ((polynomial P D H L F C hs key index negative q).coeff y)≤
      2^(2*IntegralMixedFramedBankTermBits.coordinateMass P D H L F C (key q)+1) :=
  RationalMonomialWindowQuery.coefficient_mass _ negative q y

end LeanCanny.Algebra.IntegralMixedFramedWindowQuery
