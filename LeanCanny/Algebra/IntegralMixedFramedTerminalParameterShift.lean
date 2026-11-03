/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateSource
public import LeanCanny.Algebra.IntegralMixedFramedWindowQuery
public import LeanCanny.Algebra.RationalMonomialParameterShiftNative
/-! # Actual saved coordinate coefficients at a same-terminal rational endpoint

Both the creating coordinate source and endpoint scalars are derived from
original current-Q arithmetic. A native prefix guard handles malformed
counts. Weighted integer representatives remain test polynomials only.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedTerminalParameterShiftBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedCoordinateBivariateBits (nativeWidth)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d e y : List Bool→ℕ) (index : List Bool→ℕ)

noncomputable def endpointFamily :=IntegralMixedFramedWindowQuery.family P D H L F C hs terminal index

noncomputable def original (c : List Bool) :
    MvPolynomial (Fin ((endpointFamily P D H L F C hs terminal index).arity c+1)) ℤ :=
  (IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e c).coeff (y c)

theorem original_fit (c : List Bool) (i : Fin ((endpointFamily P D H L F C hs terminal index).arity c+1)) :
    (original P D H L F C hs parent terminal d e y index c).degreeOf i<2^nativeWidth P D H parent e c :=
  IntegralMixedFramedTerminalCoordinateHeadBits.source_fit P D H parent terminal d e y c i

noncomputable def compiled (negative : Bool) :=
  RationalMonomialParameterShift.nativeFamily (endpointFamily P D H L F C hs terminal index) negative
    (nativeWidth P D H parent e) (original P D H L F C hs parent terminal d e y index)
    (original_fit P D H L F C hs parent terminal d e y index)

theorem source_packet (negative : Bool) (c : List Bool) (r m : ℕ) (hm : 0<m) :
    IntegralMixedFramedTerminalCoordinateHeadBits.sourceValue P D H parent terminal d e y
      (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m-1)))=
        residueBits (((compiled P D H L F C hs parent terminal d e y index negative).univariate.coefficient c r : ℤ) : ZMod m) :=by
  rw [IntegralMixedFramedTerminalCoordinateHeadBits.source_packet P D H parent terminal d e y c r m hm]
  apply congrArg (fun a : ℤ=>residueBits (a : ZMod m))
  rw [nativeExponent_refl]
  rfl

theorem evaluator (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) (hy : BinaryFn y) (hi : BinaryFn index)
    (negative : Bool) (target modulus : List Bool→List Bool) (hT : target∈FP) (hM : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>(atKey P D H (terminal c)).count+1)
      (RationalMonomialParameterShift.nativeTargetWidth (endpointFamily P D H L F C hs terminal index) (nativeWidth P D H parent e))
      (compiled P D H L F C hs parent terminal d e y index negative).polynomial target modulus) :=by
  have ES:=IntegralMixedFramedTerminalCoordinateHeadBits.source_evaluator P a D H L F C hL hF hC I h hb
    parent terminal hp ht d e y hd he hy
  have hA:=IntegralMixedFramedWindowQuery.arity_unary P D H L F C hs terminal index a ht
  have hW:=IntegralMixedFramedCoordinateBivariateBits.nativeWidth_unary P a D H parent hp e he
  have hw:=IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal index a ht hi
  have hS:=IntegralMixedFramedBankScalars.access P a D H Hnew bank hbank hL hF hC hs ht hi
  exact RationalMonomialParameterShift.evaluator (endpointFamily P D H L F C hs terminal index) negative
    (nativeWidth P D H parent e) (original P D H L F C hs parent terminal d e y index)
    (original_fit P D H L F C hs parent terminal d e y index) hA hW hi hw hS
    (IntegralMixedFramedTerminalCoordinateHeadBits.sourceValue P D H parent terminal d e y) ES
    (fun c r _ m hm=>source_packet P D H L F C hs parent terminal d e y index negative c r m hm) target modulus hT hM

noncomputable def massBound (c : List Bool) :=
  IntegralMixedFramedCoordinatePackedBits.headMassBound P D H L F C parent e c+
    2*RationalMonomialParameterShift.sourceDegree (endpointFamily P D H L F C hs terminal index)
      (nativeWidth P D H parent e) c*(IntegralMixedFramedBankTermBits.coordinateMass P D H L F C (terminal c)+1)

theorem massBound_binary (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (hp : parent∈FP) (ht : terminal∈FP) (he : BinaryFn e) :
    BinaryFn (massBound P D H L F C hs parent terminal e index) :=by
  have HA:=IntegralMixedFramedWindowQuery.arity_unary P D H L F C hs terminal index a ht
  have HW:=IntegralMixedFramedCoordinateBivariateBits.nativeWidth_unary P a D H parent hp e he
  have HD:=RationalMonomialParameterShift.sourceDegree_binary (endpointFamily P D H L F C hs terminal index)
    (nativeWidth P D H parent e) HA HW
  have HM : BinaryFn (fun c=>IntegralMixedFramedBankTermBits.coordinateMass P D H L F C (terminal c)) :=
    (IntegralMixedFramedBankTermBits.coordinateMass_binary P a D H hL hF hC).comp ht
  exact (IntegralMixedFramedCoordinatePackedBits.headMassBound_binary P a D H L F C hL hF hC I parent hp e he).add
    (((BinaryFn.const 2).mul HD).mul (HM.add (BinaryFn.const 1)))

end LeanCanny.Algebra.IntegralMixedFramedTerminalParameterShiftBits
