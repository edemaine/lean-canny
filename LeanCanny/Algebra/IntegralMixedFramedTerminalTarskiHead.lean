/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateReader
public import LeanCanny.Algebra.IntegralMixedFramedTerminalParameterShift
public import LeanCanny.Algebra.RationalMonomialBivariateShiftSpace
/-! # Actual eta-shifted terminal heads have native bivariate coefficients

No outer-coordinate coefficient is assumed available: it is read from the
actual creating coordinate circuit, embedded in the same terminal raw tuple,
and shifted with that tuple's actual cofactor and common integer.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiHeadBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedCoordinateBivariateBits (nativeWidth)
open IntegralMixedFramedTerminalParameterShiftBits (endpointFamily)
open IntegralMixedFramedTerminalCoordinateHeadBits (polynomial)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d e index : List Bool→ℕ)

noncomputable def head (negative : Bool) :=RationalMonomialBivariateShift.head
  (endpointFamily P D H L F C hs terminal index) negative (nativeWidth P D H parent e)
  (polynomial P D H parent terminal d e)

noncomputable def width :=RationalMonomialParameterShift.nativeTargetWidth
  (endpointFamily P D H L F C hs terminal index) (nativeWidth P D H parent e)

noncomputable def degreeBound (c : List Bool) :=RationalMonomialParameterShift.sourceDegree
  (endpointFamily P D H L F C hs terminal index) (nativeWidth P D H parent e) c*
    ((endpointFamily P D H L F C hs terminal index).weight c+1)

theorem coefficient_degree (negative : Bool) (c : List Bool) (y : ℕ) :
    ((head P D H L F C hs parent terminal d e index negative c).coeff y).totalDegree≤
      degreeBound P D H L F C hs parent terminal e index c :=
  RationalMonomialBivariateShift.coefficient_degree _ negative _ _
    (fun c y=>IntegralMixedFramedTerminalCoordinateHeadBits.source_fit P D H parent terminal d e (fun _=>y) c) c y


theorem width_unary (a : Access P) (hp : parent∈FP) (ht : terminal∈FP) (he : BinaryFn e) (hi : BinaryFn index) :
    UnaryFn (width P D H L F C hs parent terminal e index) :=
  RationalMonomialParameterShift.nativeTargetWidth_unary _ _
    (IntegralMixedFramedWindowQuery.arity_unary P D H L F C hs terminal index a ht)
    (IntegralMixedFramedCoordinateBivariateBits.nativeWidth_unary P a D H parent hp e he)
    (IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal index a ht hi)

theorem degreeBound_binary (a : Access P) (hp : parent∈FP) (ht : terminal∈FP) (he : BinaryFn e) (hi : BinaryFn index) :
    BinaryFn (degreeBound P D H L F C hs parent terminal e index) :=
  (RationalMonomialParameterShift.sourceDegree_binary _ _
    (IntegralMixedFramedWindowQuery.arity_unary P D H L F C hs terminal index a ht)
    (IntegralMixedFramedCoordinateBivariateBits.nativeWidth_unary P a D H parent hp e he)).mul
      ((IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal index a ht hi).add (BinaryFn.const 1))

noncomputable def reader (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) (hi : BinaryFn index)
    (negative : Bool) : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial
      (fun c=>(endpointFamily P D H L F C hs terminal index).arity c+1)
      (width P D H L F C hs parent terminal e index) (head P D H L F C hs parent terminal d e index negative)) :=
  RationalMonomialBivariateShift.reader (endpointFamily P D H L F C hs terminal index) negative
    (nativeWidth P D H parent e) (polynomial P D H parent terminal d e)
    (IntegralMixedFramedTerminalCoordinateReaderBits.reader P D H parent terminal d e a L F C hL hF hC I h hb hp ht hd he)
    (IntegralMixedFramedWindowQuery.arity_unary P D H L F C hs terminal index a ht)
    (IntegralMixedFramedCoordinateBivariateBits.nativeWidth_unary P a D H parent hp e he) hi
    (IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal index a ht hi)
    (IntegralMixedFramedBankScalars.access P a D H Hnew bank hbank hL hF hC hs ht hi)
    (fun c y=>(IntegralMixedFramedTerminalCoordinateHeadBits.coefficient_degree P D H parent terminal d e c y).trans_lt
      (Nat.lt_size_self _))

theorem coefficient_mass (hF : ∀ root,1≤F root)
    (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (negative : Bool) (c : List Bool) (y : ℕ) :
    MvMass.mass ((head P D H L F C hs parent terminal d e index negative c).coeff y)≤
      2^IntegralMixedFramedTerminalParameterShiftBits.massBound P D H L F C hs parent terminal e index c :=
  RationalMonomialBivariateShift.coefficient_mass _ negative _ _
    (fun c y=>IntegralMixedFramedTerminalCoordinateHeadBits.source_fit P D H parent terminal d e (fun _=>y) c) _ c y
    (IntegralMixedFramedTerminalCoordinateHeadBits.coefficient_mass P D H L F C hs hF hf parent terminal d e c y)

end LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiHeadBits
