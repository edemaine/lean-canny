/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateSource
public import LeanCanny.Algebra.FixedWidthBivariateReboxSpace
/-! # The actual terminal coordinate head has a charged bivariate reader -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateReaderBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCoordinateBivariateBits (nativeWidth)
open IntegralMixedFramedCoordinatePackedBits (degreeBound)
open IntegralMixedFramedBankSnapshotBits (atKey)
open IntegralMixedFramedTerminalCoordinateHeadBits (polynomial)
open FixedWidthBivariateReboxBits (target outer)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (parent terminal : List Bool→List Bool) (d e : List Bool→ℕ)

noncomputable def coefficientWord :=FixedWidthBivariateReboxBits.coefficient
  (fun c=>(atKey P D H (terminal c)).count+1) (nativeWidth P D H parent e)
  (polynomial P D H parent terminal d e)

theorem coefficient_evaluator (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) :
    SpaceFunction (coefficientWord P D H parent terminal d e) :=by
  have HO:=FixedWidthBivariateReader.origin_FP
  have HY : BinaryFn outer:=BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have E:=IntegralMixedFramedTerminalCoordinateHeadBits.coefficient_evaluator P a D H L F C hL hF hC I h hb
    (parent ∘ FixedWidthBivariateReader.origin) (terminal ∘ FixedWidthBivariateReader.origin)
    (mem_FP_comp HO hp) (mem_FP_comp HO ht) (d ∘ FixedWidthBivariateReader.origin) (e ∘ FixedWidthBivariateReader.origin)
    outer (hd.comp HO) (he.comp HO) HY target FixedWidthBivariateReboxBits.modulus (by polytime [target]) (by polytime [FixedWidthBivariateReboxBits.modulus])
  refine E.congr (funext fun z=>?_)
  have HE:=IntegralMixedFramedTerminalCoordinateHeadBits.polynomial_comp P D H parent terminal d e FixedWidthBivariateReader.origin z
  exact congrArg (fun p : Polynomial (MvPolynomial (Fin ((atKey P D H (terminal (FixedWidthBivariateReader.origin z))).count+1)) ℤ)=>
    residueBits ((((p.coeff (outer z)).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _)
      (nativeWidth P D H parent e (FixedWidthBivariateReader.origin z)) (Nat.fromBitsLE (target z)))) : ℤ) :
        ZMod (Nat.fromBitsLE (FixedWidthBivariateReboxBits.modulus z)+1))) HE

noncomputable def reader (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial
      (fun c=>(atKey P D H (terminal c)).count+1) (nativeWidth P D H parent e)
      (polynomial P D H parent terminal d e)) :=
  FixedWidthBivariateReader.reader _ _ _ (coefficientWord P D H parent terminal d e)
    (coefficient_evaluator P D H parent terminal d e a L F C hL hF hC I h hb hp ht hd he)
    (((IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht).add (UnaryFn.const 1))
    (IntegralMixedFramedCoordinateBivariateBits.nativeWidth_unary P a D H parent hp e he)
    (degreeBound P D H parent e)
    (IntegralMixedFramedTerminalCoordinateHeadBits.coefficient_degree P D H parent terminal d e)
    (fun _=>Nat.lt_size_self _) (FixedWidthBivariateReboxBits.coefficient_packet _ _ _)

end LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateReaderBits
