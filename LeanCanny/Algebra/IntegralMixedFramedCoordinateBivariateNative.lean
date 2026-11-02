/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateBivariate
/-! # A native original-source width for the actual coordinate test reader -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateBivariateBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCoordinatePackedBits (degreeBound)

noncomputable def nativeWidth (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (e : List Bool→ℕ) (q : List Bool) :=
  (degreeBound P D H parent e q).size

theorem nativeWidth_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (hp : parent∈FP) (e : List Bool→ℕ) (he : BinaryFn e) :
    UnaryFn (nativeWidth P D H parent e) :=
  (UnaryFn.length (IntegralMixedFramedCoordinatePackedBits.degreeBound_binary P a D H parent hp e he).bits_mem_FP).of_eq
    (fun _=>BinaryNatCode.length_encode _)

noncomputable def nativeReader (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent : List Bool→List Bool) (hp : parent∈FP) (d e : List Bool→ℕ)
    (hd : BinaryFn d) (he : BinaryFn e) :
    CertifiedPolynomial.BivariateReader (polynomial P D H parent d e (nativeWidth P D H parent e)) :=
  reader P a D H L F C hL hF hC I h hb parent hp d e (nativeWidth P D H parent e) hd he
    (nativeWidth_unary P a D H parent hp e he) (fun _=>Nat.lt_size_self _)

end LeanCanny.Algebra.IntegralMixedFramedCoordinateBivariateBits
