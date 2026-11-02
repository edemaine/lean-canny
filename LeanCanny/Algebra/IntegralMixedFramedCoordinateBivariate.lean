/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedBounds
public import LeanCanny.Algebra.FixedWidthBivariateReader
/-! # Actual saved-coordinate equations enter the native bivariate kernels

The only coefficient cost is the actual current-Q coordinate controller.
All weighted old joint variables and E are Kronecker packed, retaining Y.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateBivariateBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCoordinatePackedBits (guardedHead degreeBound)
open FixedWidthBivariateReader (origin)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e W : List Bool→ℕ) :=
  IntegralMixedFramedCoordinatePackedBits.value P D H (parent∘origin) (d∘origin) (e∘origin)
    (fun z=>Nat.fromBitsLE (pairSnd (pairSnd z))) (W∘origin)
    (fun z=>pairFst (pairSnd z)) (fun z=>pairSnd (pairFst z))

private noncomputable def entryAt (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (d e W y u : ℕ) (mw : List Bool) : List Bool :=
  residueBits (((((IntegralMixedFramedCoordinatePackedBits.head P D H (fun _=>c) (fun _=>d) (fun _=>e) []).coeff y).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) W u)) : ℤ) : ZMod (Nat.fromBitsLE mw+1))

private theorem value_entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e y W : List Bool→ℕ) (target modulus : List Bool→List Bool) (q : List Bool) :
    IntegralMixedFramedCoordinatePackedBits.value P D H parent d e y W target modulus q=
      if IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q then
        entryAt P D H (parent q) (d q) (e q) (W q) (y q) (Nat.fromBitsLE (target q)) (modulus q) else [] :=rfl

private theorem guarded_entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e : List Bool→ℕ) (q : List Bool) (W y u : ℕ) (mw : List Bool) :
    residueBits (((((guardedHead P D H parent d e q).coeff y).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) W u)) : ℤ) : ZMod (Nat.fromBitsLE mw+1))=
      if IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q then
        entryAt P D H (parent q) (d q) (e q) W y u mw else [] :=by
  by_cases hc : IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P parent q
  · rw [guardedHead,ite_eq_left hc,ite_eq_left hc]
    rfl
  · rw [guardedHead,ite_eq_right hc,ite_eq_right hc]
    change residueBits (0 : ZMod (Nat.fromBitsLE mw+1))=[]
    simp only [residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

attribute [local irreducible] entryAt

theorem coefficient_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e W : List Bool→ℕ) (q : List Bool) (u v : ℕ) :
    coefficient P D H parent d e W (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))=
      residueBits (((((guardedHead P D H parent d e (pairFst q)).coeff v).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W (pairFst q)) u)) : ℤ) :
          ZMod (Nat.fromBitsLE (pairSnd q)+1)) := by
  rw [coefficient,value_entry,guarded_entry]
  simp only [IntegralMixedFramedCoordinateCoefficientSpaceBits.Core,Function.comp_apply,origin,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  split_ifs with hc <;> simp [hc]

theorem coefficient_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent : List Bool→List Bool) (hp : parent∈FP) (d e W : List Bool→ℕ)
    (hd : BinaryFn d) (he : BinaryFn e) (hW : UnaryFn W) :
    SpaceFunction (coefficient P D H parent d e W) :=
  IntegralMixedFramedCoordinatePackedBits.evaluator P a D H L F C hL hF hC I h hb
    (parent∘origin) (mem_FP_comp FixedWidthBivariateReader.origin_FP hp) (d∘origin) (e∘origin)
    (fun z=>Nat.fromBitsLE (pairSnd (pairSnd z))) (W∘origin)
    (hd.comp FixedWidthBivariateReader.origin_FP) (he.comp FixedWidthBivariateReader.origin_FP)
    (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) (hW.comp FixedWidthBivariateReader.origin_FP)
    (fun z=>pairFst (pairSnd z)) (fun z=>pairSnd (pairFst z))
    (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e W : List Bool→ℕ) (c : List Bool) : (ℤ[X])[X] :=
  (guardedHead P D H parent d e c).map (FixedWidthKronecker.encode
    (IntegralMixedFramedCoordinateCoefficientSpaceBits.arity P D H parent c+1) (W c))

noncomputable def reader (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent : List Bool→List Bool) (hp : parent∈FP) (d e W : List Bool→ℕ)
    (hd : BinaryFn d) (he : BinaryFn e) (hW : UnaryFn W)
    (hfit : ∀ c,degreeBound P D H parent e c<2^W c) :
    CertifiedPolynomial.BivariateReader (polynomial P D H parent d e W) :=
  FixedWidthBivariateReader.reader
    (fun c=>IntegralMixedFramedCoordinateCoefficientSpaceBits.arity P D H parent c+1) W
    (guardedHead P D H parent d e) (coefficient P D H parent d e W)
    (coefficient_evaluator P a D H L F C hL hF hC I h hb parent hp d e W hd he hW)
    (IntegralMixedFramedCoordinatePackedBits.arity_unary P a D H parent hp) hW
    (degreeBound P D H parent e) (IntegralMixedFramedCoordinatePackedBits.guardedHead_degree P D H parent d e) hfit
    (coefficient_packet P D H parent d e W)

end LeanCanny.Algebra.IntegralMixedFramedCoordinateBivariateBits
