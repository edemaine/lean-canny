/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthBivariateParameterSuffixSpace
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateBivariateNative
public import LeanCanny.Algebra.IntegralMixedFramedBankSnapshot
/-! # Actual coordinate heads embed in a later raw bank with the parameter fixed

All coefficients come from the current-Q original coordinate reader. The
prefix-count check identifies this formal enlarged layout with the actual
terminal arity; old hom/row interpretation remains the literal suffix.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateParameterSuffixBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCoordinateCoefficientSpaceBits (arity)
open IntegralMixedFramedCoordinatePackedBits (guardedHead degreeBound)
open IntegralMixedFramedCoordinateBivariateBits (nativeWidth)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def newer (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (c : List Bool) :=
  (atKey P D H (terminal c)).count-arity P D H parent c

theorem arity_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (hp : parent∈FP) : UnaryFn (arity P D H parent) :=
  (IntegralMixedFramedAllCoordinateSourceBits.arity_unary P a D H).comp hp

theorem newer_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (hp : parent∈FP) (ht : terminal∈FP) : UnaryFn (newer P D H parent terminal) :=
  ((IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht).sub (arity_unary P a D H parent hp)

noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e : List Bool→ℕ) :=
  FixedWidthBivariateParameterSuffixBits.head (newer P D H parent terminal) (arity P D H parent)
    (guardedHead P D H parent d e)

theorem arity_eq_terminal (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (c : List Bool)
    (h : arity P D H parent c≤(atKey P D H (terminal c)).count) :
    newer P D H parent terminal c+(arity P D H parent c+1)=(atKey P D H (terminal c)).count+1 :=by
  unfold newer
  omega

theorem coefficient_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent terminal : List Bool→List Bool) (hp : parent∈FP) (ht : terminal∈FP)
    (d e y : List Bool→ℕ) (hd : BinaryFn d) (he : BinaryFn e) (hy : BinaryFn y)
    (target modulus : List Bool→List Bool) (hT : target∈FP) (hM : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>newer P D H parent terminal c+(arity P D H parent c+1))
      (nativeWidth P D H parent e) (fun c=>(polynomial P D H parent terminal d e c).coeff (y c)) target modulus) :=by
  let R:=IntegralMixedFramedCoordinateBivariateBits.nativeReader P a D H L F C hL hF hC I h hb parent hp d e hd he
  have hW:=IntegralMixedFramedCoordinateBivariateBits.nativeWidth_unary P a D H parent hp e he
  have HF (c : List Bool) (v : ℕ) : ((guardedHead P D H parent d e c).coeff v).totalDegree<
      2^nativeWidth P D H parent e c :=
    (IntegralMixedFramedCoordinatePackedBits.guardedHead_degree P D H parent d e c v).trans_lt (Nat.lt_size_self _)
  have E:=FixedWidthBivariateParameterSuffixBits.evaluator (arity P D H parent) (nativeWidth P D H parent e)
    (guardedHead P D H parent d e) R (arity_unary P a D H parent hp) hW HF
    id id_mem_FP (newer P D H parent terminal) y (newer_unary P a D H parent terminal hp ht) hy target modulus hT hM
  refine E.congr (funext fun c=>?_)
  simp only [FixedWidthRowBits.value,polynomial,FixedWidthBivariateParameterSuffixBits.coefficient,id_eq]
  rfl

theorem coefficient_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e : List Bool→ℕ) (c : List Bool) (y : ℕ) :
    ((polynomial P D H parent terminal d e c).coeff y).totalDegree≤degreeBound P D H parent e c :=
  (FixedWidthBivariateParameterSuffixBits.degree _ _ _ c y).trans
    (IntegralMixedFramedCoordinatePackedBits.guardedHead_degree P D H parent d e c y)

end LeanCanny.Algebra.IntegralMixedFramedCoordinateParameterSuffixBits
