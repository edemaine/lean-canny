/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedZeroTarskiFamily
public import LeanCanny.Algebra.FixedWidthBivariateZeroLiftSpace
public import LeanCanny.Algebra.FixedWidthBivariateTernaryPower
/-! # Actual original coordinate/window costs supply zero-specialized principals -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedZeroTarskiBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d e selected : List Bool→ℕ)

theorem degree_binary (hd : BinaryFn d) :BinaryFn (degree d):=
  (BinaryFn.ite ((BinaryFn.const 1).le hd) hd (BinaryFn.const 1)).of_eq (fun _=>by simp only [degree,max_def])

theorem wholeBound_binary (a : Access P) (hp : parent∈FP) (ht : terminal∈FP)
    (hd : BinaryFn d) (he : BinaryFn e) (hi : BinaryFn selected) :
    BinaryFn (wholeBound P D H L F C hs parent terminal d e selected) :=by
  have HD:=degree_binary d hd
  have HH:=IntegralMixedFramedCoordinatePackedBits.degreeBound_binary P a D H parent hp e he
  have HQ:=(BinaryFn.const 2).mul ((IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal selected a ht hi).add (BinaryFn.const 1))
  have HR:=MultivariateTarskiDegreeBounds.principalDegreeBound_binary HD (HD.sub (BinaryFn.const 1)) (HD.add (BinaryFn.const 2)) HH HQ
  exact (HH.add HQ).add HR

theorem width_unary (a : Access P) (hp : parent∈FP) (ht : terminal∈FP)
    (hd : BinaryFn d) (he : BinaryFn e) (hi : BinaryFn selected) :
    UnaryFn (width P D H L F C hs parent terminal d e selected) :=
  (UnaryFn.length (wholeBound_binary P D H L F C hs parent terminal d e selected a hp ht hd he hi).bits_mem_FP).of_eq
    (fun _=>BinaryNatCode.length_encode _)

attribute [local irreducible] width

noncomputable def headReader (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) (hi : BinaryFn selected) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>arity P D H terminal c+2)
      (width P D H L F C hs parent terminal d e selected) (head P D H parent terminal d e)) :=by
  let A:=arity P D H terminal
  let U:=IntegralMixedFramedCoordinateBivariateBits.nativeWidth P D H parent e
  let W:=width P D H L F C hs parent terminal d e selected
  let PH:=IntegralMixedFramedTerminalCoordinateHeadBits.polynomial P D H parent terminal d e
  let B:=headBound P D H parent e
  have HA : UnaryFn A:=(IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht
  have HU : UnaryFn U:=IntegralMixedFramedCoordinateBivariateBits.nativeWidth_unary P a D H parent hp e he
  have HW : UnaryFn W:=width_unary P D H L F C hs parent terminal d e selected a hp ht hd he hi
  have Hdegree : ∀c y,((PH c).coeff y).totalDegree≤B c:=IntegralMixedFramedTerminalCoordinateHeadBits.coefficient_degree P D H parent terminal d e
  have HUfit : ∀c,B c<2^U c:=fun _=>Nat.lt_size_self _
  have HWfit (c : List Bool) :B c<2^W c:=by
    have HB :B c≤wholeBound P D H L F C hs parent terminal d e selected c:=by unfold B wholeBound;omega
    apply HB.trans_lt
    dsimp only [W]
    unfold width
    exact Nat.lt_size_self _
  let R0:=IntegralMixedFramedTerminalCoordinateReaderBits.reader P D H parent terminal d e a L F C hL hF hC I h hb hp ht hd he
  let R1:=FixedWidthBivariateZeroLiftBits.reader A U PH R0 HA HU B Hdegree HUfit
  exact FixedWidthBivariateReboxBits.reader (fun c=>A c+2) U W (head P D H parent terminal d e) R1
    (HA.add (UnaryFn.const 2)) HU HW
    (fun c y=>(head_coefficient_degree P D H parent terminal d e c y).trans_lt (HUfit c)) B
    (head_coefficient_degree P D H parent terminal d e) HWfit

noncomputable def queryReader (a : Access P)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) (hi : BinaryFn selected)
    (power : List Bool→Fin 3) (hpower : BinaryFn (fun c=>(power c).val)) (negative : Bool) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>arity P D H terminal c+2)
      (width P D H L F C hs parent terminal d e selected) (query P D H L F C hs terminal selected power negative)) :=by
  let A:=arity P D H terminal
  let W:=width P D H L F C hs parent terminal d e selected
  let QF:=IntegralMixedFramedWindowQuery.family P D H L F C hs terminal selected
  let U:=RationalMonomialWindowQuery.nativeWidth QF
  let PQ:=IntegralMixedFramedWindowQuery.polynomial P D H L F C hs terminal selected negative
  let B:=windowBound P D H L F C hs terminal selected
  have HA : UnaryFn A:=(IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht
  have HU : UnaryFn U:=RationalMonomialWindowQuery.nativeWidth_unary QF
    (IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal selected a ht hi)
  have HW : UnaryFn W:=width_unary P D H L F C hs parent terminal d e selected a hp ht hd he hi
  have Hdegree :∀c y,((PQ c).coeff y).totalDegree≤B c:=IntegralMixedFramedWindowQuery.coefficient_degree P D H L F C hs terminal selected negative
  have HUfit :∀c,B c<2^U c:=fun _=>Nat.lt_size_self _
  have HWfit (c : List Bool) :B c<2^W c:=by
    have HB :B c≤wholeBound P D H L F C hs parent terminal d e selected c:=by unfold B wholeBound queryBound;omega
    apply HB.trans_lt
    dsimp only [W]
    unfold width
    exact Nat.lt_size_self _
  let R0:=IntegralMixedFramedWindowQuery.nativeReader P D H L F C hs terminal selected a Hnew bank hbank hL hF hC ht hi negative
  let R1:=FixedWidthBivariateZeroLiftBits.epsilonReader A U PQ R0 HA HU B Hdegree HUfit
  have HQ (c : List Bool) (y : ℕ) :((baseQuery P D H L F C hs terminal selected negative c).coeff y).totalDegree≤B c:=
    (FixedWidthBivariateZeroLiftBits.epsilon_degree _ _ c y).trans (Hdegree c y)
  let R2:=FixedWidthBivariateReboxBits.reader (fun c=>A c+2) U W (baseQuery P D H L F C hs terminal selected negative) R1
    (HA.add (UnaryFn.const 2)) HU HW (fun c y=>(HQ c y).trans_lt (HUfit c)) B HQ HWfit
  exact FixedWidthBivariateTernaryPowerBits.reader (fun c=>A c+2) W (baseQuery P D H L F C hs terminal selected negative) R2 power hpower

noncomputable def access (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) (hi : BinaryFn selected)
    (power : List Bool→Fin 3) (hpower : BinaryFn (fun c=>(power c).val)) (negative : Bool) :
    FixedWidthTarskiPrincipalBits.Access (family P D H L F C hs parent terminal d e selected power negative) :=by
  have HD:=degree_binary d hd
  exact {head:=headReader P D H L F C hs parent terminal d e selected a hL hF hC I h hb hp ht hd he hi
         query:=queryReader P D H L F C hs parent terminal d e selected a Hnew bank hbank hL hF hC hp ht hd he hi power hpower negative
         degree:=HD
         bound:=HD.add (BinaryFn.const 2)
         seedDegree:=HD.sub (BinaryFn.const 1)}

end LeanCanny.Algebra.IntegralMixedFramedZeroTarskiBits
