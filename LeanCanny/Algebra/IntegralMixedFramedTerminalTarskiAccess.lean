/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiFamily
public import LeanCanny.Algebra.FixedWidthBivariateTernaryPower
/-! # Original current-Q arithmetic supplies the actual two-parameter principals -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiFamilyBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d e center selected : List Bool→ℕ)

theorem degree_binary (hd : BinaryFn d) : BinaryFn (degree d) :=
  (BinaryFn.ite ((BinaryFn.const 1).le hd) hd (BinaryFn.const 1)).of_eq (fun _=>by simp only [degree,max_def])

theorem width_unary (a : Access P) (hp : parent∈FP) (ht : terminal∈FP)
    (hd : BinaryFn d) (he : BinaryFn e) (hc : BinaryFn center) (hi : BinaryFn selected) :
    UnaryFn (width P D H L F C hs parent terminal d e center selected) :=by
  have HD:=degree_binary d hd
  have HP:=IntegralMixedFramedTerminalTarskiHeadBits.degreeBound_binary P D H L F C hs parent terminal e center a hp ht he hc
  have HQ : BinaryFn (queryBound P D H L F C hs terminal selected):=(BinaryFn.const 2).mul
    ((IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal selected a ht hi).add (BinaryFn.const 1))
  have HR:=MultivariateTarskiDegreeBounds.principalDegreeBound_binary HD (HD.sub (BinaryFn.const 1))
    (HD.add (BinaryFn.const 2)) HP HQ
  have HW : BinaryFn (wholeBound P D H L F C hs parent terminal d e center selected):=(HP.add HQ).add HR
  exact (UnaryFn.length HW.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)

attribute [local irreducible] width

noncomputable def headReader (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) (hc : BinaryFn center) (hi : BinaryFn selected)
    (negativeEta : Bool) : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial
      (fun c=>1+(arity P D H terminal c+1)) (width P D H L F C hs parent terminal d e center selected)
      (head P D H L F C hs parent terminal d e center negativeEta)) :=by
  let A:=arity P D H terminal
  let W:=width P D H L F C hs parent terminal d e center selected
  let PH:=IntegralMixedFramedTerminalTarskiHeadBits.head P D H L F C hs parent terminal d e center negativeEta
  let HP:=headBound P D H L F C hs parent terminal e center
  have HA : UnaryFn A:=(IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht
  have HW : UnaryFn W:=width_unary P D H L F C hs parent terminal d e center selected a hp ht hd he hc hi
  have HH : ∀ c y,((PH c).coeff y).totalDegree≤HP c:=
    IntegralMixedFramedTerminalTarskiHeadBits.coefficient_degree P D H L F C hs parent terminal d e center negativeEta
  have HFH (c : List Bool) : HP c<2^W c :=by
    have HL : HP c≤wholeBound P D H L F C hs parent terminal d e center selected c:=by
      unfold HP wholeBound
      omega
    unfold W
    unfold IntegralMixedFramedTerminalTarskiFamilyBits.width
    have HT : wholeBound P D H L F C hs parent terminal d e center selected c<
        2^(wholeBound P D H L F C hs parent terminal d e center selected c).size:=
      Nat.lt_size_self (wholeBound P D H L F C hs parent terminal d e center selected c)
    exact Nat.lt_of_le_of_lt HL HT
  let RH0:=IntegralMixedFramedTerminalTarskiHeadBits.reader P D H L F C hs parent terminal d e center a
    hL hF hC I h hb Hnew bank hbank hp ht hd he hc negativeEta
  let UH:=IntegralMixedFramedTerminalTarskiHeadBits.width P D H L F C hs parent terminal e center
  have UHnative : UnaryFn UH:=IntegralMixedFramedTerminalTarskiHeadBits.width_unary P D H L F C hs parent terminal e center a hp ht he hc
  have HFH0 (c : List Bool) : HP c<2^UH c:=RationalMonomialParameterShift.target_fit
    (IntegralMixedFramedTerminalParameterShiftBits.endpointFamily P D H L F C hs terminal center)
    (IntegralMixedFramedCoordinateBivariateBits.nativeWidth P D H parent e) c
  let RH1:=FixedWidthBivariateReboxBits.reader (fun c=>A c+1) UH W PH RH0 (HA.add (UnaryFn.const 1))
    UHnative HW (fun c y=>(HH c y).trans_lt (HFH0 c)) HP HH HFH
  exact FixedWidthBivariateParameterPairBits.reader true A W PH RH1 HA HW HP HH HFH

noncomputable def queryReader (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) (hc : BinaryFn center) (hi : BinaryFn selected)
    (power : List Bool→Fin 3) (hpower : BinaryFn (fun c=>(power c).val)) (negativeEpsilon : Bool) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial
      (fun c=>1+(arity P D H terminal c+1)) (width P D H L F C hs parent terminal d e center selected)
      (query P D H L F C hs terminal selected power negativeEpsilon)) :=by
  let A:=arity P D H terminal
  let W:=width P D H L F C hs parent terminal d e center selected
  let PQ:=IntegralMixedFramedWindowQuery.polynomial P D H L F C hs terminal selected negativeEpsilon
  let QP:=windowBound P D H L F C hs terminal selected
  have HA : UnaryFn A:=(IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht
  have HW : UnaryFn W:=width_unary P D H L F C hs parent terminal d e center selected a hp ht hd he hc hi
  have HQ : ∀ c y,((PQ c).coeff y).totalDegree≤QP c:=
    IntegralMixedFramedWindowQuery.coefficient_degree P D H L F C hs terminal selected negativeEpsilon
  have HFQ (c : List Bool) : QP c<2^W c :=by
    have HL : QP c≤wholeBound P D H L F C hs parent terminal d e center selected c:=by
      unfold QP wholeBound queryBound
      omega
    unfold W
    unfold IntegralMixedFramedTerminalTarskiFamilyBits.width
    have HT : wholeBound P D H L F C hs parent terminal d e center selected c<
        2^(wholeBound P D H L F C hs parent terminal d e center selected c).size:=
      Nat.lt_size_self (wholeBound P D H L F C hs parent terminal d e center selected c)
    exact Nat.lt_of_le_of_lt HL HT
  let QF:=IntegralMixedFramedWindowQuery.family P D H L F C hs terminal selected
  let UQ:=RationalMonomialWindowQuery.nativeWidth QF
  have UQnative : UnaryFn UQ:=RationalMonomialWindowQuery.nativeWidth_unary QF
    (IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal selected a ht hi)
  let RQ0:=IntegralMixedFramedWindowQuery.nativeReader P D H L F C hs terminal selected a Hnew bank hbank hL hF hC ht hi negativeEpsilon
  let RQ1:=FixedWidthBivariateReboxBits.reader (fun c=>A c+1) UQ W PQ RQ0 (HA.add (UnaryFn.const 1))
    UQnative HW (fun c y=>(HQ c y).trans_lt (Nat.lt_size_self _)) QP HQ HFQ
  let RQ:=FixedWidthBivariateParameterPairBits.reader false A W PQ RQ1 HA HW QP HQ HFQ
  let RP:=FixedWidthBivariateTernaryPowerBits.reader (fun c=>1+(A c+1)) W
    (baseQuery P D H L F C hs terminal selected negativeEpsilon) RQ power hpower
  exact RP

noncomputable def access (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (IntegralMixedFramedHistoryFamilyBits.family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (he : BinaryFn e) (hc : BinaryFn center) (hi : BinaryFn selected)
    (power : List Bool→Fin 3) (hpower : BinaryFn (fun c=>(power c).val)) (negativeEta negativeEpsilon : Bool) :
    FixedWidthTarskiPrincipalBits.Access
      (family P D H L F C hs parent terminal d e center selected power negativeEta negativeEpsilon) :=by
  have HD : BinaryFn (degree d):=degree_binary d hd
  exact {
    head:=headReader P D H L F C hs parent terminal d e center selected a hL hF hC I h hb Hnew bank hbank
      hp ht hd he hc hi negativeEta
    query:=queryReader P D H L F C hs parent terminal d e center selected a hL hF hC Hnew bank hbank
      hp ht hd he hc hi power hpower negativeEpsilon
    degree:=HD
    bound:=HD.add (BinaryFn.const 2)
    seedDegree:=HD.sub (BinaryFn.const 1) }

end LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiFamilyBits
