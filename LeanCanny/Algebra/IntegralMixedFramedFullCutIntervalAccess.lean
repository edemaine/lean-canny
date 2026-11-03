/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFullCutIntervalFamily
public import LeanCanny.Algebra.FixedWidthBivariateTernaryPower
/-! # Original-only native principals for actual full-factor interval queries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullCutIntervalFamily
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (parent terminal : List Bool→List Bool) (d selected : List Bool→ℕ)

theorem degree_binary (hd : BinaryFn d) : BinaryFn (degree d) :=
  (BinaryFn.ite ((BinaryFn.const 1).le hd) hd (BinaryFn.const 1)).of_eq (fun _=>by simp only [degree,max_def])

theorem width_unary (a : Access P) (hp : parent∈FP) (ht : terminal∈FP)
    (hd : BinaryFn d) (hi : BinaryFn selected) :
    UnaryFn (width P D H L F C hs parent terminal d selected) :=by
  have HD:=degree_binary d hd
  have HP:=IntegralMixedFramedFullCutHead.headDegree_binary P D H parent a hp
  have HQ : BinaryFn (queryBound P D H L F C hs terminal selected):=(BinaryFn.const 2).mul
    ((IntegralMixedFramedWindowQuery.weight_binary P D H L F C hs terminal selected a ht hi).add (BinaryFn.const 1))
  have HR:=MultivariateTarskiDegreeBounds.principalDegreeBound_binary HD (HD.sub (BinaryFn.const 1))
    (HD.add (BinaryFn.const 2)) HP HQ
  have HW : BinaryFn (wholeBound P D H L F C hs parent terminal d selected):=(HP.add HQ).add HR
  exact (UnaryFn.length HW.bits_mem_FP).of_eq (fun _=>BinaryNatCode.length_encode _)

attribute [local irreducible] width

noncomputable def headReader (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (hi : BinaryFn selected) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial
      (fun c=>1+(arity P D H terminal c+1)) (width P D H L F C hs parent terminal d selected)
      (head P D H parent terminal d)) :=by
  let A:=arity P D H terminal
  let W:=width P D H L F C hs parent terminal d selected
  let PH:=IntegralMixedFramedFullCutTerminalHead.polynomial P D H parent terminal d
  let HP:=headBound P D H parent
  have HA : UnaryFn A:=(IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht
  have HW : UnaryFn W:=width_unary P D H L F C hs parent terminal d selected a hp ht hd hi
  have HH : ∀c y,((PH c).coeff y).totalDegree≤HP c:=
    IntegralMixedFramedFullCutTerminalHead.coefficient_degree P D H parent terminal d
  have HFH (c : List Bool) : HP c<2^W c :=by
    have HL : HP c≤wholeBound P D H L F C hs parent terminal d selected c:=by unfold HP wholeBound;omega
    have HB : wholeBound P D H L F C hs parent terminal d selected c<2^W c :=by
      unfold W
      unfold width
      exact Nat.lt_size_self _
    exact HL.trans_lt HB
  let RH:=IntegralMixedFramedFullCutTerminalHead.reader P D H a L F C hL hF hC h hb parent terminal hp ht d W hd HW HFH
  exact FixedWidthBivariateParameterPairBits.reader true A W PH RH HA HW HP HH HFH

noncomputable def queryReader (a : Access P) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (hi : BinaryFn selected)
    (power : List Bool→Fin 3) (hpower : BinaryFn (fun c=>(power c).val)) (negativeEpsilon : Bool) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial
      (fun c=>1+(arity P D H terminal c+1)) (width P D H L F C hs parent terminal d selected)
      (query P D H L F C hs terminal selected power negativeEpsilon)) :=by
  let A:=arity P D H terminal
  let W:=width P D H L F C hs parent terminal d selected
  let PQ:=IntegralMixedFramedWindowQuery.polynomial P D H L F C hs terminal selected negativeEpsilon
  let QP:=windowBound P D H L F C hs terminal selected
  have HA : UnaryFn A:=(IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp ht
  have HW : UnaryFn W:=width_unary P D H L F C hs parent terminal d selected a hp ht hd hi
  have HQ : ∀ c y,((PQ c).coeff y).totalDegree≤QP c:=
    IntegralMixedFramedWindowQuery.coefficient_degree P D H L F C hs terminal selected negativeEpsilon
  have HFQ (c : List Bool) : QP c<2^W c :=by
    have HL : QP c≤wholeBound P D H L F C hs parent terminal d selected c:=by
      unfold QP wholeBound queryBound
      omega
    unfold W
    unfold IntegralMixedFramedFullCutIntervalFamily.width
    have HT : wholeBound P D H L F C hs parent terminal d selected c<
        2^(wholeBound P D H L F C hs parent terminal d selected c).size:=
      Nat.lt_size_self (wholeBound P D H L F C hs parent terminal d selected c)
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
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (bank : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hbank : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew bank)
    (hp : parent∈FP) (ht : terminal∈FP) (hd : BinaryFn d) (hi : BinaryFn selected)
    (power : List Bool→Fin 3) (hpower : BinaryFn (fun c=>(power c).val)) (negativeEpsilon : Bool) :
    FixedWidthTarskiPrincipalBits.Access
      (family P D H L F C hs parent terminal d selected power negativeEpsilon) :=by
  have HD : BinaryFn (degree d):=degree_binary d hd
  exact {
    head:=headReader P D H L F C hs parent terminal d selected a hL hF hC h hb hp ht hd hi
    query:=queryReader P D H L F C hs parent terminal d selected a hL hF hC Hnew bank hbank
      hp ht hd hi power hpower negativeEpsilon
    degree:=HD
    bound:=HD.add (BinaryFn.const 2)
    seedDegree:=HD.sub (BinaryFn.const 1) }

end LeanCanny.Algebra.IntegralMixedFramedFullCutIntervalFamily
