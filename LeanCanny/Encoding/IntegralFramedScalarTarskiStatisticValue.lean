/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedScalarTarskiStatistic
public import LeanCanny.Algebra.RealIteratedTarski
/-! # The streamed statistic specializes one actual principal sequence

This identifies the declared principal statistic. Equality to a Tarski root
query still requires the exact head and seed degree semantics.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedScalarTarskiStatistic
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open Polynomial PrincipalSubresultant
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthTarskiPrincipalBits.polynomial

private theorem principal_cast_retarget (MF : FixedWidthTarskiPrincipalBits.Family)
    (M : ℕ) (z z' : List Bool) (hz : z=z') (j j' : ℕ) (hj : j=j')
    (h : MF.arity z=M) (h' : MF.arity z'=M) :
    MvTwoParameterEncodedCoefficient.castPolynomial h (FixedWidthTarskiPrincipalBits.polynomial MF z j)=
      MvTwoParameterEncodedCoefficient.castPolynomial h' (FixedWidthTarskiPrincipalBits.polynomial MF z' j') :=by
  subst z'
  subst j'
  rfl

private theorem reverse_range (d : ℕ) :
    (List.range (d+1)).reverse=(List.range (d+1)).map (fun i=>d-i) :=by
  have H:=List.reverse_range' (s:=0) (n:=d+1)
  simpa only [Nat.zero_add,Nat.add_sub_cancel,←List.range_eq_range'] using H

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
variable (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
variable (key : List Bool→List Bool) (hpos : ∀c,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key c))
variable (O : SquareSampleInput.Inputs)
variable (hc : ∀c,O.count c=(IntegralMixedFramedBankSnapshotBits.atKey P D H (key c)).count)
variable (MF : FixedWidthTarskiPrincipalBits.Family) (read : List Bool→List Bool)
variable (budget height : List Bool→ℕ)
variable (dim : ∀c b,MF.arity (read (pair c b))=O.count c+2)
variable (hdegree : ∀c b j,(FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) j).totalDegree≤budget (pair c b))
variable (hmass : ∀c b j,MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) j)≤2^height (pair c b))
local notation "S" => IntegralFramedPhysicalSquare.input P D H L F C hs key hpos

noncomputable def specialization (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :=
  IntegralFramedScalarTarskiIteratedSign.specialization P D H L F C hs key hpos O hc MF read dim c w b hv

noncomputable def principal (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (j : ℕ) :=
  specialization P D H L F C hs key hpos O hc MF read dim c w b hv
    (FixedWidthTarskiPrincipalBits.polynomial MF (read (pair c b)) j)

theorem signs_packet (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (k : ℕ) :
    signs P D H L F C hs key hpos O hc MF read budget height dim hdegree hmass
      (pair (pair (pair c w) b) (BinaryNatCode.encode k))=
      InfinitesimalSign.encode (SignType.sign (RealIteratedTarski.lex
        (principal P D H L F C hs key hpos O hc MF read dim c w b hv
          (MF.degree (read (pair c b))-k)))) :=by
  unfold signs query
  simp only [pairFst_pair,pairSnd_pair]
  rw [IntegralFramedScalarTarskiIteratedSign.value_at (hv:=hv)]
  unfold IntegralFramedScalarTarskiIteratedSign.selected
  simp only [Function.comp_apply]
  have HB : base (pair c (pair b (BinaryNatCode.encode k)))=pair c b :=by
    simp only [base,pairFst_pair,pairSnd_pair]
  have HJ : index MF read (pair c (pair b (BinaryNatCode.encode k)))=MF.degree (read (pair c b))-k :=by
    unfold index
    rw [HB]
    simp only [pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HM : MF.arity (read (base (pair c (pair b (BinaryNatCode.encode k)))))=O.count c+2 :=by
    rw [HB]
    exact dim c b
  rw [principal_cast_retarget MF (O.count c+2) _ _ (congrArg read HB) _ _ HJ HM (dim c b)]
  rfl

theorem value_at (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    value P D H L F C hs key hpos O hc MF read budget height dim hdegree hmass (pair (pair c w) b)=
      permanencesMinusVariations ((List.range (MF.degree (read (pair c b))+1)).reverse.map
        (fun j=>RealIteratedTarski.lex (principal P D H L F C hs key hpos O hc MF read dim c w b hv j))) :=by
  unfold value
  rw [CanonicalSignStatisticBits.value_at _ _ _
    (fun k=>RealIteratedTarski.lex (principal P D H L F C hs key hpos O hc MF read dim c w b hv
      (MF.degree (read (pair c b))-k)))
    (fun k _=>signs_packet P D H L F C hs key hpos O hc MF read budget height dim hdegree hmass c w b hv k)]
  simp only [count,IntegralFramedScalarTarskiIteratedSign.inputContext,pairFst_pair,pairSnd_pair]
  rw [reverse_range,List.map_map]
  rfl

noncomputable def model (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :=
  RealIteratedTarski.value
    ((MF.head (read (pair c b))).map (specialization P D H L F C hs key hpos O hc MF read dim c w b hv))
    ((MF.query (read (pair c b))).map (specialization P D H L F C hs key hpos O hc MF read dim c w b hv))
    (MF.degree (read (pair c b))) (MF.bound (read (pair c b))) (MF.seedDegree (read (pair c b)))

theorem model_at (c w b : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    value P D H L F C hs key hpos O hc MF read budget height dim hdegree hmass (pair (pair c w) b)=
      model P D H L F C hs key hpos O hc MF read dim c w b hv :=by
  rw [value_at]
  unfold model RealIteratedTarski.value
  apply congrArg permanencesMinusVariations
  apply List.map_congr_left
  intro j _
  rw [principal,FixedWidthTarskiPrincipalBits.selected]
  rfl

end LeanCanny.Encoding.IntegralFramedScalarTarskiStatistic
