/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention
public import LeanCanny.Encoding.IntegralFramedPhysicalBankChronologicalPoint
/-! # Native chronological fields preserve the marked prelude tests -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate original number)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedPhysicalMarkedSemantics (env)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedPhysicalMarkedPlan.tables
 IntegralMixedFramedHistoryFamilyBits.family env IntegralFramedPhysicalBankTerm.env
 IntegralMixedPhysicalFieldEquality.point IntegralFramedPhysicalSquare.point
 IntegralMixedAuxiliaryMarkedRecordPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bankKey


theorem env_field (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false) (sampleContext ctx) w)
    (i : ℕ) (hi : i < number n ctx+8) :
    env hn ht ha (radius_binary hR0) false ctx w hv i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (sampleContext ctx) w hv i :=by
  let B:=IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
  have HB:=IntegralMixedPhysicalMarkedPlan.count_bound hn ht ha (radius_binary hR0) false ctx
  have HI : i < (IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key (sampleContext ctx))).count:=
    hi.trans_le (by simpa only [B,IntegralMixedPhysicalMarkedPlan.leafCount,sampleContext,pairFst_pair,
      Bool.false_eq_true,ite_false] using HB)
  have HP:=IntegralFramedPhysicalBankTerm.env_chronological B
    (IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false)
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false)
    (sampleContext ctx) w hv i HI
  have HC:=IntegralMixedFramedHistoryFamilyBits.family_birth B.parameters B.plan B.data (B.key (sampleContext ctx))
  have HF : i < IntegralMixedFramedHistoryFamilyBits.prefixLength B.parameters (B.key (sampleContext ctx)):=by
    rw [←HC]
    exact HI
  have HQ:=IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0) (sampleContext ctx) w hv i HF
  have HE:=congrArg (fun j : Fin ((IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth
      (B.key (sampleContext ctx)))=>IntegralFramedPhysicalSquare.point B.parameters B.plan B.data B.nodes B.factor B.seed
        B.bounds B.key B.positive (sampleContext ctx) w hv j)
    (show (⟨(IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth (B.key (sampleContext ctx))-1-i,
      by have H : 0<(IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth (B.key (sampleContext ctx)):=B.positive _;omega⟩ :
      Fin ((IntegralMixedFramedHistoryFamilyBits.family B.parameters B.plan B.data).birth (B.key (sampleContext ctx))))=
      ⟨IntegralMixedFramedHistoryFamilyBits.prefixLength B.parameters (B.key (sampleContext ctx))-1-i,by rw [←HC];omega⟩ from
        Fin.ext (congrArg (fun j : ℕ=>j-1-i) HC))
  unfold env
  exact HP.trans (HE.trans HQ.symm)


theorem language_transfer_fields (cL cR wL wR : List Bool)
    (hL : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false) (sampleContext cL) wL)
    (hR : SquareSampleCompleteVertices.Valid (input hn ht ha (radius_binary hR0) false) (sampleContext cR) wR)
    (hc : candidate cL=candidate cR)
    (he : ∀i < number n cL+8,
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (sampleContext cL) wL hL i=
        IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (sampleContext cR) wR hR i)
    (HL : pair cL wL∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false) :
    pair cR wR∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false :=by
  apply language_transfer hn ht ha hR0 cL cR wL wR hL hR hc _ HL
  intro i hi
  rw [env_field hn ht ha hR0 cL wL hL i hi,env_field hn ht ha hR0 cR wR hR i (by
    rw [←IntegralMixedMarkedPreludeCongruence.number_eq (n:=n) cL cR hc];exact hi)]
  exact he i hi

end LeanCanny.Encoding.IntegralMixedPhysicalMarkedRetention
