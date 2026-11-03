/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCandidateReplayNew
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerProperties
public import LeanCanny.Algebra.IntegerPolynomialSourceChoice
/-! # Original untruncated integer leaves tested at one marked joint tuple

Only chronological coordinate selection occurs in the datum. The implicit
integer polynomial is the original prelude source, not its padded row.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedLeafTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedCandidateReplayNew (bank input sampleContext)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

def query (z : List Bool) := pair (pairFst (pairFst z))
  (BinaryNatCode.encode (IntegralMixedCandidateReplayDatum.index (pairSnd z)))
theorem query_FP : query∈FP :=
  mem_FP_pair (mem_FP_comp (f:=pairFst) (g:=pairFst) pairFst_mem_FP pairFst_mem_FP)
    (BinaryFn.fromBits (mem_FP_comp (f:=pairSnd) (g:=fun d=>pairFst (pairSnd d)) pairSnd_mem_FP
      (mem_FP_comp (f:=pairSnd) (g:=pairFst) pairSnd_mem_FP pairFst_mem_FP))).bits_mem_FP

noncomputable def source : IntegerPolynomialRootQueriesBits.Source := IntegerPolynomialSourceChoice.reindex
  (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) query

include hR in
theorem source_access : IntegerPolynomialRootQueriesBits.Access (source hn ht ha (R:=R)) :=
  IntegerPolynomialSourceChoice.reindex_access _ (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR) query_FP

noncomputable def value : List Bool→List Bool := IntegralFramedBankUnivariateTest.value
  (bank hn ht ha hR).parameters (bank hn ht ha hR).plan (bank hn ht ha hR).data
  (bank hn ht ha hR).nodes (bank hn ht ha hR).factor (bank hn ht ha hR).seed (bank hn ht ha hR).bounds
  (bank hn ht ha hR).key (bank hn ht ha hR).positive (IntegralMixedCandidateReplayNew.coordinate hn ht ha hR)
  (source hn ht ha (R:=R))

attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerPlan.bank

theorem evaluator : SpaceFunction (value hn ht ha hR) := by
  let A:=IntegralMixedAuxiliaryMarkedIntegerPlan.bank_access hn ht ha hR
  exact IntegralFramedBankUnivariateTest.evaluator _ A.parameters _ _ A.liftedData A.controls A.bounds
    A.nodes A.factor A.seed (bank hn ht ha hR).bounds (bank hn ht ha hR).key A.key (bank hn ht ha hR).positive
    (IntegralMixedCandidateReplayNew.coordinate hn ht ha hR) (IntegralMixedCandidateReplayNew.coordinate_unary hn ht ha hR)
    _ (source_access hn ht ha hR)

noncomputable def point (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w) (j : ℕ) : ℝ :=
  (IntegralMixedFramedBankObservation.ofState (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state
    (bank hn ht ha hR).parameters (bank hn ht ha hR).plan (bank hn ht ha hR).data
    ((bank hn ht ha hR).key (sampleContext ctx)))).point
    (IntegralMixedFramedBankObservation.extend (SquareSampleCompleteVertices.candidate (input hn ht ha hR)
      (sampleContext ctx) w hv).val) (number n ctx+7-j)

theorem source_packet (ctx : List Bool) (i : ℕ) :
    (source hn ht ha (R:=R)).polynomial (pair (sampleContext ctx) (IntegralMixedCandidateReplayDatum.packet [] i 0))=
      (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial (pair ctx (BinaryNatCode.encode i)) := by
  unfold source IntegerPolynomialSourceChoice.reindex
  simp only [Function.comp_apply,query,IntegralMixedCandidateReplayDatum.index,IntegralMixedCandidateReplayDatum.packet,
    sampleContext,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

attribute [local irreducible] value IntegralFramedBankUnivariateTest.value IntegralMixedAuxiliaryMarkedIntegerSource.source

theorem packet (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w)
    (i : ℕ) :
    value hn ht ha hR (pair (pair (sampleContext ctx) w) (IntegralMixedCandidateReplayDatum.packet [] i 0))=
      InfinitesimalSign.encode (SignType.sign
        (((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial (pair ctx (BinaryNatCode.encode i))).eval₂
          (Int.castRingHom ℝ) (point hn ht ha hR ctx w hv i))) := by
  have HI : (IntegralMixedCandidateReplayNew.coordinate hn ht ha hR (sampleContext ctx)
      (IntegralMixedCandidateReplayDatum.packet [] i 0)).val=number n ctx+7-i := by
    rw [IntegralMixedCandidateReplayNew.coordinate]
    change (input hn ht ha hR).count (sampleContext ctx)-1-IntegralMixedCandidateReplayDatum.index (IntegralMixedCandidateReplayDatum.packet [] i 0)=_
    rw [IntegralMixedCandidateReplayNew.count_eq]
    simp only [sampleContext,IntegralMixedCandidateReplayDatum.index,IntegralMixedCandidateReplayDatum.packet,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    omega
  have HP:=IntegralFramedBankUnivariateTest.packet (bank hn ht ha hR).parameters (bank hn ht ha hR).plan
    (bank hn ht ha hR).data (bank hn ht ha hR).nodes (bank hn ht ha hR).factor (bank hn ht ha hR).seed
    (bank hn ht ha hR).bounds (bank hn ht ha hR).key (bank hn ht ha hR).positive
    (IntegralMixedCandidateReplayNew.coordinate hn ht ha hR) (source hn ht ha (R:=R)) (sampleContext ctx) w
    (IntegralMixedCandidateReplayDatum.packet [] i 0) hv
  have HX:=IntegralMixedFramedBankObservation.point_ofState
    (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state (bank hn ht ha hR).parameters (bank hn ht ha hR).plan
      (bank hn ht ha hR).data ((bank hn ht ha hR).key (sampleContext ctx)))
    (SquareSampleCompleteVertices.candidate (input hn ht ha hR) (sampleContext ctx) w hv).val
    (IntegralMixedCandidateReplayNew.coordinate hn ht ha hR (sampleContext ctx) (IntegralMixedCandidateReplayDatum.packet [] i 0))
  have HQ:=source_packet hn ht ha (R:=R) ctx i
  have HPoint : LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
      (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state (bank hn ht ha hR).parameters (bank hn ht ha hR).plan
        (bank hn ht ha hR).data ((bank hn ht ha hR).key (sampleContext ctx)))
      (SquareSampleCompleteVertices.candidate (input hn ht ha hR) (sampleContext ctx) w hv).val
      (IntegralMixedCandidateReplayNew.coordinate hn ht ha hR (sampleContext ctx) (IntegralMixedCandidateReplayDatum.packet [] i 0))=
      point hn ht ha hR ctx w hv i := by
    rw [←HX,HI]
    rfl
  have HE:=congrArg₂ (fun (p : Polynomial ℤ) (v : ℝ)=>p.eval₂ (Int.castRingHom ℝ) v) HQ HPoint
  simpa only [value] using HP.trans (congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v)) HE)

end LeanCanny.Encoding.IntegralMixedMarkedLeafTest
