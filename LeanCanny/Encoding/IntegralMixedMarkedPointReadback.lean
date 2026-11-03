/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPointTest
public import LeanCanny.Encoding.IntegralMixedMarkedLeafPowers
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedOldInterpretation
public import LeanCanny.Geometry.IntegralMixedFramedBankTermObservation
/-! # Marked term variables are the actual chronological retained quotients -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPointReadback
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedIntegerSource (number original oldKey tail beta)
open IntegralMixedAuxiliaryParametricSlackSource (regularizationAt penaltyAt)
open IntegralMixedAuxiliaryMarkedOldInterpretation (count_at charge_at)
open IntegralMixedCandidateReplayNew (bank input sampleContext)
open IntegralMixedMarkedPointTest (charge)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

theorem key_root (ctx : List Bool) : pairFst ((bank hn ht ha hR).key (sampleContext ctx))=ctx := by
  simp only [IntegralMixedCandidateReplayNew.bank,IntegralMixedAuxiliaryMarkedIntegerPlan.bank,
    IntegralMixedAuxiliaryMarkedIntegerPlan.bankKey,sampleContext,IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]

theorem count_eq (ctx : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey (bank hn ht ha hR).parameters (bank hn ht ha hR).plan
      (bank hn ht ha hR).data ((bank hn ht ha hR).key (sampleContext ctx))).count=number n ctx+8 := by
  change (input hn ht ha hR).count (sampleContext ctx)=_
  simpa only [sampleContext,pairFst_pair] using IntegralMixedCandidateReplayNew.count_eq hn ht ha hR (sampleContext ctx)

attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerPlan.bank

noncomputable abbrev env (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w) :=
  IntegralFramedBankTermCurrentQ.point (bank hn ht ha hR) (sampleContext ctx) w hv

noncomputable def point (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w) : Fin (number n ctx+4)→ℝ :=
  fun i=>env hn ht ha hR ctx w hv i.val

theorem coordinate (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w)
    (j : ℕ) (hj : j<number n ctx+8) :
    env hn ht ha hR ctx w hv j=IntegralMixedMarkedLeafTest.point hn ht ha hR ctx w hv j := by
  have HJ : j<(IntegralMixedFramedBankSnapshotBits.atKey (bank hn ht ha hR).parameters (bank hn ht ha hR).plan
      (bank hn ht ha hR).data ((bank hn ht ha hR).key (sampleContext ctx))).count := by rw [count_eq]; exact hj
  unfold env IntegralFramedBankTermCurrentQ.point LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point
  rw [dite_eq_left HJ]
  have HX:=IntegralMixedFramedBankObservation.point_ofState
    (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state (bank hn ht ha hR).parameters (bank hn ht ha hR).plan
      (bank hn ht ha hR).data ((bank hn ht ha hR).key (sampleContext ctx)))
    (SquareSampleCompleteVertices.candidate (input hn ht ha hR) (sampleContext ctx) w hv).val
    ⟨IntegralMixedFramedBankTermBits.reverseIndex (bank hn ht ha hR).parameters (bank hn ht ha hR).plan
      (bank hn ht ha hR).data ((bank hn ht ha hR).key (sampleContext ctx)) j,
      IntegralMixedFramedBankTermBits.reverse_lt _ _ _ _ _ HJ⟩
  rw [←HX]
  unfold IntegralMixedMarkedLeafTest.point IntegralMixedFramedBankTermBits.reverseIndex
  congr 1
  change (IntegralMixedFramedBankSnapshotBits.atKey (bank hn ht ha hR).parameters (bank hn ht ha hR).plan
    (bank hn ht ha hR).data ((bank hn ht ha hR).key (sampleContext ctx))).count-1-j=number n ctx+7-j
  rw [count_eq]
  omega

theorem parameters (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w)
    (hl : IntegralMixedMarkedLeafScan.holds hn ht ha hR (pair ctx w)) :
    env hn ht ha hR ctx w hv (number n ctx+4)=(2:ℝ)^R ctx ∧
    env hn ht ha hR ctx w hv (number n ctx+5)=(2:ℝ)^LeanCanny.Geometry.BoundedRegularSource.regularizationExponent
      (number n ctx) (charge t ctx) (charge t ctx) (R ctx) ∧
    env hn ht ha hR ctx w hv (number n ctx+6)=(2:ℝ)^LeanCanny.Geometry.BoundedZeroSource.perturbationExponent
      (number n ctx) (charge t ctx) (charge t ctx) (R ctx) ∧
    env hn ht ha hR ctx w hv (number n ctx+7)=(2:ℝ)^LeanCanny.Geometry.BoundedZeroSource.penaltyExponent
      (number n ctx) (charge t ctx) (R ctx) := by
  have HR : (R∘tail) (oldKey n t ctx)=R ctx:=congrArg R (IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail n t ctx)
  have HRoots:=(IntegralMixedMarkedLeafScan.holds_iff hn ht ha hR ctx w hv).mp hl
  refine ⟨?_,?_,?_,?_⟩
  · exact (coordinate hn ht ha hR ctx w hv _ (by omega)).trans
      (IntegralMixedMarkedLeafPowers.radius hn ht ha hR ctx w hv HRoots)
  · have H:=IntegralMixedMarkedLeafPowers.regularization hn ht ha hR ctx w hv HRoots
    have HH:= (coordinate hn ht ha hR ctx w hv (number n ctx+5) (by omega)).trans H
    simpa only [regularizationAt,count_at,charge_at,HR,charge,LeanCanny.Geometry.AuxiliaryCandidateRegularLift.allowance] using HH
  · have H:=IntegralMixedMarkedLeafPowers.perturbation hn ht ha hR ctx w hv HRoots
    have HH:= (coordinate hn ht ha hR ctx w hv (number n ctx+6) (by omega)).trans H
    simpa only [beta,count_at,charge_at,HR,charge,LeanCanny.Geometry.AuxiliaryCandidateRegularLift.allowance] using HH
  · have H:=IntegralMixedMarkedLeafPowers.penalty hn ht ha hR ctx w hv HRoots
    have HH:= (coordinate hn ht ha hR ctx w hv (number n ctx+7) (by omega)).trans H
    simpa only [penaltyAt,count_at,charge_at,HR,charge,LeanCanny.Geometry.AuxiliaryCandidateRegularLift.allowance] using HH

end LeanCanny.Encoding.IntegralMixedMarkedPointReadback
