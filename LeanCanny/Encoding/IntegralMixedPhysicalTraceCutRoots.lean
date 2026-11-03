/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutValidity
public import LeanCanny.Encoding.IntegralMixedPhysicalCutRoot
/-! # Every accepted literal cut retains an actual selected-factor root -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalTraceCutValidity
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open IntegralFramedTraceCutScan (stagePacket)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank IntegralMixedFramedHistoryFamilyBits.family

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool) (ctx w : List Bool) (j : ℕ)
local notation "B" => bank hn ht ha hR outer
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "u" => List.replicate j true
local notation "p" => IntegralFramedPhysicalTraceCutSource.parent B (sampleContext ctx) u
local notation "old" => IntegralMixedVirtualTaskBits.saved P p
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G old
local notation "rule" => IntegralMixedCutSource.Family.rule G old
local notation "kind" => IntegralMixedCutSource.Family.kind G old
local notation "offset" => IntegralFramedTerminalCutTest.count P D H
  (IntegralFramedPhysicalTraceCutSource.taskKey B) p-IntegralMixedCutSource.Family.birth G old

noncomputable def RootCompatible
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w) : Prop :=
  ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv (i.val+offset)^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
          (2^(G).width old) ((G).birth old) i) ∧
    IntegralMixedRelativeCuts.Valid x bound rule φ kind ∧
    ((IntegralMixedRelativeCuts.factor x bound rule kind).map φ.toRingHom).natDegree=(G).degree old ∧
    (IntegralMixedRelativeCuts.factor x bound rule kind).eval₂ φ.toRingHom
      (IntegralMixedPhysicalCutCoefficientSemantics.bankQuotient hn ht ha hR outer ctx w u hv)=0

theorem actual_cut_root
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w)
    (hh : IntegralMixedPhysicalTraceCutScan.holds hn ht ha hR outer (pair ctx w))
    (hj : j<IntegralFramedTraceCutMetadata.length P D ctx)
    (hcut : IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D ctx j).command) :
    RootCompatible hn ht ha hR outer ctx w j hv :=by
  obtain ⟨HC,HA,_⟩:=origin hn ht ha hR outer ctx w j hj hcut
  have HJ : j<IntegralFramedTraceCutMetadata.length P D (pairFst (pair ctx w))+1 :=by
    rw [pairFst_pair]
    omega
  have HB:=IntegralFramedTraceCutOrigin.parent_birth P D (pair ctx w) j HJ
  rw [parent_stage hn ht ha hR outer ctx w j] at HB
  have HCut : IntegralFramedCreatingCut.ParentCut P D p :=by
    change IntegralFramedCreatingCut.ParentCut P D (IntegralFramedTraceCutGuards.parent P (stagePacket (pair ctx w) j)) at HC
    rw [parent_stage hn ht ha hR outer ctx w j] at HC
    exact HC
  have HCount : j<IntegralMixedPhysicalTraceCutScan.count hn ht ha hR outer (pair ctx w) :=by
    rw [IntegralMixedPhysicalTraceCutScan.count_eq_length]
    exact hj
  have HF : IntegralCriticalHistoryTask.birth P p<(G).birth ((B).key (sampleContext ctx)) :=
    HB.trans_lt (HCount.trans_eq (birth_count hn ht ha hR outer ctx w).symm)
  have HG:=hh j HCount (origin hn ht ha hR outer ctx w j hj hcut).1
  have HG' : IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer
      (IntegralMixedPhysicalCutCoefficientSemantics.stage ctx w u) :=by
    simpa only [stagePacket,IntegralMixedPhysicalCutCoefficientSemantics.stage,pairFst_pair,pairSnd_pair] using HG
  exact IntegralMixedPhysicalCutCoefficientSemantics.exists_factor_root hn ht ha hR outer ctx w u hv HA HCut HF
    (by simpa only [List.length_replicate] using HB) HG'

theorem accepted_all_roots (h : pair ctx w∈IntegralMixedPhysicalTraceCutScan.language hn ht ha hR outer) :
    ∃hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w,
      ∀i<IntegralFramedTraceCutMetadata.length P D ctx,
        IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P D ctx i).command→
          RootCompatible hn ht ha hR outer ctx w i hv :=by
  have HP : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w ∧
      IntegralMixedPhysicalTraceCutScan.holds hn ht ha hR outer (pair ctx w) :=by
    simpa only [IntegralMixedPhysicalTraceCutScan.language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] using h
  exact ⟨HP.1,fun i hi hc=>actual_cut_root hn ht ha hR outer ctx w i HP.1 HP.2 hi hc⟩

end LeanCanny.Encoding.IntegralMixedPhysicalTraceCutValidity
