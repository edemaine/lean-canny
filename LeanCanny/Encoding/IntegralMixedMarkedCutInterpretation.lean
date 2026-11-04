/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedCutStage
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixPoint
public import LeanCanny.Encoding.IntegralFramedTraceCutObservation
/-! # Every chronological cut interpretation reads its own natural prefix -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedCutStage
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank parent saved
  IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedExceptionalBounds.auxiliaryCap
  IntegralMixedAuxiliaryMarkedIntegerPlan.degree IntegralMixedAuxiliaryMarkedIntegerSource.source
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus

variable (root w :List Bool) (hw :SquareSampleCompleteVertices.Valid
  (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
  (IntegralMixedMarkedPrefixFieldReadback.context root) w)
  (j :ℕ) (hj :j<IntegralMixedCausalRecordPlanBits.count root)
local notation "b"=>number n root+8+j
local notation "old"=>saved hn ht ha hR0 root b
local notation "task"=>parent hn ht ha hR0 root b
local notation "x"=>IntegralMixedCutSource.Family.state G old

include hj in
theorem fits :(G).birth old≤(G).birth ((B).key (CTX root)):=by
  have HB :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount;omega
  rw [saved_birth hn ht ha hR0 root b HB]
  change b≤IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (CTX root)
  rw [IntegralMixedPhysicalFieldEquality.count_eq]
  simp only [IntegralMixedMarkedPrefixFieldReadback.context,pairFst_pair]
  exact HB.le

attribute [local semireducible] IntegralMixedFramedHistoryFamilyBits.family

theorem quotients_at (oldkey :List Bool) (hkey :oldkey=old)
    (φ :((G).state oldkey).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (((G).state oldkey).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSuffixTest.rawTuple B (CTX root) w hw
        (i.val+(IntegralFramedTerminalCutTest.count P D H
          (IntegralFramedPhysicalTraceCutSource.taskKey B) task-(G).birth oldkey))^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P task)
          (2^(G).width oldkey) ((G).birth oldkey) i) :
    ∀i :Fin (commands P D oldkey).length,
      φ (((G).state oldkey).bank.numerator i)/(((G).state oldkey).bank.denominator i:ℝ)=
        (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj.le).point
          (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw) i.val:=by
  have HB :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount;omega
  have HF0:=fits hn ht ha hR0 root j hj
  have HF :(G).birth oldkey≤(G).birth ((B).key (CTX root)):=
    (congrArg (G).birth hkey).trans_le HF0
  have HR :pairFst ((B).key (CTX root))=root:=by
    rw [IntegralMixedPhysicalFieldEquality.key_root]
    exact pairFst_pair _ _
  have HE :oldkey=keyAt (pairFst ((B).key (CTX root))) b (BinaryNatCode.encode 2):=by
    rw [HR]
    exact hkey.trans (saved_eq hn ht ha hR0 root b HB)
  have HM :b≤prefixLength P ((B).key (CTX root)):=
    ((congrArg (G).birth hkey).trans (saved_birth hn ht ha hR0 root b HB)).symm.trans_le
      (HF.trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _))
  have HP :oldkey=IntegralMixedVirtualTaskBits.saved P
      (IntegralFramedPhysicalTraceCutSource.parent B (CTX root) (List.replicate b true)):=by
    simpa only [saved,parent,IntegralMixedMarkedPrefixFieldReadback.context,
      IntegralMixedPhysicalMarkedTest.sampleContext] using hkey
  have HGen :∀i,φ (((G).state oldkey).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSuffixTest.rawTuple B (CTX root) w hw
        (i.val+(IntegralFramedTerminalCutTest.count P D H (IntegralFramedPhysicalTraceCutSource.taskKey B)
          (IntegralFramedPhysicalTraceCutSource.parent B (CTX root) (List.replicate b true))-(G).birth oldkey))^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P
          (IntegralFramedPhysicalTraceCutSource.parent B (CTX root) (List.replicate b true)))
          (2^(G).width oldkey) ((G).birth oldkey) i:=by
    simpa only [parent,IntegralMixedMarkedPrefixFieldReadback.context,
      IntegralMixedPhysicalMarkedTest.sampleContext] using hφ
  have HQ:=IntegralFramedPhysicalTraceCutSource.quotient_observation B
    (IntegralMixedPhysicalTraceCutTest.key_context hn ht ha (radius_binary hR0) false)
    (CTX root) w hw (List.replicate b true) oldkey HP b HM (BinaryNatCode.encode 2) HE HF φ HGen
  have HObs :IntegralFramedPhysicalScalarObservation.atKeyObservation P D oldkey=
      IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj.le:=by
    have H0:=congrArg (IntegralFramedPhysicalScalarObservation.atKeyObservation P D)
      (hkey.trans (saved_eq hn ht ha hR0 root b HB))
    have HB0 :b≤(P).cap root+1:=by
      unfold IntegralMixedPhysicalMarkedPlan.bank
      exact IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 root j hj.le
    have H1:=IntegralFramedPhysicalScalarObservation.observation_keyAt P D root b (BinaryNatCode.encode 2) HB0
    have H2 :IntegralFramedPhysicalPrefixObservation.atRoot P D root b HB0=
        IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj.le:=by
      unfold IntegralMixedPhysicalMarkedPlan.bank
      rfl
    exact H0.trans (H1.trans H2)
  intro i
  exact (HQ i).trans (congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.point
    (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw) i.val) HObs)

end LeanCanny.Encoding.IntegralMixedMarkedCutStage
