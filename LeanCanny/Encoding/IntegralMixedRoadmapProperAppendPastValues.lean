/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendParentTransfer
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPastValues
/-! # Old natural columns preserve every field before a general proper append -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex (arity)
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedRoadmapRetainedAppend (chronological_value arity_prefix_mono)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root

noncomputable abbrev oldNatural (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old):=
  IntegralMixedRoadmapRetainedAppend.oldNatural hn ht ha hR0 old hv

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (left right :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old left right)

include hv in
theorem old_valid_native :SquareSampleCompleteVertices.Valid S
    (CTX (IntegralMixedRoadmapAtomic.root old)) (IntegralMixedRoadmapAtomic.word old):=
  IntegralMixedRoadmapRetainedAppend.old_valid_native hn ht ha hR0 old hv

theorem oldNatural_eq_native :oldNatural hn ht ha hR0 old hv=
    IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old)
      (IntegralMixedRoadmapAtomic.word old) (old_valid_native hn ht ha hR0 old hv):=
  IntegralMixedRoadmapRetainedAppend.oldNatural_eq_native hn ht ha hR0 old hv

include hn ht ha hR0 in
theorem begin_eq_old_start :beginBirth hn ht ha hR0 old=
    number n (IntegralMixedRoadmapAtomic.root old)+8+start hn ht ha hR0 old:=by
  have HI :IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old=
      number n (IntegralMixedRoadmapAtomic.root old)+8:=by
    rw [IntegralMixedRoadmapAtomic.initial_eq]
    simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,
      IntegralMixedRoadmapAtomic.original,pairFst_pair]
  unfold beginBirth IntegralMixedRoadmapAtomic.endBirth start
  rw [HI]

attribute [local irreducible] preparedRoot start IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedMarkedPrefixObservation.observation IntegralMixedRoadmapAtomic.root
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.payload
  IntegralMixedRoadmapAtomic.depth IntegralMixedRoadmapAtomic.endBirth parentCommands

/-- All old prefix bank values are preserved by literal raw-column retention.
The tuple premise is exactly on the old meaningful prefix, not on either
complete word or on independently chosen bank coordinate roots. -/
theorem past_prefix_point (z v :ℕ→ℝ)
    (hz :∀r<(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0
      (IntegralMixedRoadmapAtomic.root old) (start hn ht ha hR0 old) (start_fit hn ht ha hR0 old hv)).arity,z r=v r)
    (j :ℕ) (hj :j≤start hn ht ha hR0 old) (i :ℕ)
    (hi :i<number n (IntegralMixedRoadmapAtomic.root old)+8+j) :
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (preparedRoot hn ht ha hR0 old left right side) j
      ((hj.trans (start_fit hn ht ha hR0 old hv)).trans_eq (prepared_count hn ht ha hR0 old hv hd left right side hE).symm)).point z i=
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old) j
      (hj.trans (start_fit hn ht ha hR0 old hv))).point v i:=by
  have HE:=prefix_observation hn ht ha hR0 old hv hd left right side hE j hj
  have H0:=congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.point z i) HE
  apply H0.trans
  unfold IntegralMixedMarkedPrefixObservation.observation
  let root:=IntegralMixedRoadmapAtomic.root old
  let cs:=paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P PLAN root) ((PLAN).rules root) (number n root+8+j)
  have HI :i<cs.length:=by dsimp only [cs];rw [paddedPast_length];exact hi
  apply IntegralMixedMarkedPrefixPoint.point_congr (IntegralMixedFramedHistoryFamilyBits.initial P PLAN root) cs
    (by dsimp only [cs];rw [paddedPast_length];exact
      (IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 root j (hj.trans (start_fit hn ht ha hR0 old hv))).trans (Nat.le_succ _)) z v ?_ ⟨i,HI⟩
  intro r hr
  apply hz r
  unfold IntegralMixedMarkedPrefixObservation.observation
  change r<arity (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P PLAN root)
    ((PLAN).rules root) (number n root+8+start hn ht ha hR0 old))
  exact hr.trans_le (arity_prefix_mono ((PLAN).rules root) (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P PLAN root)
    (number n root+8+j) (number n root+8+start hn ht ha hR0 old) (by omega) (by
      rw [IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0 root]
      unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
      have HFit :start hn ht ha hR0 old≤IntegralMixedCausalRecordPlanBits.count root:=start_fit hn ht ha hR0 old hv
      omega))

include hd hE in
theorem past_raw_native (z :ℕ→ℝ)
    (hz :∀i<arity (parentCommands hn ht ha hR0 old left right side),z i=oldNatural hn ht ha hR0 old hv i):
    ∀i<(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0
      (IntegralMixedRoadmapAtomic.root old) (start hn ht ha hR0 old) (start_fit hn ht ha hR0 old hv)).arity,
      z i=IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old)
        (IntegralMixedRoadmapAtomic.word old) (old_valid_native hn ht ha hR0 old hv) i:=by
  have H0:=prefix_observation hn ht ha hR0 old hv hd left right side hE (start hn ht ha hR0 old) le_rfl
  have H1 :(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0
      (preparedRoot hn ht ha hR0 old left right side) (start hn ht ha hR0 old)
      (prepared_start_fit hn ht ha hR0 old hv hd left right side hE)).arity=
        arity (parentCommands hn ht ha hR0 old left right side):=by
    unfold IntegralMixedMarkedPrefixObservation.observation
    change arity (paddedPast _ _ (number n (preparedRoot hn ht ha hR0 old left right side)+8+
      start hn ht ha hR0 old))=arity (parentCommands hn ht ha hR0 old left right side)
    unfold parentCommands
    rw [begin_eq_start hn ht ha hR0 old left right side]
  have HA :(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0
      (IntegralMixedRoadmapAtomic.root old) (start hn ht ha hR0 old) (start_fit hn ht ha hR0 old hv)).arity=
      arity (parentCommands hn ht ha hR0 old left right side):=
    (congrArg IntegralMixedFramedRunObservation.Data.arity H0).symm.trans H1
  intro i hi
  exact (hz i (hi.trans_eq HA)).trans (congrFun (oldNatural_eq_native hn ht ha hR0 old hv) i)

include hd hE in
theorem past_fields (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX (preparedRoot hn ht ha hR0 old left right side)) w)
    (hr :∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands hn ht ha hR0 old left right side),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (preparedRoot hn ht ha hR0 old left right side) w hw r=
        oldNatural hn ht ha hR0 old hv r) :
    ∀b,b<beginBirth hn ht ha hR0 old→
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (CTX (preparedRoot hn ht ha hR0 old left right side)) w hw b=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (CTX (IntegralMixedRoadmapAtomic.root old)) (IntegralMixedRoadmapAtomic.word old)
        (old_valid_native hn ht ha hR0 old hv) b:=by
  let r:=preparedRoot hn ht ha hR0 old left right side
  let l:=IntegralMixedRoadmapAtomic.root old
  have HN :number n r=number n l:=IntegralMixedMarkedPreludeCongruence.number_eq r l
    (prepared_candidate hn ht ha hR0 old left right side)
  have HR:=past_raw_native hn ht ha hR0 old hv hd left right side hE _ hr
  intro b hb
  rw [begin_eq_old_start hn ht ha hR0 old] at hb
  change b<number n l+8+start hn ht ha hR0 old at hb
  let i:=number n l+8+start hn ht ha hR0 old-1-b
  have HI :i<number n l+8+start hn ht ha hR0 old:=by dsimp only [i];omega
  have HP:=past_prefix_point hn ht ha hR0 old hv hd left right side hE _ _ HR
    (start hn ht ha hR0 old) le_rfl i HI
  have HL:=chronological_value hn ht ha hR0 l (IntegralMixedRoadmapAtomic.word old)
    (old_valid_native hn ht ha hR0 old hv) (start hn ht ha hR0 old) (start_fit hn ht ha hR0 old hv) i HI
  have HJ:=(start_fit hn ht ha hR0 old hv).trans_eq (prepared_count hn ht ha hR0 old hv hd left right side hE).symm
  have HRI :i<number n r+8+start hn ht ha hR0 old:=by rw [HN];exact HI
  have HV:=chronological_value hn ht ha hR0 r w hw (start hn ht ha hR0 old) HJ i HRI
  have HE :number n l+8+start hn ht ha hR0 old-1-i=b:=by dsimp only [i];omega
  have HE' :number n r+8+start hn ht ha hR0 old-1-i=b:=by rw [HN];exact HE
  rw [HE] at HL
  rw [HE'] at HV
  exact HV.symm.trans (HP.trans HL)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
