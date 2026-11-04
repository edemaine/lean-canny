/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPrefix
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendParent
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixPoint
/-! # Exact old raw-prefix retention preserves every historical bank field -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex (arity)
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem arity_append {n B :ℕ} (cs ds :List (Instruction n B)) :
    arity (cs++ds)=arity cs+arity ds:=by
  induction cs with
  | nil=>simp only [List.nil_append,arity,Nat.zero_add]
  | cons c cs ih=>simp only [List.cons_append,arity,ih];omega

theorem arity_drop_le {n B :ℕ} (cs :List (Instruction n B)) (k :ℕ) :arity (cs.drop k)≤arity cs:=by
  have H:=arity_append (cs.take k) (cs.drop k)
  rw [List.take_append_drop] at H
  omega

theorem arity_prefix_mono {n B :ℕ} (cs :List (Instruction n B)) (fallback :Instruction n B)
    (a b :ℕ) (hab :a≤b) (hb :b≤cs.length) :
    arity (paddedPast fallback cs a)≤arity (paddedPast fallback cs b):=by
  rw [paddedPast_valid fallback cs a (hab.trans hb),paddedPast_valid fallback cs b hb]
  simp only [past,List.reverse_take,List.length_reverse,List.reverse_reverse]
  have HE :cs.drop (cs.length-a)=(cs.drop (cs.length-b)).drop (b-a):=by
    rw [List.drop_drop]
    congr 1
    omega
  rw [HE]
  exact arity_drop_le _ _

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root

theorem chronological_value (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX root) w)
    (j :ℕ) (hj :j≤IntegralMixedCausalRecordPlanBits.count root)
    (i :ℕ) (hi :i<number n root+8+j) :
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj).point
      (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw) i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX root) w hw
        (number n root+8+j-1-i):=by
  have HV:=IntegralMixedMarkedPrefixPoint.value hn ht ha hR0 root w hw j hj i hi
  have HC :IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (CTX root)=
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    rw [IntegralMixedPhysicalFieldEquality.count_eq]
    simp only [IntegralMixedMarkedPrefixFieldReadback.context,pairFst_pair]
  have HM :number n root+8+j≤IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount;omega
  have HE :IntegralMixedPhysicalFieldEquality.newest
      (IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (CTX root))
      (number n root+8+j-1-i)=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root-(number n root+8+j)+i:=by
    rw [HC]
    unfold IntegralMixedPhysicalFieldEquality.newest
    rw [min_eq_left (by omega)]
    omega
  unfold IntegralMixedPhysicalFieldEquality.point
  rw [HE]
  exact HV

attribute [local irreducible] preparedRoot start IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedMarkedPrefixObservation.observation IntegralMixedRoadmapAtomic.root
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.payload
  IntegralMixedRoadmapAtomic.depth IntegralMixedRoadmapAtomic.endBirth
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)

/-- All old prefix bank values are preserved by literal raw-column retention.
The tuple premise is exactly on the old meaningful prefix, not on either
complete word or on independently chosen bank coordinate roots. -/
theorem past_prefix_point (z v :ℕ→ℝ)
    (hz :∀r<(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0
      (IntegralMixedRoadmapAtomic.root old) (start hn ht ha hR0 old) (start_fit hn ht ha hR0 old hv)).arity,z r=v r)
    (j :ℕ) (hj :j≤start hn ht ha hR0 old) (i :ℕ)
    (hi :i<number n (IntegralMixedRoadmapAtomic.root old)+8+j) :
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (preparedRoot hn ht ha hR0 old producer) j
      ((hj.trans (start_fit hn ht ha hR0 old hv)).trans_eq (prepared_count hn ht ha hR0 old hv hd producer he).symm)).point z i=
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old) j
      (hj.trans (start_fit hn ht ha hR0 old hv))).point v i:=by
  have HE:=prefix_observation hn ht ha hR0 old hv hd producer he j hj
  have H0:=congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.point z i) HE
  apply H0.trans
  unfold IntegralMixedMarkedPrefixObservation.observation
  let root:=IntegralMixedRoadmapAtomic.root old
  let cs:=paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root) ((D).rules root) (number n root+8+j)
  have HI :i<cs.length:=by dsimp only [cs];rw [paddedPast_length];exact hi
  apply IntegralMixedMarkedPrefixPoint.point_congr (IntegralMixedFramedHistoryFamilyBits.initial P D root) cs
    (by dsimp only [cs];rw [paddedPast_length];exact
      (IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 root j (hj.trans (start_fit hn ht ha hR0 old hv))).trans (Nat.le_succ _)) z v ?_ ⟨i,HI⟩
  intro r hr
  apply hz r
  unfold IntegralMixedMarkedPrefixObservation.observation
  change r<arity (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)
    ((D).rules root) (number n root+8+start hn ht ha hR0 old))
  exact hr.trans_le (arity_prefix_mono ((D).rules root) (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D root)
    (number n root+8+j) (number n root+8+start hn ht ha hR0 old) (by omega) (by
      rw [IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0 root]
      unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
      have HFit :start hn ht ha hR0 old≤IntegralMixedCausalRecordPlanBits.count root:=start_fit hn ht ha hR0 old hv
      omega))

include hv in
theorem old_valid_native :SquareSampleCompleteVertices.Valid S
    (CTX (IntegralMixedRoadmapAtomic.root old)) (IntegralMixedRoadmapAtomic.word old):=
  IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv

theorem oldNatural_eq_native :oldNatural hn ht ha hR0 old hv=
    IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old)
      (IntegralMixedRoadmapAtomic.word old) (old_valid_native hn ht ha hR0 old hv):=by
  unfold oldNatural IntegralMixedMarkedPrefixTransfer.tuple IntegralFramedPhysicalPrefixObservation.tuple
    IntegralMixedMarkedPrefixFieldReadback.natural IntegralFramedPhysicalSquare.naturalPoint
    IntegralMixedFramedBankObservation.extend IntegralMixedMarkedReservedParent.bank IntegralMixedPhysicalMarkedPlan.bank
  rfl

/-- The local continuation's raw-column receipt is precisely the old-prefix
receipt consumed by guard persistence; the old complete ordinal is not reused. -/
theorem past_raw_native (z :ℕ→ℝ)
    (hz :∀r<arity (parentCommands hn ht ha hR0 old hv hd producer he),z r=oldNatural hn ht ha hR0 old hv r) :
    ∀r<(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0
      (IntegralMixedRoadmapAtomic.root old) (start hn ht ha hR0 old) (start_fit hn ht ha hR0 old hv)).arity,
      z r=IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old)
        (IntegralMixedRoadmapAtomic.word old) (old_valid_native hn ht ha hR0 old hv) r:=by
  have H0:=prefix_observation hn ht ha hR0 old hv hd producer he (start hn ht ha hR0 old) le_rfl
  have H1:=parent_observation hn ht ha hR0 old hv hd producer he
  have HA :(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0
      (IntegralMixedRoadmapAtomic.root old) (start hn ht ha hR0 old) (start_fit hn ht ha hR0 old hv)).arity=
      arity (parentCommands hn ht ha hR0 old hv hd producer he):=
    (congrArg IntegralMixedFramedRunObservation.Data.arity H0).symm.trans
      (congrArg IntegralMixedFramedRunObservation.Data.arity H1)
  intro r hr
  exact (hz r (hr.trans_eq HA)).trans (congrFun (oldNatural_eq_native hn ht ha hR0 old hv) r)

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
