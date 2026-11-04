/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedRealization
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedFieldRetention
/-! # Initial chronological seed values are the old accepted prelude values -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem point_drop {n S B :ℕ} {Q :SpatialSource n}
    (x :State Q S B 0 (Fin 0)) (cs :List (Instruction n B)) (hc :cs.length≤S+1)
    (k :ℕ) (hk :k≤cs.length) (hd :(cs.drop k).length≤S+1) (z :ℕ→ℝ) (i :Fin (cs.drop k).length) :
    (ofCommands x (cs.drop k) hd).point z i.val=(ofCommands x cs hc).point z (k+i.val):=by
  induction cs generalizing k with
  | nil=>simp only [List.drop_nil,List.length_nil] at i;exact Fin.elim0 i
  | cons c cs ih=>
    cases k with
    | zero=>simp only [List.drop_zero,Nat.zero_add]
    | succ k=>
      have HT :cs.length≤S+1:=by simp only [List.length_cons] at hc;omega
      have HI :k+i.val<cs.length:=by have H:=i.isLt;simp only [List.drop_succ_cons,List.length_drop] at H;omega
      have HH:=ih HT k (by simp only [List.length_cons] at hk;omega) hd i
      refine HH.trans ?_
      have HP:=IntegralFramedPhysicalPrefixPoint.point_cons x c cs hc HT z ⟨k+i.val,HI⟩
      simpa only [Fin.val_mk,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using HP.symm

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedExceptionalBounds.auxiliaryCap
  preparedRoot seedOlder seedSelections seedTail seedState seedPoint
  IntegralMixedMarkedRecordContinuation.oldCommands

private theorem observation_commands {a S B :ℕ} {Q :SpatialSource a}
    (x :State Q S B 0 (Fin 0)) (cs ds :List (Instruction a B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (he :cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd:=by cases he;rfl

theorem original_prelude_value (root :List Bool) (u :ℕ→ℝ) (i :ℕ) (hi :i<number n root+8) :
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root 0 (Nat.zero_le _)).point u i=
      (IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root).point u
        (IntegralMixedCausalRecordPlanBits.count root+i):=by
  have HL:=IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0 root
  change ((D).rules root).length=number n root+8+IntegralMixedCausalRecordPlanBits.count root at HL
  have HD:=paddedPast_drop (defaultInstruction P D root) ((D).rules root) ((D).rules root).length
    (number n root+8) (by omega)
  rw [paddedPast_full,HL,Nat.add_sub_cancel_left] at HD
  have HO :IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root 0 (Nat.zero_le _)=
      ofCommands (initial P D root) (((D).rules root).drop (IntegralMixedCausalRecordPlanBits.count root))
        (by rw [List.length_drop,HL];have HH :((D).rules root).length+2≤(P).cap root+1:=(D).room root;omega):=by
    unfold IntegralMixedMarkedPrefixObservation.observation
    apply observation_commands
    simpa only [Nat.add_zero] using HD.symm
  rw [HO]
  exact point_drop (initial P D root) ((D).rules root) (by have HH :((D).rules root).length+2≤(P).cap root+1:=(D).room root;omega)
    (IntegralMixedCausalRecordPlanBits.count root) (by omega) _ u
    ⟨i,by rw [List.length_drop,HL];omega⟩

theorem seedPoint_observation (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (i :Fin (seedOlder hn ht ha hR0 old).length) :
    seedPoint hn ht ha hR0 old hv i=
      (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (preparedRoot hn ht ha hR0 old)
        0 (Nat.zero_le _)).point (oldTuple hn ht ha hR0 old hv) i.val:=by
  rw [prelude_observation]
  have HE:=IntegralMixedFramedRunObservation.point_actual (initial P D (preparedRoot hn ht ha hR0 old))
    (seedOlder hn ht ha hR0 old)
    (by rw [seedOlder,IntegralMixedMarkedRecordContinuation.oldCommands_length]
        exact (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 _ _ (by omega)).trans (Nat.le_succ _))
    (oldTuple hn ht ha hR0 old hv) i
  unfold seedPoint IntegralMixedFullBankPoint.point IntegralMixedCanonicalBankPoint.point
  unfold seedState preludeTuple
  unfold seedOlder at i HE ⊢
  simpa only [reframe,Function.comp_apply,IntegralMixedMarkedRecordContinuation.oldCommands,
    IntegralMixedCanonicalBankPoint.point] using HE.symm

theorem seedPoint_original (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (i :Fin (seedOlder hn ht ha hR0 old).length) :
    seedPoint hn ht ha hR0 old hv i=
      (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old)
        0 (Nat.zero_le _)).point (oldTuple hn ht ha hR0 old hv) i.val:=by
  rw [seedPoint_observation]
  have HE:=IntegralMixedMarkedPrefixObservation.eq hn ht ha hR0
    (IntegralMixedRoadmapAtomic.root old) (preparedRoot hn ht ha hR0 old)
    (by simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,preparedRoot,
      IntegralMixedRoadmapAtomic.root,candidate_packet,pairFst_pair])
    (prepared_count hn ht ha hR0 old hv) 0 (Nat.zero_le _) (by intro j hj;omega)
  rw [HE]

theorem oldTuple_natural (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    oldTuple hn ht ha hR0 old hv=IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0
      (IntegralMixedRoadmapAtomic.root old) (IntegralMixedRoadmapAtomic.word old)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv):=by
  unfold oldTuple IntegralMixedMarkedPrefixTransfer.tuple IntegralMixedMarkedPrefixFieldReadback.natural
    IntegralFramedPhysicalPrefixObservation.tuple IntegralFramedPhysicalSquare.naturalPoint
    IntegralMixedFramedBankObservation.extend
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  rfl

theorem seedPoint_old_field (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (label :ℕ) (hl :label<(seedOlder hn ht ha hR0 old).length) :
    seedPoint hn ht ha hR0 old hv ⟨(seedOlder hn ht ha hR0 old).length-1-label,by omega⟩=
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) label:=by
  have HN:=IntegralMixedMarkedPreludeCongruence.number_eq (n:=n)
    (IntegralMixedRoadmapAtomic.root old) (preparedRoot hn ht ha hR0 old)
    (by simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,preparedRoot,
      IntegralMixedRoadmapAtomic.root,candidate_packet,pairFst_pair])
  have HO:=seed_older_length hn ht ha hR0 old
  have HC:=IntegralMixedPhysicalFieldEquality.count_eq hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context old)
  have HT :IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context old)=number n (IntegralMixedRoadmapAtomic.root old)+8+
        IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root old):=by
    simpa only [IntegralMixedRoadmapAtomic.context,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount] using HC
  rw [seedPoint_original,original_prelude_value hn ht ha hR0 _ _ _ (by omega),oldTuple_natural]
  have HI :IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root old)+
      ((seedOlder hn ht ha hR0 old).length-1-label)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedRoadmapAtomic.context old):=by omega
  rw [IntegralMixedMarkedPrefixFieldReadback.full_value hn ht ha hR0 _ _ _ _ HI]
  unfold IntegralMixedPhysicalFieldEquality.point IntegralMixedPhysicalFieldEquality.newest
  rw [min_eq_left (by omega)]
  congr 1
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
