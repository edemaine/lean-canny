/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedWord
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedScan
/-! # Literal native columns of the prescribed seed tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "CTX" old=>IntegralMixedRoadmapSeedMetadata.context hn ht ha hR0 old
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters preparedRoot seedOlder seedSelections seedTail
  IntegralMixedFramedPhysicalIndex.prefixArity UniformIntegralPowerSchedule.physical

private theorem native_prelude_arity (root :List Bool) :
    prefixArity (B).parameters T (pair ((B).key (pair root [])) (List.replicate (number n root+8) true))=
      (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root 0 (Nat.zero_le _)).arity:=by
  rw [prefixArity_packet (B).parameters (B).plan (B).data T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false)]
  rw [IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0),pairFst_pair]
  unfold IntegralMixedMarkedPrefixObservation.observation IntegralMixedPhysicalMarkedPlan.bank
  rfl

theorem seed_older_arity (old :List Bool) :
    arity (seedOlder hn ht ha hR0 old)=number n (preparedRoot hn ht ha hR0 old)+8:=by
  have HN:=IntegralMixedRoadmapSeedMetadata.prefix_arity hn ht ha hR0 old 0 (Nat.zero_le _)
  simp only [Nat.add_zero,Nat.mul_zero] at HN
  have HO:=congrArg IntegralMixedFramedRunObservation.Data.arity (prelude_observation hn ht ha hR0 (preparedRoot hn ht ha hR0 old))
  have HP:=native_prelude_arity hn ht ha hR0 (preparedRoot hn ht ha hR0 old)
  simp only [IntegralMixedFramedRunObservation.ofCommands] at HO
  unfold IntegralMixedRoadmapSeedMetadata.context at HN
  simpa only [seedOlder] using HO.symm.trans (HP.symm.trans HN)

private theorem candidates_congr (I J :SquareSampleInput.Inputs) (h:I=J) (c w :List Bool)
    (hi :SquareSampleCompleteVertices.Valid I c w) (hj :SquareSampleCompleteVertices.Valid J c w)
    (u :ℕ→ℝ) (H :∀i :Fin (I.count c),(SquareSampleCompleteVertices.candidate I c w hi).val i=u i.val) :
    ∀i :Fin (J.count c),(SquareSampleCompleteVertices.candidate J c w hj).val i=u i.val:=by
  cases h
  exact H

theorem seed_candidates (c w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false) c w)
    (u :ℕ→ℝ)
    (HJ :∀i :Fin (IntegralFramedPhysicalSquare.count
        (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters
        (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).plan
        ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).key c)),
      IntegralFramedPhysicalSquare.joint
        (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters
        (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).plan
        (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).data
        (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).nodes
        (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).factor
        (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).seed
        (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).bounds
        (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).key
        (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).positive c w
        (seed_valid_to_parent hn ht ha hR0 c w hw) i=u i.val) :
    ∀i :Fin ((IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false).count c),
      (SquareSampleCompleteVertices.candidate
        (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false) c w hw).val i=u i.val:=by
  apply candidates_congr (IntegralMixedMarkedReservedParent.input hn ht ha hR0) _
    (seed_input_eq hn ht ha hR0) c w (seed_valid_to_parent hn ht ha hR0 c w hw) hw u
  exact HJ

theorem seed_native_dimension (old :List Bool) :
    (B).parameters.ambient (pairFst ((B).key (CTX old)))=(P).ambient (preparedRoot hn ht ha hR0 old):=by
  rw [IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0),
    IntegralMixedRoadmapSeedMetadata.context,pairFst_pair]
  unfold IntegralMixedPhysicalMarkedPlan.bank
  rfl

noncomputable def seedNativePoint (old :List Bool)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ) :
    Fin ((B).parameters.ambient (pairFst ((B).key (CTX old)))+1)→ℝ:=
  fun i=>p (Fin.cast (congrArg (·+1) (seed_native_dimension hn ht ha hR0 old)) i)

private theorem block_column_lt (old :List Bool)
    (a :ℕ) (ha0 :a<IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old))
    (i :Fin ((B).parameters.ambient (pairFst ((B).key (CTX old)))+1)) :
    prefixArity (B).parameters T (pair ((B).key (CTX old))
      (List.replicate (number n (preparedRoot hn ht ha hR0 old)+8+a) true))+i.val<
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false).count (CTX old):=by
  have HC:=IntegralMixedRoadmapSeedMetadata.critical_active hn ht ha hR0 old a ha0
  have HL:=IntegralMixedFramedPointEqualityBits.column_lt (B).parameters T
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) (fun _=>i.val)
    IntegralFramedPhysicalCriticalGuardScan.stage
    (pair (CTX old) (List.replicate (number n (preparedRoot hn ht ha hR0 old)+8+a) true)) HC
    (by simpa only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair] using i.isLt)
  have HE:=IntegralMixedPhysicalGuardScan.count_eq hn ht ha (radius_binary hR0) false (CTX old)
    (List.replicate (number n (preparedRoot hn ht ha hR0 old)+8+a) true)
  simpa only [IntegralMixedFramedPointEqualityBits.column,IntegralMixedFramedCriticalGuardBits.packet,
    IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
    pairFst_pair,pairSnd_pair,List.length_replicate] using HL.trans_eq HE

private theorem native_physical_power (old :List Bool) (a :ℕ) :
    IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters (B).key
      (fun _=>number n (preparedRoot hn ht ha hR0 old)+8+a) (CTX old)=
    UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot hn ht ha hR0 old)+1)
      (2^(P).width (preparedRoot hn ht ha hR0 old)) (number n (preparedRoot hn ht ha hR0 old)+8+a):=by
  unfold IntegralMixedFramedCriticalGuardBits.physicalPower
  rw [IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0),
    IntegralMixedRoadmapSeedMetadata.context,pairFst_pair]
  unfold IntegralMixedPhysicalMarkedPlan.bank
  rfl

theorem geometricPoint_of_columns (old w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false) (CTX old) w)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ) (u :ℕ→ℝ)
    (HJ :∀i :Fin ((IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false).count (CTX old)),
      (SquareSampleCompleteVertices.candidate
        (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false) (CTX old) w hw).val i=u i.val)
    (HB :∀k :Fin (seedSelections hn ht ha hR0 old).length,∀i,
      u (arity (seedOlder hn ht ha hR0 old)+(2*(P).ambient (preparedRoot hn ht ha hR0 old)+4)*
        ((seedSelections hn ht ha hR0 old).length-1-k.val)+i.val)^
        UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot hn ht ha hR0 old)+1)
          (2^(P).width (preparedRoot hn ht ha hR0 old))
          ((seedOlder hn ht ha hR0 old).length+((seedSelections hn ht ha hR0 old).length-1-k.val))=p i)
    (a :ℕ) (ha0 :a<IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old)) :
    IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (CTX old) w hw (number n (preparedRoot hn ht ha hR0 old)+8+a)=seedNativePoint hn ht ha hR0 old p:=by
  funext i
  have HS:=seed_length hn ht ha hR0 old
  let k :Fin (seedSelections hn ht ha hR0 old).length:=
    ⟨(seedSelections hn ht ha hR0 old).length-1-a,by omega⟩
  let j :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1):=
    Fin.cast (congrArg (·+1) (seed_native_dimension hn ht ha hR0 old)) i
  have HE :(seedSelections hn ht ha hR0 old).length-1-k.val=a:=by dsimp only [k];omega
  have HBlock:=HB k j
  rw [HE,seed_older_arity,seed_older_length] at HBlock
  have HP:=IntegralMixedRoadmapSeedMetadata.prefix_arity hn ht ha hR0 old a ha0.le
  rw [←prepared_dimension hn ht ha hR0 old] at HP
  have HC:=block_column_lt hn ht ha hR0 old a ha0 i
  unfold IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalPointEquality.block
  rw [dite_eq_left HC]
  have HVal:=HJ ⟨_,HC⟩
  have HPO:=native_physical_power hn ht ha hR0 old a
  have HF :u (prefixArity (B).parameters T (pair ((B).key (CTX old))
      (List.replicate (number n (preparedRoot hn ht ha hR0 old)+8+a) true))+i.val)^
      IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters (B).key
        (fun _=>number n (preparedRoot hn ht ha hR0 old)+8+a) (CTX old)=
      seedNativePoint hn ht ha hR0 old p i:=by
    rw [HP,HPO]
    exact HBlock
  exact (congrArg (fun v:ℝ=>v^IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters
    (B).key (fun _=>number n (preparedRoot hn ht ha hR0 old)+8+a) (CTX old)) HVal).trans HF

end LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
