/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendWord
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPhysicalArity
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedNativeReadback
/-! # Every new physical block of the freshly sampled append has its prescribed point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem splice_blocks (dim S B m j c k L :ℕ) (u z :ℕ→ℝ)
    (p p0 :Fin (dim+1)→ℝ)
    (keep :∀i,i<L+(2*dim+4)*j+(2*dim+4)*c→u i=z i)
    (mid :∀a :Fin j,∀i,z (L+(2*dim+4)*(j-1-a.val)+i.val)^
      UniformIntegralPowerSchedule.physical S (2^B) (m+(j-1-a.val))=p i)
    (child :∀a :Fin c,∀i,z (L+(2*dim+4)*j+(2*dim+4)*(c-1-a.val)+i.val)^
      UniformIntegralPowerSchedule.physical S (2^B) (m+j+(c-1-a.val))=p i)
    (pad :∀a :Fin k,∀i,u (L+(2*dim+4)*j+(2*dim+4)*c+(2*dim+4)*(k-1-a.val)+i.val)^
      UniformIntegralPowerSchedule.physical S (2^B) (m+j+c+(k-1-a.val))=p0 i)
    (b :ℕ) (hb0 :m≤b) (hb1 :b<m+j+c+k) (i :Fin (dim+1)):
    u (L+(2*dim+4)*(b-m)+i.val)^UniformIntegralPowerSchedule.physical S (2^B) b=
      if b<m+j+c then p i else p0 i:=by
  by_cases hm :b<m+j
  · let a :Fin j:=⟨j-1-(b-m),by omega⟩
    have HA :j-1-a.val=b-m:=by dsimp only [a];omega
    have HB :m+(b-m)=b:=by omega
    have HI :L+(2*dim+4)*(b-m)+i.val<L+(2*dim+4)*j+(2*dim+4)*c:=by
      have HM:=Nat.mul_le_mul_left (2*dim+4) (show b-m+1≤j from by omega)
      nlinarith [i.isLt]
    rw [keep _ HI,ite_eq_left (by omega)]
    simpa only [HA,HB] using mid a i
  · by_cases hc :b<m+j+c
    · let a :Fin c:=⟨c-1-(b-m-j),by omega⟩
      have HA :c-1-a.val=b-m-j:=by dsimp only [a];omega
      have HB :m+j+(b-m-j)=b:=by omega
      have HD :b-m=j+(b-m-j):=by omega
      have HI :L+(2*dim+4)*(b-m)+i.val<L+(2*dim+4)*j+(2*dim+4)*c:=by
        have HM:=Nat.mul_le_mul_left (2*dim+4) (show b-m-j+1≤c from by omega)
        rw [HD,Nat.mul_add]
        nlinarith [i.isLt]
      rw [keep _ HI,ite_eq_left hc]
      have H:=child a i
      rw [HA,HB] at H
      rw [HD,Nat.mul_add]
      simpa only [Nat.mul_add,Nat.add_assoc] using H
    · let a :Fin k:=⟨k-1-(b-m-j-c),by omega⟩
      have HA :k-1-a.val=b-m-j-c:=by dsimp only [a];omega
      have HB :m+j+c+(b-m-j-c)=b:=by omega
      have HD :b-m=j+c+(b-m-j-c):=by omega
      rw [ite_eq_right hc]
      have H:=pad a i
      rw [HA,HB] at H
      rw [HD,Nat.mul_add]
      simpa only [Nat.mul_add,Nat.add_assoc] using H

private theorem cast_point_heq {a b :ℕ} (h:a=b) (p :Fin b→ℝ):
    HEq (fun i:Fin a=>p (Fin.cast h i)) p:=by
  cases h
  rfl

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (e :ℕ) (he :e<IntegralMixedRoadmapAtomic.endBirth
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
local notation "r"=>preparedRoot hn ht ha hR0 old e
local notation "older"=>parentCommands hn ht ha hR0 old hv hd e he
local notation "js"=>midpointSelections hn ht ha hR0 old hv hd e he
local notation "cs"=>childSelections hn ht ha hR0 old hv hd e he
local notation "localCs"=>localInstructions hn ht ha hR0 old hv hd e he
local notation "tailCount"=>seedTailCount hn ht ha hR0 old e
local notation "CTX"=>context hn ht ha hR0 old e

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap preparedRoot parentCommands localInstructions midpointSelections childSelections
  IntegralMixedFramedHistoryFamilyBits.family

theorem local_finish :(localCs).length=finishBirth hn ht ha hR0 old e:=by
  have HL:=local_length hn ht ha hR0 old hv hd e he
  have HM:=midpoint_selection_count hn ht ha hR0 old hv hd e he
  have HC:=child_selection_count hn ht ha hR0 old hv hd e he
  have HB:=parent_length hn ht ha hR0 old hv hd e he
  have HF:=finish_eq hn ht ha hR0 old e
  change (older).length=beginBirth hn ht ha hR0 old at HB
  omega

theorem full_birth_length :fullBirth hn ht ha hR0 old e=(localCs).length+
    (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount).length:=by
  have H:=congrArg List.length (full_local_commands hn ht ha hR0 old hv hd e he)
  rw [IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0 r,List.length_append,List.length_replicate] at H
  rw [IntegralMixedCanonicalPadding.paddingSelections_length]
  change IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r=_
  omega

theorem physical_dimension :(B).parameters.ambient (pairFst ((B).key CTX))=(P).ambient r:=
  (native_dimension hn ht ha hR0 old e).trans (prepared_dimension hn ht ha hR0 old e).symm

noncomputable def nativePoint (p :Fin ((P).ambient r+1)→ℝ):
    Fin ((B).parameters.ambient (pairFst ((B).key CTX))+1)→ℝ:=
  fun i=>p (Fin.cast (congrArg (·+1) (physical_dimension hn ht ha hR0 old e)) i)


theorem nativePoint_heq (p :Fin ((P).ambient r+1)→ℝ):
    HEq (nativePoint hn ht ha hR0 old e p) p:=
  cast_point_heq (congrArg (·+1) (physical_dimension hn ht ha hR0 old e)) p


theorem receipt_block (p p0 :Fin ((P).ambient r+1)→ℝ)
    (W :WordReceipt hn ht ha hR0 old hv hd e he p p0)
    (b :ℕ) (hb0 :beginBirth hn ht ha hR0 old≤b) (hb1 :b<fullBirth hn ht ha hR0 old e)
    (i :Fin ((P).ambient r+1)):
    W.tuple (arity older+(2*(P).ambient r+4)*(b-beginBirth hn ht ha hR0 old)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b=
        if b<finishBirth hn ht ha hR0 old e then p i else p0 i:=by
  have HB :(older).length=beginBirth hn ht ha hR0 old:=parent_length hn ht ha hR0 old hv hd e he
  have HL:=local_length hn ht ha hR0 old hv hd e he
  have HF:=local_finish hn ht ha hR0 old hv hd e he
  have HT:=full_birth_length hn ht ha hR0 old hv hd e he
  have HK :∀a,a<arity older+(2*(P).ambient r+4)*(js).length+(2*(P).ambient r+4)*(cs).length→
      W.tuple a=W.localTuple a:=by
    intro a hi
    exact W.preserved a (hi.trans_eq (local_arity hn ht ha hR0 old hv hd e he).symm)
  have HP:=W.padding_blocks
  rw [local_arity hn ht ha hR0 old hv hd e he,local_length hn ht ha hR0 old hv hd e he] at HP
  have H:=splice_blocks ((P).ambient r) ((P).cap r+1) ((P).width r) (older).length
    (js).length (cs).length (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount).length
    (arity older) W.tuple W.localTuple p p0 HK W.midpoint_blocks W.child_blocks HP b
    (by omega) (by omega) i
  rw [HL.symm.trans HF,HB] at H
  exact H

private theorem physical_column_lt (b :ℕ)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false CTX b)
    (i :Fin ((B).parameters.ambient (pairFst ((B).key CTX))+1)):
    prefixArity (B).parameters T (pair ((B).key CTX) (List.replicate b true))+i.val<(S).count CTX:=by
  have HL:=IntegralMixedFramedPointEqualityBits.column_lt (B).parameters T
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) (fun _=>i.val)
    IntegralFramedPhysicalCriticalGuardScan.stage (pair CTX (List.replicate b true)) hb
    (by simpa only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair] using i.isLt)
  have HE:=IntegralMixedPhysicalGuardScan.count_eq hn ht ha (radius_binary hR0) false CTX
    (List.replicate b true)
  simpa only [IntegralMixedFramedPointEqualityBits.column,IntegralMixedFramedCriticalGuardBits.packet,
    IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
    pairFst_pair,pairSnd_pair,List.length_replicate] using HL.trans_eq HE

private theorem native_physical_power (b :ℕ):
    IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters (B).key (fun _=>b) CTX=
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b:=by
  unfold IntegralMixedFramedCriticalGuardBits.physicalPower
  rw [native_root hn ht ha hR0 old e]
  unfold IntegralMixedPhysicalMarkedPlan.bank
  rfl

theorem physical_of_word_receipt (p p0 :Fin ((P).ambient r+1)→ℝ)
    (W :WordReceipt hn ht ha hR0 old hv hd e he p p0)
    (b :ℕ) (hb0 :beginBirth hn ht ha hR0 old≤b) (hb1 :b<fullBirth hn ht ha hR0 old e):
    IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      CTX W.word W.valid b=
      if b<finishBirth hn ht ha hR0 old e then nativePoint hn ht ha hR0 old e p
        else nativePoint hn ht ha hR0 old e p0:=by
  have HJ:=IntegralMixedRoadmapSeedResampling.seed_candidates hn ht ha hR0 CTX W.word W.valid W.tuple W.joint
  have HActive:=active_after_begin hn ht ha hR0 old hv hd e he b hb0 hb1
  funext i
  let j:=Fin.cast (congrArg (·+1) (physical_dimension hn ht ha hR0 old e)) i
  have HB:=receipt_block hn ht ha hR0 old hv hd e he p p0 W b hb0 hb1 j
  have HA:=prefix_arity_after_begin hn ht ha hR0 old hv hd e he b hb0 hb1.le
  rw [←prepared_dimension hn ht ha hR0 old e] at HA
  have HC:=physical_column_lt hn ht ha hR0 old e b HActive i
  simp only [ite_apply]
  unfold IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalPointEquality.block
  rw [dite_eq_left HC]
  have HV:=HJ ⟨_,HC⟩
  have HP:=native_physical_power hn ht ha hR0 old e b
  have HF :W.tuple (prefixArity (B).parameters T (pair ((B).key CTX) (List.replicate b true))+i.val)^
      IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters (B).key (fun _=>b) CTX=
        if b<finishBirth hn ht ha hR0 old e then nativePoint hn ht ha hR0 old e p i
          else nativePoint hn ht ha hR0 old e p0 i:=by
    rw [HA,HP]
    exact HB
  exact (congrArg (fun v:ℝ=>v^IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters
    (B).key (fun _=>b) CTX) HV).trans HF

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
