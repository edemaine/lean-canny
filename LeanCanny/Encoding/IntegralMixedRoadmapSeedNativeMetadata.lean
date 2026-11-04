/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedHeader
public import LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionSemantics
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualitySemantics
/-! # Actual seed guard metadata uses its fixed original full prefix

All stored stages are the original integer prelude followed by critical
seed records. Physical blocks have their actual oldest-first columns.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralFramedPhysicalCriticalGuardTest (keyDatum)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "DIM" old=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
local notation "ROOT" old=>IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old
local notation "stage"=>IntegralFramedPhysicalCriticalGuardScan.stage
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedAuxiliaryMarkedRecordPlan.plan
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedFramedRootPullback.instructionAt stageHeader
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerSource.source
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus

noncomputable def context (old : List Bool):=pair (ROOT old) []

private theorem stage_packet (c : List Bool) (b : ℕ) :
    IntegralFramedPhysicalCriticalGuardScan.stage (pair c (List.replicate b true))=b :=by
  rw [IntegralFramedPhysicalCriticalGuardScan.stage,pairSnd_pair,List.length_replicate]

private theorem datum_packet (f : List Bool→List Bool) (c : List Bool) (b : ℕ) :
    keyDatum f (pair c (List.replicate b true))=f c :=congrArg f (pairFst_pair _ _)

theorem native_header (old : List Bool) (b : ℕ) :
    IntegralMixedFramedCriticalGuardBits.header T (keyDatum (B).key) stage
      (pair (context hn ht ha hR0 old) (List.replicate b true))=
        stageHeader hn ht ha hR0 (ROOT old) b :=by
  rw [IntegralMixedFramedCriticalGuardBits.header_actual P D H T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false)]
  rw [datum_packet,stage_packet]
  rw [IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0),context,pairFst_pair]
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank stageHeader
  rfl

theorem prefix_length (old : List Bool) : IntegralMixedFramedHistoryFamilyBits.prefixLength P
    ((B).key (context hn ht ha hR0 old))=number n (ROOT old)+8+IntegralMixedCausalRecordPlanBits.count (ROOT old) :=by
  have HC:=IntegralMixedPhysicalFieldEquality.count_eq hn ht ha (radius_binary hR0) (context hn ht ha hR0 old)
  have HO : IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst (context hn ht ha hR0 old))=
      number n (ROOT old)+8+IntegralMixedCausalRecordPlanBits.count (ROOT old):=by
    rw [context,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
  exact (IntegralMixedFramedHistoryFamilyBits.family_birth P D H ((B).key (context hn ht ha hR0 old))).symm.trans
    (HC.trans HO)

theorem prelude_inactive (old : List Bool) (b : ℕ) (hb : b<number n (ROOT old)+8) :
    ¬IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (context hn ht ha hR0 old) b :=by
  intro HB
  have HC:=HB.2
  rw [native_header,prelude_header hn ht ha hR0 _ _ hb] at HC
  cases HC

theorem critical_active (old : List Bool) (a : ℕ) (ha0 : a<IntegralMixedCausalRecordPlanBits.count (ROOT old)) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false
      (context hn ht ha hR0 old) (number n (ROOT old)+8+a) :=by
  constructor
  · rw [datum_packet,stage_packet]
    rw [prefix_length]
    omega
  · rw [native_header,seed_header hn ht ha hR0 old a ha0]

theorem critical_selected (old : List Bool) (a : ℕ) (ha0 : a<IntegralMixedCausalRecordPlanBits.count (ROOT old)) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
      (context hn ht ha hR0 old) (number n (ROOT old)+8+a)=selected (DIM old) a :=by
  unfold IntegralMixedPhysicalPointCompanionScan.selected
  rw [native_header,seed_header hn ht ha hR0 old a ha0]
  exact Nat.zero_add _

private theorem header_packet (TT : IntegralMixedHeaderTablesBits.Tables) (f : List Bool→List Bool)
    (c : List Bool) (b : ℕ) : IntegralMixedFramedCriticalGuardBits.header TT (keyDatum f) stage
      (pair c (List.replicate b true))=IntegralMixedCommandHeaderBits.lookup (TT.commands (pairFst (f c))) b :=by
  rw [IntegralMixedFramedCriticalGuardBits.header,datum_packet,stage_packet]

theorem native_span (old : List Bool) (b : ℕ) :
    IntegralMixedFramedPhysicalIndex.span P T (pair ((B).key (context hn ht ha hR0 old)) (List.replicate b true))=
      if (stageHeader hn ht ha hR0 (ROOT old) b).context=1 then
        IntegralMixedFramedPhysicalIndex.block (DIM old)+1 else 1 :=by
  have HH:=native_header hn ht ha hR0 old b
  rw [header_packet] at HH
  unfold IntegralMixedFramedPhysicalIndex.span
  simp only [pairFst_pair,pairSnd_pair,List.length_replicate]
  rw [HH,IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0),context,pairFst_pair]
  have HD : (P).ambient (ROOT old)=DIM old:=by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    exact dimension_root hn ht ha hR0 old
  rw [HD]

private theorem prefix_succ (PP : Parameters) (TT : IntegralMixedHeaderTablesBits.Tables) (key : List Bool) (b : ℕ) :
    IntegralMixedFramedPhysicalIndex.prefixArity PP TT (pair key (List.replicate (b+1) true))=
      IntegralMixedFramedPhysicalIndex.prefixArity PP TT (pair key (List.replicate b true))+
        IntegralMixedFramedPhysicalIndex.span PP TT (pair key (List.replicate b true)) :=by
  simp only [IntegralMixedFramedPhysicalIndex.prefixArity,pairFst_pair,pairSnd_pair,
    List.length_replicate,Finset.sum_range_succ]

theorem prefix_arity (old : List Bool) (a : ℕ) (ha0 : a≤IntegralMixedCausalRecordPlanBits.count (ROOT old)) :
    IntegralMixedFramedPhysicalIndex.prefixArity P T
      (pair ((B).key (context hn ht ha hR0 old)) (List.replicate (number n (ROOT old)+8+a) true))=
        number n (ROOT old)+8+(2*(DIM old)+4)*a :=by
  induction a with
  | zero=>
    simp only [Nat.add_zero,Nat.mul_zero]
    unfold IntegralMixedFramedPhysicalIndex.prefixArity
    simp only [pairFst_pair,pairSnd_pair,List.length_replicate]
    have HE : ∀j∈Finset.range (number n (ROOT old)+8),
        IntegralMixedFramedPhysicalIndex.span P T
          (pair ((B).key (context hn ht ha hR0 old)) (List.replicate j true))=1:=by
      intro j hj
      rw [native_span,prelude_header hn ht ha hR0 _ _ (Finset.mem_range.mp hj)]
      rfl
    rw [Finset.sum_congr rfl HE]
    simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.mul_one]
  | succ a ih=>
    have Hlt : a<IntegralMixedCausalRecordPlanBits.count (ROOT old):=by omega
    rw [show number n (ROOT old)+8+(a+1)=(number n (ROOT old)+8+a)+1 by omega,
      prefix_succ,ih (by omega),native_span,seed_header hn ht ha hR0 old a Hlt]
    simp only [IntegralMixedFramedPhysicalIndex.block,ite_true]
    ring

end LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata
