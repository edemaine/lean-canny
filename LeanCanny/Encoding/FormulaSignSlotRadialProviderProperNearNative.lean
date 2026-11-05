module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowQuery
public import LeanCanny.Encoding.IntegralFramedPhysicalNearGuard
public import LeanCanny.Encoding.IntegralFramedZeroTarskiStatisticSpace
public import LeanCanny.Encoding.IntegralFramedZeroTarskiStatisticValue
/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Native provider Near and zero-parameter midpoint statistic machines

Every query uses its literal prepared ordinary or mean-centered cut root.
Its full word is an independent argument, never a copied ordinal word.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "A"=>FormulaSignSlotRadialProviderRecordPlan.bank_access
local notation "T"=>FormulaSignSlotRadialProviderRecordPlan.tables
local notation "hT"=>FormulaSignSlotRadialProviderRecordPlan.tables_native
local notation "hr"=>FormulaSignSlotRadialProviderAtomic.bank_represents
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank_access
  FormulaSignSlotRadialProviderRecordPlan.tables IntegralMixedFramedHistoryFamilyBits.family
  dimension initial parent terminal FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial

noncomputable def count (mean : Bool) (z : List Bool):=
  (IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data (terminal mean z)).count
theorem count_unary (mean : Bool) : UnaryFn (count mean):=
  (IntegralMixedFramedBankSnapshotBits.count_unary (B).parameters (A).parameters (B).plan (B).data).comp
    (terminal_FP mean)

noncomputable def pointProducer (mid : Bool) (z : List Bool):=if mid then
  IntegralMixedRoadmapProper.midProducer (dimension z) (initial z) (atomic z) (coordinate z)
  else IntegralMixedRoadmapProper.childProducer (dimension z) (initial z) (atomic z) (coordinate z)

theorem pointProducer_binary (mid : Bool) : BinaryFn (pointProducer mid):=by
  have HM:=((IntegralMixedRoadmapProper.midFirst_unary (FormulaSignSlotRadialProviderAtomic.dimension_unary)
    (FormulaSignSlotRadialProviderAtomic.initial_unary)).comp atomic_FP)
  have HC:=((IntegralMixedRoadmapAtomic.first_unary (FormulaSignSlotRadialProviderAtomic.dimension_unary)
    (FormulaSignSlotRadialProviderAtomic.initial_unary)).comp atomic_FP)
  have HM' : UnaryFn (fun z=>IntegralMixedRoadmapProper.midFirst (dimension z)
      (initial z) (atomic z)):=by
    simpa only [dimension,initial] using HM
  have HC' : UnaryFn (fun z=>IntegralMixedRoadmapAtomic.first (dimension z)
      (initial z) (atomic z)):=by
    simpa only [dimension,initial] using HC
  have HJ:=((BinaryFn.ofUnary (dimension_unary)).sub coordinate_binary)
  cases mid
  · change BinaryFn (fun z=>IntegralMixedRoadmapAtomic.first (dimension z)
      (initial z) (atomic z)+(dimension z-coordinate z))
    exact (BinaryFn.ofUnary HC').add HJ
  · change BinaryFn (fun z=>IntegralMixedRoadmapProper.midFirst (dimension z)
      (initial z) (atomic z)+(dimension z-coordinate z))
    exact (BinaryFn.ofUnary HM').add HJ

noncomputable def pointIndex (mean mid : Bool) (z : List Bool):=count mean z-1-pointProducer mid z
noncomputable def centerIndex (right : Bool) (z : List Bool):=count false z-1-oldProducer right z

theorem pointIndex_binary (mean mid : Bool) : BinaryFn (pointIndex mean mid):=
  ((BinaryFn.ofUnary (count_unary mean)).sub (BinaryFn.const 1)).sub (pointProducer_binary mid)
theorem centerIndex_binary (right : Bool) : BinaryFn (centerIndex right):=
  ((BinaryFn.ofUnary (count_unary false)).sub (BinaryFn.const 1)).sub (oldProducer_binary right)

theorem metadata : IntegralMixedVirtualQueryBits.InputMetadata
    (IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data) :=IntegralMixedFramedPhysicalBits.virtualInputMetadata (B).parameters (A).parameters
  (B).plan (B).data T hT hr

theorem sampler_access (mean : Bool) :
    (IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (terminal mean) (positive mean)).Access :=
  IntegralFramedPhysicalSquare.native_access (B).parameters (A).parameters (B).plan (B).data T hT hr
    (B).nodes (B).factor (B).seed (B).bounds (A).nodes (A).factor (A).seed
    (terminal mean) (terminal_FP mean) (positive mean)
    (A).liftedData (A).controls (A).bounds

noncomputable def nearLanguage (right : Bool) : Language:=IntegralFramedPhysicalNear.guarded
  (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
  (parent false) (terminal false)
  (centerIndex right) (pointIndex false false) (positive false)
  (FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive)
  (FormulaSignSlotRadialProviderAtomic.Cuts.fallback) right

theorem near_decider (right : Bool) : SpaceDecider (nearLanguage right):=
  IntegralFramedPhysicalNear.guarded_decider (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (parent false) (terminal false)
    (centerIndex right) (pointIndex false false) (positive false)
    (A).parameters (A).nodes (A).factor (A).seed (metadata)
    (FormulaSignSlotRadialProviderAtomic.Cuts.probeControls)
    (FormulaSignSlotRadialProviderAtomic.Cuts.probeBounds)
    (A).liftedData (A).controls (A).bounds T hT hr
    (parent_FP false) (terminal_FP false)
    (centerIndex_binary right) (pointIndex_binary false false)
    (sampler_access false)
    (FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive)
    (FormulaSignSlotRadialProviderAtomic.Cuts.fallback) right

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Five actual zero-parameter statistics check a captured midpoint rank

The mean-centered source is queried at eta zero, with the captured MID
coordinate as epsilon-window center. The integer rank is the outer datum.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "A"=>FormulaSignSlotRadialProviderRecordPlan.bank_access
local notation "T"=>FormulaSignSlotRadialProviderRecordPlan.tables
local notation "hT"=>FormulaSignSlotRadialProviderRecordPlan.tables_native
local notation "hr"=>FormulaSignSlotRadialProviderAtomic.bank_represents
local notation "hf"=>FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive
local notation "hd"=>FormulaSignSlotRadialProviderAtomic.Cuts.fallback
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank_access
  FormulaSignSlotRadialProviderRecordPlan.tables IntegralMixedFramedHistoryFamilyBits.family
  parent terminal pointIndex IntegralFramedZeroTarskiStatistic.value

noncomputable def zeroStatistic (power : Fin 3) (negative : Bool):=IntegralFramedZeroTarskiStatistic.value
  (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
  (parent true) (terminal true) (pointIndex true true)
  (positive true) hf hd power negative

theorem zeroStatistic_evaluator (power : Fin 3) (negative : Bool) :
    SpaceFunction (fun u=>SignStatisticBits.integerCode (zeroStatistic power negative u)):=
  IntegralFramedZeroTarskiStatistic.evaluator (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (parent true) (terminal true) (pointIndex true true)
    (positive true) (A).parameters (A).nodes (A).factor (A).seed (metadata)
    (FormulaSignSlotRadialProviderAtomic.Cuts.probeControls)
    (FormulaSignSlotRadialProviderAtomic.Cuts.probeBounds)
    (A).liftedData (A).controls (A).bounds T hT hr
    (parent_FP true) (terminal_FP true) (pointIndex_binary true true)
    (sampler_access true) hf hd power negative

noncomputable def rankPacket (u : List Bool):=OrderedWindowStatisticBits.pack (pairSnd u)
  (SignStatisticBits.integerCode (zeroStatistic 0 false (IntegralFramedPhysicalNear.reset u)))
  (SignStatisticBits.integerCode (zeroStatistic 2 false (IntegralFramedPhysicalNear.reset u)))
  (SignStatisticBits.integerCode (zeroStatistic 1 false (IntegralFramedPhysicalNear.reset u)))
  (SignStatisticBits.integerCode (zeroStatistic 2 true (IntegralFramedPhysicalNear.reset u)))
  (SignStatisticBits.integerCode (zeroStatistic 1 true (IntegralFramedPhysicalNear.reset u)))

theorem rankPacket_evaluator : SpaceFunction (rankPacket):=by
  have E (p : Fin 3) (negative : Bool):=(zeroStatistic_evaluator p negative).precompose
    IntegralFramedPhysicalNear.reset IntegralFramedPhysicalNear.reset_FP
  exact (SpaceFunction.ofFP pairSnd pairSnd_mem_FP).pairOutputs ((E 0 false).pairOutputs
    ((E 2 false).pairOutputs ((E 1 false).pairOutputs ((E 2 true).pairOutputs (E 1 true)))))

noncomputable def RankAccept (u : List Bool):=OrderedWindowStatisticBits.Accept (rankPacket u)
noncomputable def rankLanguage : Language:={u |
  IntegralFramedPhysicalNear.Metadata (B).parameters (B).plan (B).data (parent true)
    (terminal true) (pointIndex true true) (pointIndex true true) (pairFst (pairFst u)) ∧
  SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (terminal true) (positive true))
      (pairFst (pairFst u)) (pairSnd (pairFst u)) ∧ RankAccept u}

theorem rank_decider : SpaceDecider (rankLanguage):=by
  have HM:=SpaceFunction.ofFP _ ((IntegralFramedPhysicalNear.metadata_FP (B).parameters (B).plan (B).data
    (parent true) (terminal true) (pointIndex true true)
    (pointIndex true true) (A).parameters (parent_FP true) (terminal_FP true)
    (pointIndex_binary true true) (pointIndex_binary true true)).comp
      (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).flag_mem_FP
  have HV:=((SquareSampleCompleteVertices.decider (sampler_access true)).flagEvaluator).precompose pairFst pairFst_mem_FP
  have HR:=(rankPacket_evaluator).postcompose
    (fun q=>[decide (OrderedWindowStatisticBits.Accept q)]) OrderedWindowStatisticBits.accept_fppred.flag_mem_FP
  apply (HM.andFlags (HV.andFlags HR)).decider (fun q=>decide (q=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro u
  simp only [Function.comp_apply,RankAccept,rankLanguage,SquareSampleCompleteVertices.language,
    Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
