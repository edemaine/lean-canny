/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicCutTest
public import LeanCanny.Encoding.IntegralFramedTraceCutTask

/-! # Ordinary and mean-centered queries replace only the reserved last record

Input: pair atomicVertex globalCoordinateBits. Both queries retain the
literal OLD or EXTERNAL provider and all older raw bytes. Their complete words must be allocated
at their own new roots; no sampler word is copied by these writers.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def atomic (z : List Bool):=pairFst z
def coordinate (z : List Bool):=Nat.fromBitsLE (pairSnd z)
def oldPacket (z : List Bool):=IntegralMixedRoadmapProper.badPacket (atomic z)
def labels (z : List Bool):=IntegralMixedRoadmapProper.labels (atomic z)
def offset (z : List Bool):=IntegralMixedRoadmapProper.levelIndex (atomic z)+1
def relativeCoordinate (z : List Bool):=coordinate z-offset z
def oldProducer (right : Bool) (z : List Bool):=IntegralMixedRoadmapProper.producer right (atomic z)

theorem atomic_FP : atomic∈FP:=pairFst_mem_FP
theorem coordinate_binary : BinaryFn coordinate:=BinaryFn.fromBits pairSnd_mem_FP
theorem oldPacket_FP : oldPacket∈FP:=mem_FP_comp atomic_FP IntegralMixedRoadmapProper.badPacket_FP
theorem labels_FP : labels∈FP:=mem_FP_comp atomic_FP IntegralMixedRoadmapProper.labels_FP
theorem offset_unary : UnaryFn offset:=
  (IntegralMixedRoadmapProper.levelIndex_unary.comp atomic_FP).add (UnaryFn.const 1)
theorem oldProducer_binary (right : Bool) : BinaryFn (oldProducer right):=
  (IntegralMixedRoadmapProper.producer_binary right).comp atomic_FP
theorem relativeCoordinate_binary : BinaryFn relativeCoordinate:=coordinate_binary.sub (BinaryFn.ofUnary offset_unary)

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderRecordPlan.bank

noncomputable def dimension (z : List Bool):=FormulaSignSlotRadialProviderAtomic.dimension (atomic z)
noncomputable def initial (z : List Bool):=FormulaSignSlotRadialProviderAtomic.initial (atomic z)
noncomputable def creating (z : List Bool):=IntegralMixedRoadmapBadProbePacket.creating (initial z) (oldPacket z)
theorem dimension_unary : UnaryFn (dimension):=
  (FormulaSignSlotRadialProviderAtomic.dimension_unary).comp atomic_FP
theorem initial_unary : UnaryFn (initial):=
  (FormulaSignSlotRadialProviderAtomic.initial_unary).comp atomic_FP
theorem creating_unary : UnaryFn (creating):=
  IntegralMixedRoadmapBadProbePacket.creating_unary (initial_unary) oldPacket_FP

attribute [local irreducible] dimension initial creating oldProducer atomic
  IntegralMixedChronologicalMeanCutCode.code IntegralMixedChronologicalCutCode.code

noncomputable def code (mean : Bool) (z : List Bool):=if mean then
  IntegralMixedChronologicalMeanCutCode.code (dimension z) (labels z)
    (oldProducer false z) (oldProducer true z)
    (offset z) (coordinate z) 0 0 0
  else IntegralMixedChronologicalCutCode.code (dimension z) (labels z)
    (offset z) (coordinate z) 0 0 0

theorem code_FP (mean : Bool) : code mean∈FP:=by
  have HG:=BinaryFn.ofUnary offset_unary
  have HA : BinaryFn (oldProducer false):=oldProducer_binary false
  have HB : BinaryFn (oldProducer true):=oldProducer_binary true
  cases mean
  · change (fun z=>IntegralMixedChronologicalCutCode.code (dimension z) (labels z)
      (offset z) (coordinate z) 0 0 0)∈FP
    exact IntegralMixedChronologicalCutCode.code_FP (dimension_unary) HG coordinate_binary
      (BinaryFn.const 0) (BinaryFn.const 0) (BinaryFn.const 0) labels_FP
  · change (fun z=>IntegralMixedChronologicalMeanCutCode.code (dimension z) (labels z)
      (oldProducer false z) (oldProducer true z)
      (offset z) (coordinate z) 0 0 0)∈FP
    exact IntegralMixedChronologicalMeanCutCode.code_FP
      (n:=dimension)
      (a:=oldProducer false)
      (b:=oldProducer true)
      (g:=offset) (j:=coordinate) (tag:=fun _=>0) (choice:=fun _=>0) (degree:=fun _=>0) (labels:=labels)
      (dimension_unary) HA HB HG coordinate_binary
      (BinaryFn.const 0) (BinaryFn.const 0) (BinaryFn.const 0) labels_FP

attribute [local irreducible] code

noncomputable def raw (mean : Bool) (z : List Bool):=WordList.encode
  (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)++[code mean z])
noncomputable def root (mean : Bool) (z : List Bool):=pair
  (FormulaSignSlotRadialProviderAtomic.provider (atomic z)) (pair (raw mean z) [])
noncomputable def context (mean : Bool) (z : List Bool):=pair (root mean z) []

theorem raw_FP (mean : Bool) : raw mean∈FP:=by
  apply mem_FP_of_eq (appendFn_mem_FP
    (mem_FP_comp oldPacket_FP IntegralMixedRoadmapBadProbePacket.prefixWord_FP)
    (mem_FP_pair (code_FP mean) (constFn_mem_FP [])))
  intro z
  simp only [raw,IntegralMixedRoadmapBadProbePacket.prefixWord,
    IntegralMixedRoadmapLevel.encode_append,WordList.encode,Function.comp_apply]
theorem root_FP (mean : Bool) : root mean∈FP:=mem_FP_pair
  (mem_FP_comp atomic_FP FormulaSignSlotRadialProviderAtomic.provider_FP)
  (mem_FP_pair (raw_FP mean) (constFn_mem_FP []))
theorem context_FP (mean : Bool) : context mean∈FP:=
  mem_FP_pair (root_FP mean) (constFn_mem_FP [])

local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "A"=>FormulaSignSlotRadialProviderRecordPlan.bank_access
noncomputable def terminal (mean : Bool) : List Bool→List Bool:=(B).key∘context mean
noncomputable def base (mean : Bool) (z : List Bool):=RankedHistoryTask.pack (root mean z) 0 0 []
noncomputable def parent (mean : Bool) : List Bool→List Bool:=IntegralMixedRoutineContextQuery.query (B).parameters
  (base mean) (creating) .rawFactor .companion relativeCoordinate (fun _=>2)

theorem terminal_FP (mean : Bool) : terminal mean∈FP:=mem_FP_comp
  (context_FP mean) (A).key
theorem base_FP (mean : Bool) : base mean∈FP:=mem_FP_pair (root_FP mean) (constFn_mem_FP _)
theorem parent_FP (mean : Bool) : parent mean∈FP:=
  IntegralMixedRoutineContextQuery.query_FP (B).parameters (A).parameters (base mean)
    (base_FP mean) (creating) (BinaryFn.ofUnary (creating_unary))
    .rawFactor .companion relativeCoordinate (fun _=>2) relativeCoordinate_binary (BinaryFn.const 2)

theorem positive (mean : Bool) (z : List Bool) :
    0<(IntegralMixedFramedHistoryFamilyBits.family (B).parameters (B).plan (B).data).birth (terminal mean z):=
  (B).positive (context mean z)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
