/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPrefix
public import LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionSemantics
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalPoint
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalScanSemantics
/-! # Actual new-column readbacks for a retained-endpoint extension -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "DIM"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedPhysicalPointCompanionScan.geometricPoint
  IntegralMixedPhysicalPointCompanionScan.retained IntegralMixedPhysicalFieldEquality.point

noncomputable def context (old : List Bool) (e : ℕ):=pair (preparedRoot hn ht ha hR0 old e) []
noncomputable def beginBirth (old : List Bool):=IntegralMixedRoadmapAtomic.endBirth (DIM old) (N old) old
noncomputable def finishBirth (old : List Bool) (e : ℕ):=
  IntegralMixedRoadmapAtomic.endBirth (DIM old) (N old) (packet (DIM old) old e [])
noncomputable def fullBirth (old : List Bool) (e : ℕ):=
  number n (preparedRoot hn ht ha hR0 old e)+8+
    IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old e)

local notation "CTX"=>context hn ht ha hR0

/-- The meaningful new level uses `p`; its remaining padding and final probe
use `p0`. These are equations for the new word's own physical columns and
chronological scalar fields, without an assumed native scan. -/
structure FreshReadback (old : List Bool) (e : ℕ) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old e) w)
    (p p0 : Fin ((P).ambient (pairFst ((B).key (CTX old e)))+1)→ℝ) : Prop where
  physical : ∀b,beginBirth hn ht ha hR0 old≤b→b<fullBirth hn ht ha hR0 old e→
    IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (CTX old e) w hw b=if b<finishBirth hn ht ha hR0 old e then p else p0
  scalar : ∀b,beginBirth hn ht ha hR0 old≤b→b<fullBirth hn ht ha hR0 old e→
    ∀hb : IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) b,
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX old e) w hw b=
        (if b<finishBirth hn ht ha hR0 old e then p else p0)
          ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e) b,
            IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩

theorem prefix_length (old : List Bool) (e : ℕ) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (CTX old e))=
      fullBirth hn ht ha hR0 old e:=by
  have HC:=IntegralMixedPhysicalFieldEquality.count_eq hn ht ha (radius_binary hR0) (CTX old e)
  have HO : IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst (CTX old e))=
      fullBirth hn ht ha hR0 old e:=by
    rw [context,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
    rfl
  exact (IntegralMixedFramedHistoryFamilyBits.family_birth P (B).plan (B).data ((B).key (CTX old e))).symm.trans
    (HC.trans HO)

theorem critical_of_fresh_readback (old : List Bool) (e : ℕ) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old e) w)
    (p p0 : Fin ((P).ambient (pairFst ((B).key (CTX old e)))+1)→ℝ)
    (hr : FreshReadback hn ht ha hR0 old e w hw p p0)
    (b : ℕ) (hb0 : beginBirth hn ht ha hR0 old≤b) (hb1 : b<fullBirth hn ht ha hR0 old e)
    (hb : IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) b) :
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false (CTX old e) w hw b hb=
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
        (CTX old e) w hw b
          ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e) b,
            IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩ :=by
  rw [hr.physical b hb0 hb1]
  exact (IntegralMixedPhysicalFieldEquality.retained_point hn ht ha (radius_binary hR0)
    (CTX old e) w hw b hb).trans (hr.scalar b hb0 hb1 hb)

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
