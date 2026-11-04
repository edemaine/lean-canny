/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedJointFieldReadback
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendWindows
/-! # Chronological scalar readback of the sampled proper-append word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
open IntegralMixedFramedPhysicalIndex (arity)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "localCs"=>compiledProgram hn ht ha hR0 old hv hd left right R side
local notation "tailCount"=>seedTailCount hn ht ha hR0 old hv hd left right R side
local notation "CTX"=>pair r []

local notation "C"=>canonicalObservation hn ht ha hR0 old hv hd left right R side
local notation "pads"=>IntegralMixedCanonicalPadding.paddingSelections (Parameters.ambient (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)) r) tailCount
local notation "FB"=>fullBirth hn ht ha hR0 old hv hd left right R side
local notation "finish"=>finishBirth hn ht ha hR0 old hv hd left right R side
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  preparedRoot compiledProgram canonicalObservation seedTailCount
  IntegralMixedMarkedPrefixFieldReadback.fullObservation IntegralMixedPhysicalFieldEquality.point

private theorem scalar_clock :FB=(localCs).length+(pads).length:=by
  rw [full_birth hn ht ha hR0 old hv hd left right R side,
    compiled_program_length hn ht ha hR0 old hv hd left right R side]
  simp only [IntegralMixedCanonicalPadding.paddingSelections,List.length_replicate]

theorem WordReceipt.field {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (b :ℕ) (hb :b<FB):
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid b=
      IntegralMixedPointCompanion.values p0 (fun j :Fin (localCs).length=>(C).point z j.val) pads
        ⟨FB-1-b,by rw [←scalar_clock hn ht ha hR0 old hv hd left right R side];omega⟩:=by
  have HF:=IntegralMixedMarkedJointFieldReadback.field_observation hn ht ha hR0 r W.word W.valid
    W.tuple W.joint b hb
  exact HF.trans (W.values ⟨FB-1-b,by rw [←scalar_clock hn ht ha hR0 old hv hd left right R side];omega⟩)

theorem WordReceipt.local_field {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (b :ℕ) (hb :b<finish):
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid b=
      (C).point z ((localCs).length-1-b):=by
  have HL:=compiled_program_length hn ht ha hR0 old hv hd left right R side
  have HF:=scalar_clock hn ht ha hR0 old hv hd left right R side
  have H:=W.field hn ht ha hR0 old hv hd left right R side b (by omega)
  let i :Fin (localCs).length:=⟨(localCs).length-1-b,by omega⟩
  have HE :FB-1-b=(pads).length+i.val:=by dsimp only [i];omega
  have HI :(⟨FB-1-b,by omega⟩ :Fin ((localCs).length+(pads).length))=
      ⟨(pads).length+i.val,by omega⟩:=Fin.ext HE
  exact H.trans ((congrArg
    (IntegralMixedPointCompanion.values p0 (fun j :Fin (localCs).length=>(C).point z j.val) pads) HI).trans
      (IntegralMixedPointCompanion.values_old p0 (fun j :Fin (localCs).length=>(C).point z j.val) pads i))

theorem WordReceipt.padding_field {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (b :ℕ) (hb0 :finish≤b) (hb1 :b<FB):
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid b=p0 0:=by
  have HL:=compiled_program_length hn ht ha hR0 old hv hd left right R side
  have HF:=scalar_clock hn ht ha hR0 old hv hd left right R side
  have H:=W.field hn ht ha hR0 old hv hd left right R side b hb1
  let j :Fin (pads).length:=⟨FB-1-b,by omega⟩
  apply H.trans
  apply (IntegralMixedPointCompanion.values_get p0 (fun j :Fin (localCs).length=>(C).point z j.val) pads j).trans
  apply congrArg p0
  simp only [IntegralMixedCanonicalPadding.paddingSelections,List.get_eq_getElem,List.getElem_replicate,
    IntegralMixedCanonicalPadding.zeroFree]

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
