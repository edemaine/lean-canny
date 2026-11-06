/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendCriticalScan
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendCompanions
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendBeforeProbe
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPrelude
/-! # A fresh accepted retained child at the prescribed genuine point -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem cast_function_heq {n m : ℕ} (h : n=m) (p : Fin (m+1)→ℝ) :
    HEq (fun i : Fin (n+1)=>p (Fin.cast (congrArg (·+1) h) i)) p := by cases h;rfl

private theorem point_at_context (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input c w)
    (b : ℕ) (hc : FormulaSignSlotRadialProviderAtomic.context q=c)
    (hword : FormulaSignSlotRadialProviderAtomic.word q=w)
    (hb : FormulaSignSlotRadialProviderAtomic.anchor (FormulaSignSlotRadialProviderAtomic.dimension q)
      (FormulaSignSlotRadialProviderAtomic.initial q) q=b) :
    HEq (FormulaSignSlotRadialProviderAtomic.point q hv)
      (FormulaSignSlotRadialProviderAtomic.geometricPoint c w hw b) := by
  cases hc
  cases hword
  cases hb
  rfl

private theorem field_at_context (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input c w)
    (hc : FormulaSignSlotRadialProviderAtomic.context q=c)
    (hword : FormulaSignSlotRadialProviderAtomic.word q=w) (b : ℕ) :
    FormulaSignSlotRadialProviderAtomic.field q hv b=FormulaSignSlotRadialProviderAtomic.bankField c w hw b := by
  cases hc
  cases hword
  rfl

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom parentCommands parentDescriptor

theorem nativePoint_heq (old : List Bool) (e : ℕ)
    (p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ) : HEq (nativePoint old e p) p :=
  cast_function_heq (native_dimension old e) p

variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {e : ℕ} {he : e<endBirth (dimension old) (N old) old}
  {p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ}

theorem WordReceipt.atomic_valid (W : WordReceipt old hv hd e he p) :
    A (packet (dimension old) old e W.word) :=
  ⟨grammar old hv hd e he W.word,W.full_valid,W.before_probe,W.all_critical,
    W.latest_companions,W.marked,W.replay⟩

theorem WordReceipt.point_heq (W : WordReceipt old hv hd e he p)
    (hnew : A (packet (dimension old) old e W.word)) :
    HEq (FormulaSignSlotRadialProviderAtomic.point (packet (dimension old) old e W.word) hnew) p := by
  have HA : FormulaSignSlotRadialProviderAtomic.anchor (dimension (packet (dimension old) old e W.word))
      (N (packet (dimension old) old e W.word)) (packet (dimension old) old e W.word)=
      N old+start old+1+(dimension old-depth old) := by
    change IntegralMixedRoadmapAtomic.anchor (dimension (packet (dimension old) old e W.word))
      (N (packet (dimension old) old e W.word)) (packet (dimension old) old e W.word)=_
    rw [dimension_packet,initial_packet]
    exact latest_anchor_packet old e W.word
  have H := point_at_context (packet (dimension old) old e W.word) hnew (C (preparedRoot old e)) W.word W.valid _
    (context_packet old e W.word) (word_packet _ _ _ _) HA
  have HF := finish_eq old e
  have HB := begin_eq old
  exact H.trans ((heq_of_eq (W.local_geometric_point _ (by omega) (by omega))).trans (nativePoint_heq old e p))

theorem exists_valid_at (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old)
    (p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ)
    (HS : p∈IntegralMixedFrozenFrame.slice (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e))
      (parentDescriptor old hv hd e he).frame (parentValues old hv hd e he))
    (Hh : p (IntegralMixedChronologicalSweepFrame.next (parentDescriptor old hv hd e he)
      (parent_descriptor_fit old hv hd e he))=
        parentValues old hv hd e he (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)))
    (Hgrad : ∀i,i∉insert (IntegralMixedChronologicalSweepFrame.next (parentDescriptor old hv hd e he)
      (parent_descriptor_fit old hv hd e he)) (parentDescriptor old hv hd e he).frame.frozen→
        i≠childCoordinate old hv hd e he→(MvPolynomial.pderiv i
          (FermatCriticalHomogenization.polynomial (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).low
            (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).leading
              (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    ∃q,∃hq : A q,FormulaSignSlotRadialProviderAtomic.provider q=FormulaSignSlotRadialProviderAtomic.provider old ∧
      depth q=depth old+1 ∧ HEq (FormulaSignSlotRadialProviderAtomic.point q hq) p ∧
      ∀b<N old+start old,FormulaSignSlotRadialProviderAtomic.field q hq b=
        FormulaSignSlotRadialProviderAtomic.field old hv b := by
  obtain ⟨W⟩ := exists_word_receipt old hv hd e he p HS Hh Hgrad
  refine ⟨packet (dimension old) old e W.word,W.atomic_valid,provider_packet _ _ _ _,depth_packet _ _ _ _,
    W.point_heq W.atomic_valid,?_⟩
  intro b hb
  exact (field_at_context _ W.atomic_valid (C (preparedRoot old e)) W.word W.valid
    (context_packet old e W.word) (word_packet _ _ _ _) b).trans (W.old_fields b hb)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
