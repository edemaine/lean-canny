/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalReadback
public import LeanCanny.Geometry.IntegralMixedFramedCriticalAnchor
/-! # Active full-vertex critical anchors need no physical-point or hom premise

Actual command ancestry supplies the creating block. Its powered ambient
tuple is a geometric critical point for the same older hom. The native
correlation polynomial identifies its selected coordinate with the actual
retained bank quotient on that same full vertex.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCriticalReadback
open LeanCanny.Algebra LeanCanny.Geometry IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan family initial commands defaultInstruction)
open IntegralMixedFramedPhysicalIndex (enumerate)
open IntegralMixedFramedCriticalGuardBits
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem extend_cast {a b : ℕ} (h : a=b) (z : Fin b→ℝ) :
    IntegralMixedFramedBankObservation.extend (z∘Fin.cast h)=IntegralMixedFramedBankObservation.extend z :=by
  cases h
  rfl

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
  (key : List Bool→List Bool) (hpos : ∀q,0<(family P D H).birth (key q))
  (stage : List Bool→ℕ) (q w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hpos) q w)
  (ha : Active P T key stage q)

noncomputable def guardTuple : Fin (count P T key q)→ℝ :=
  IntegralFramedPhysicalSquare.joint P D H L F C hs key hpos q w hv∘Fin.cast (count_actual P D H T hr key q)

theorem guardTuple_extend : IntegralMixedFramedBankObservation.extend (guardTuple P D H L F C hs T hr key hpos q w hv)=
    tuple P D H L F C hs key hpos q w hv :=extend_cast _ _

local notation "c" => IntegralMixedFramedRootPullback.instructionAt P D (pairFst (key q)) (stage q)
local notation "older" => paddedPast (defaultInstruction P D (pairFst (key q))) (D.rules (pairFst (key q))) (stage q)
local notation "newer" => List.take (age P key stage q) (commands P D (key q))

include hr ha in
theorem exists_active_point :
    ∃r : CriticalRule (P.ambient (pairFst (key q))),(c).command=.critical r ∧
    ∃hcs : commands P D (key q)=newer++⟨(c).source,(c).source_cap,.critical r⟩::older,
    let x:=oldState P D H key q (c).source (c).source_cap r newer older hcs
    ∃φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ (x.sampler.scalarPrefix.basis.generator i)=
        tuple P D H L F C hs key hpos q w hv (enumerate older (x.sampler.scalar i)).val^
          UniformIntegralPowerSchedule.weights (P.cap (pairFst (key q))+1) (2^P.width (pairFst (key q))) (older).length i) ∧
      IntegralMixedCriticalReadback.CriticalPoint x (older_room P D H key q (c).source (c).source_cap r newer older hcs) r φ
        (IntegralMixedFramedCriticalAnchor.geometricPoint P D key stage q (tuple P D H L F C hs key hpos q w hv)) :=by
  obtain ⟨r,hc,hcs⟩:=IntegralMixedFramedCriticalAnchor.exists_active_decomposition P D H T hr key stage q ha
  obtain ⟨φ,hφ,HP⟩:=exists_critical_point P D H L F C hs key hpos q w hv (c).source (c).source_cap r newer older hcs
  refine ⟨r,hc,hcs,φ,hφ,?_⟩
  exact IntegralMixedFramedCriticalAnchor.geometricPoint_eq P D key stage q
    (tuple P D H L F C hs key hpos q w hv) ▸ HP

include hr in
theorem guard_selected_coordinate (r : CriticalRule (P.ambient (pairFst (key q)))) (hc : (c).command=.critical r) :
    (polynomial P D H T key stage q).eval₂ (Int.castRingHom ℝ) (guardTuple P D H L F C hs T hr key hpos q w hv)=0↔
      IntegralMixedFramedCriticalGuard.actualPoint P D H T hr key stage q ha (guardTuple P D H L F C hs T hr key hpos q w hv)=
        IntegralMixedFramedCriticalAnchor.geometricPoint P D key stage q (tuple P D H L F C hs key hpos q w hv)
          (ClearedCoordinateCritical.freeIndex r.offset.val (IntegralMixedCriticalRoot.fit r).le
            (IntegralMixedCriticalRoot.coordinate r)) :=by
  have HE:=IntegralMixedFramedCriticalAnchor.zero_iff_selected_coordinate P D H T hr key stage q ha r hc
    (guardTuple P D H L F C hs T hr key hpos q w hv)
  simpa only [guardTuple_extend P D H L F C hs T hr key hpos q w hv] using HE

end LeanCanny.Encoding.IntegralFramedPhysicalCriticalReadback
