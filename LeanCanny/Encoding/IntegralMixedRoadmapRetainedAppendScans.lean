/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendReadback
/-! # New physical readbacks reconstruct the native correlation scans -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX"=>context hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedPhysicalPointCompanionScan.geometricPoint
  IntegralMixedPhysicalPointCompanionScan.retained preparedRoot

theorem all_critical_of_past_and_fresh (old : List Bool) (e : ℕ) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old e) w)
    (p p0 : Fin ((P).ambient (pairFst ((B).key (CTX old e)))+1)→ℝ)
    (hr : FreshReadback hn ht ha hR0 old e w hw p p0)
    (hPast : ∀b,b<beginBirth hn ht ha hR0 old→
      ∀hb : IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) b,
        IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false (CTX old e) w hw b hb=
          IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false (CTX old e) w hw b
            ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e) b,
              IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩) :
    pair (preparedRoot hn ht ha hR0 old e) w∈
      IntegralMixedPhysicalGuardScan.language hn ht ha (radius_binary hR0) false:=by
  apply (IntegralMixedPhysicalPointCompanionScan.all_critical_packet_iff hn ht ha (radius_binary hR0) false
    (preparedRoot hn ht ha hR0 old e) w).mpr
  refine ⟨hw,?_⟩
  intro b hb hactive
  change b<IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (CTX old e)) at hb
  rw [prefix_length] at hb
  by_cases hOld : b<beginBirth hn ht ha hR0 old
  · exact hPast b hOld hactive
  · exact critical_of_fresh_readback hn ht ha hR0 old e w hw p p0 hr b (by omega) hb hactive

theorem companion_of_fresh_readback (old : List Bool) (e : ℕ) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old e) w)
    (p p0 : Fin ((P).ambient (pairFst ((B).key (CTX old e)))+1)→ℝ)
    (hr : FreshReadback hn ht ha hR0 old e w hw p p0)
    (a f k : ℕ) (ha0 : beginBirth hn ht ha hR0 old≤a)
    (ha1 : a<finishBirth hn ht ha hR0 old e)
    (hf : beginBirth hn ht ha hR0 old≤f) (hfk : f+k≤finishBirth hn ht ha hR0 old e)
    (hend : finishBirth hn ht ha hR0 old e≤fullBirth hn ht ha hR0 old e)
    (hAnchor : IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) a)
    (hCapture : ∀j,j<k→IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false
      (CTX old e) (f+j)) :
    pair (pair (CTX old e) w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k)∈
      IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false:=by
  apply (IntegralMixedPhysicalPointCompanionScan.language_packet_iff hn ht ha (radius_binary hR0) false
    (CTX old e) w hw a f k hAnchor (by rw [prefix_length];omega)).mpr
  have HA : IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (CTX old e) w hw a=p:=by
    simpa only [ite_eq_left ha1] using hr.physical a ha0 (ha1.trans_le hend)
  intro j hj
  have HJ0 : beginBirth hn ht ha hR0 old≤f+j:=by omega
  have HJ1 : f+j<finishBirth hn ht ha hR0 old e:=by omega
  have HB:=hCapture j hj
  have HPoint : IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (CTX old e) w hw (f+j)=p:=by
    simpa only [ite_eq_left HJ1] using hr.physical (f+j) HJ0 (HJ1.trans_le hend)
  refine ⟨HB,HPoint.trans HA.symm,?_⟩
  rw [HA]
  have HScalar:=hr.scalar (f+j) HJ0 (HJ1.trans_le hend) HB
  rw [ite_eq_left HJ1] at HScalar
  exact (IntegralMixedPhysicalFieldEquality.retained_point hn ht ha (radius_binary hR0)
    (CTX old e) w hw (f+j) HB).trans HScalar

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
