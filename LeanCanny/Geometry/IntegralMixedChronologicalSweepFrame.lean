/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameCodeActual
public import LeanCanny.Geometry.IntegralMixedOriginalSweepRecord
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCutContinue
/-! # The next chronological coordinate gives the actual temporary sweep frame

The new frozen row has height zero before the sweep substitutes its actual
current-Q parameter. It consumes no producer or alias birth.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}

def next (d : Descriptor n birth) (hk : d.labels.length<n+1) : Fin (n+1):=⟨d.labels.length,hk⟩
noncomputable def frame (d : Descriptor n birth) (hk : d.labels.length<n+1) :=line d.frame (next d hk)

theorem next_free (d : Descriptor n birth) (hk : d.labels.length<n+1) : next d hk∉d.frame.frozen :=by
  rw [d.frozen_mem]
  exact Nat.lt_irrefl _

theorem frozen_card (d : Descriptor n birth) (hk : d.labels.length<n+1) :
    (frame d hk).frozen.card=d.labels.length+1 :=by
  change (insert (next d hk) d.frame.frozen).card=_
  rw [Finset.card_insert_of_notMem (next_free d hk),d.frozen_card]

theorem prefix_frozen (d : Descriptor n birth) (hk : d.labels.length<n+1) : PrefixFrozen (frame d hk) :=by
  have HE : firstFree d.frame (by rw [d.frozen_card];exact hk)=next d hk:=Fin.ext d.frozen_card
  have H:=d.prefix_frozen.line_first (by rw [d.frozen_card];exact hk)
  rw [HE] at H
  exact H

theorem free_iff (d : Descriptor n birth) (hk : d.labels.length<n+1) (i : Fin (n+1)) :
    i∉(frame d hk).frozen ↔d.labels.length+1≤ i.val :=by
  simp only [frame,line,Finset.mem_insert,d.frozen_mem,next,Fin.ext_iff]
  omega

noncomputable def pointData (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen) :
    IntegralMixedCriticalRecordConstructor.Data n birth :=
  originalPointData (frame d hk).frozen (fun _=>false) (fun i=>.single (d.atom i)) g j hg hj

theorem pointData_rule (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen) :
    (pointData d hk g j hg hj).rule=pointRule (frame d hk) g hg j hj :=
  originalPointData_rule _ _ _ _ _ _ _

theorem pointData_offset (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen) :
    (pointData d hk g j hg hj).offset.val=d.labels.length+1 :=frozen_card d hk

noncomputable def data (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen) :
    IntegralMixedCutRecordConstructor.Data n birth where
  critical:=pointData d hk g j hg hj
  positive:=by rw [pointData_offset];omega
  height:=⟨d.labels.length,by rw [pointData_offset];omega⟩
  current:=true

theorem data_slope (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (Q : ℤ) (hQ : Q≠0) : ((data d hk g j hg hj).rule Q hQ).slope=Q :=rfl

theorem data_height (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen)
    (Q : ℤ) (hQ : Q≠0) : ((data d hk g j hg hj).rule Q hQ).height=next d hk :=rfl

private theorem rule_ext (r s : IntegralMixedCriticalSweep.Rule n)
    (HC : r.critical=s.critical) (HH : r.height=s.height) (HS : r.slope=s.slope) : r=s :=by
  cases r
  cases s
  cases HC
  cases HH
  cases HS
  rfl

theorem data_rule {S B : ℕ} {P : SpatialSource n} {ι : Type} (x : State P S B birth ι)
    (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g j : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hj : j∉(frame d hk).frozen) :
    (data d hk g j hg hj).rule (commonDenominator x) (commonDenominator_ne_zero x)=
      IntegralMixedSweepRetarget.rule (cutRule x d.frame (next d hk) g hg) (j.val-(d.labels.length+1)) :=by
  have HJ : (freeCoordinate (frame d hk) j hj).val=j.val-(d.labels.length+1):=by
    change ((FrozenCoordinateOrdering.permutation (frame d hk).frozen).symm j).val-
      (frame d hk).frozen.card=j.val-(d.labels.length+1)
    rw [(prefix_frozen d hk).permutation,frozen_card]
    rfl
  apply rule_ext
  · change (pointData d hk g j hg hj).rule=
      {critical (frame d hk) g hg with coordinate:=j.val-(d.labels.length+1)}
    rw [pointData_rule]
    change {critical (frame d hk) g hg with coordinate:=(freeCoordinate (frame d hk) j hj).val}=_
    rw [HJ]
  · change next d hk=(FrozenCoordinateOrdering.permutation (frame d hk).frozen).symm (next d hk)
    rw [(prefix_frozen d hk).permutation]
    rfl
  · rfl

end LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
