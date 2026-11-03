/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalCutActual
public import LeanCanny.Encoding.IntegralMixedChosenCutRecordBounds

/-! # A selected cut emits the exact chronological coordinate and stored degree -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalCutCode
open LeanCanny.Algebra LeanCanny.Geometry IntegralMixedHistory IntegralMixedRelativeCuts
open IntegralMixedChronologicalFrame IntegralMixedChronologicalSweepFrame IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}

noncomputable def physicalCoordinate (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(frame d hk).frozen)
    (j : Fin (n-(pointData d hk g g hg hg).offset.val+1)) : Fin (n+1) :=
  ⟨(pointData d hk g g hg hg).offset.val+j.val,by
    have HO:=(pointData d hk g g hg hg).offset.isLt
    have HJ:=j.isLt
    omega⟩

theorem physicalCoordinate_free (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(frame d hk).frozen)
    (j : Fin (n-(pointData d hk g g hg hg).offset.val+1)) :
    physicalCoordinate d hk g hg j∉(frame d hk).frozen :=by
  rw [free_iff]
  change d.labels.length+1≤(pointData d hk g g hg hg).offset.val+j.val
  have HO:=pointData_offset d hk g g hg hg
  omega

theorem data_retarget (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(frame d hk).frozen)
    (j : Fin (n-(pointData d hk g g hg hg).offset.val+1)) :
    (data d hk g g hg hg).retarget j=
      data d hk g (physicalCoordinate d hk g hg j) hg (physicalCoordinate_free d hk g hg j) :=by
  have HC : (pointData d hk g (physicalCoordinate d hk g hg j) hg
      (physicalCoordinate_free d hk g hg j)).coordinate=j :=by
    apply Fin.ext
    change ((FrozenCoordinateOrdering.permutation (frame d hk).frozen).symm
      (physicalCoordinate d hk g hg j)).val-(frame d hk).frozen.card=j.val
    rw [(prefix_frozen d hk).permutation,frozen_card]
    change (pointData d hk g g hg hg).offset.val+j.val-(d.labels.length+1)=j.val
    have HO:=pointData_offset d hk g g hg hg
    omega
  have HK : ({pointData d hk g g hg hg with coordinate:=j} :
      IntegralMixedCriticalRecordConstructor.Data n birth)=
      pointData d hk g (physicalCoordinate d hk g hg j) hg (physicalCoordinate_free d hk g hg j) :=
    congrArg (fun t=>({pointData d hk g g hg hg with coordinate:=t} :
      IntegralMixedCriticalRecordConstructor.Data n birth)) HC.symm
  unfold IntegralMixedCutRecordConstructor.Data.retarget IntegralMixedChronologicalSweepFrame.data
  congr 1

theorem chosenCode_actual (d : Descriptor n birth) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(frame d hk).frozen) (P : SpatialSource n) (Q : ℤ) (hQ : Q≠0)
    (c : Kind P ((data d hk g g hg hg).rule Q hQ)) (degree : ℕ) :
    (data d hk g g hg hg).chosenCode Q hQ c degree=
      code n (IntegralMixedChronologicalFrameCode.labels d) g.val
        (physicalCoordinate d hk g hg ((data d hk g g hg hg).coordinate Q hQ c)).val
        (IntegralMixedCutRecordConstructor.tagIndex
          (IntegralMixedSweepRetarget.tag ((data d hk g g hg hg).rule Q hQ) c))
        (IntegralMixedSweepRetarget.choiceIndex ((data d hk g g hg hg).rule Q hQ) c) degree :=by
  unfold IntegralMixedCutRecordConstructor.Data.chosenCode
  rw [data_retarget,data_code]

end LeanCanny.Encoding.IntegralMixedChronologicalCutCode
