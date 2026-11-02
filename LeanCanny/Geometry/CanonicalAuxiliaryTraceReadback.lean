/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliarySampleTrace

/-! # Exact original-coordinate bank indices along the constructed trace -/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedDilationAdvance
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling SampleFrame
open scoped Classical
variable {n S B D : ℕ} {t : Term} {ht : (term n t).degreeBound≤D}

def SampleFrame.Front (F : SampleFrame n S B D t ht) : Prop :=
  ∀ i : Fin F.frozen, (F.selector i).val=frontIndex F.frozen i.val

theorem CutWitness.frame_front {F : SampleFrame n S B D t ht} {hk : F.frozen<n}
    {b : slice (polynomial n t) F.frozen F.parameters} (W : CutWitness F hk b)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (hF : F.Front) : (W.frame hcap).Front := by
  change ∀ i : Fin (F.frozen+1), (nextSelector F.selector i).val=frontIndex (F.frozen+1) i.val
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [nextSelector_new]
    change 0=(F.frozen+1)-1-F.frozen
    omega
  · rw [nextSelector_old]
    change (F.selector j).val+1=F.frozen+1-1-j.val
    have H := hF j
    have HI := j.isLt
    unfold frontIndex at H
    omega

theorem SampleTrace.front {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B}
    {F L : SampleFrame n S B D t ht} {r : ℕ} (H : SampleTrace hcap F r L) (hF : F.Front) : L.Front := by
  induction H with
  | nil _ => exact hF
  | cut hk b W tail ih => exact ih (W.frame_front _ hF)

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
