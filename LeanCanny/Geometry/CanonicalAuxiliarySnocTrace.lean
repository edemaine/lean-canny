/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliarySampleTrace

/-! # Chronological trace induction for literal framed-script readback -/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling
open scoped Classical
variable {n S B D : ℕ} {t : Term} {ht : (term n t).degreeBound≤D}

inductive SnocTrace (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (F : SampleFrame n S B D t ht) : ℕ → SampleFrame n S B D t ht → Prop
  | nil : SnocTrace hcap F 0 F
  | snoc {G r} (prior : SnocTrace hcap F r G) (hk : G.frozen<n)
      (b : slice (polynomial n t) G.frozen G.parameters) (W : CutWitness G hk b) :
      SnocTrace hcap F (r+1) (W.frame hcap)

namespace SnocTrace
variable {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B}

theorem prepend {F L : SampleFrame n S B D t ht} {hk : F.frozen<n}
    {b : slice (polynomial n t) F.frozen F.parameters} (W : CutWitness F hk b) {r : ℕ}
    (H : SnocTrace hcap (W.frame hcap) r L) : SnocTrace hcap F (r+1) L := by
  induction H with
  | nil => exact SnocTrace.snoc SnocTrace.nil hk b W
  | snoc prior hk' b' W' ih => exact SnocTrace.snoc ih hk' b' W'

end SnocTrace

namespace SampleTrace
variable {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B}

theorem toSnoc {F L : SampleFrame n S B D t ht} {r : ℕ} (H : SampleTrace hcap F r L) : SnocTrace hcap F r L := by
  induction H with
  | nil _ => exact SnocTrace.nil
  | cut hk b W tail ih => exact SnocTrace.prepend W ih

theorem appendStep {F G : SampleFrame n S B D t ht} {r : ℕ} (H : SampleTrace hcap F r G) :
    ∀ (hk : G.frozen<n) (b : slice (polynomial n t) G.frozen G.parameters) (W : CutWitness G hk b),
      SampleTrace hcap F (r+1) (W.frame hcap) := by
  induction H with
  | nil F =>
    intro hk b W
    exact SampleTrace.cut hk b W (SampleTrace.nil _)
  | cut hk b W tail ih =>
    intro hk' b' W'
    exact SampleTrace.cut hk b W (ih hk' b' W')

end SampleTrace

theorem SnocTrace.toForward {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B}
    {F L : SampleFrame n S B D t ht} {r : ℕ} (H : SnocTrace hcap F r L) : SampleTrace hcap F r L := by
  induction H with
  | nil => exact SampleTrace.nil _
  | snoc prior hk b W ih => exact ih.appendStep hk b W

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
