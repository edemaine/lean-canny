/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliarySampleTrace
public import LeanCanny.Geometry.CanonicalAuxiliaryHeightAccess

/-! # The actual recursive trace has the original native height ceiling

Every trace edge applies the proved uniform bank charge. The final actual bank
is bounded by the same original-only scheduledHeight function with a unary
trace length. No final-bank or normalization-matrix bound is assumed.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR AuxiliaryTiltedTerm SampleFrame
open scoped Classical
variable {n S B D : ℕ} {t : Term} {ht : (term n t).degreeBound≤D}
namespace SampleTrace
variable {hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B}
    {F L : SampleFrame n S B D t ht} {r : ℕ}

theorem height_eq (H : SampleTrace hcap F r L) : L.height=nextHeight n S B D 1^r*F.height := by
  induction H with
  | nil F => simp only [pow_zero,one_mul]
  | @cut F L r hk b W tail ih =>
    change L.height=nextHeight n S B D 1^r*nextHeight n S B D F.height at ih
    have HE : nextHeight n S B D F.height=nextHeight n S B D 1*F.height := by
      simp only [nextHeight,Nat.mul_one]
    rw [HE] at ih
    rw [ih,pow_succ]
    ac_rfl

theorem height_eq_scheduled (H : SampleTrace hcap F r L) :
    L.height=scheduledHeight n S B D (F.height-1) r := by
  rw [height_eq H]
  have HE : F.height-1+1=F.height := by have HP := F.height_pos; omega
  simp only [scheduledHeight,HE]

theorem bank_bound (H : SampleTrace hcap F r L) :
    L.state.bank.Bounds (scheduledHeight n S B D (F.height-1) r) := by
  rw [← height_eq_scheduled H]
  exact L.bank_bound

end SampleTrace
end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
