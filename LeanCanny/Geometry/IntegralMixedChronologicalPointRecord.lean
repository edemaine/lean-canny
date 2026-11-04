/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalAtomicFrameReadback
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameDecode
/-! # The atomic chronological point record has its literal native bytes -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedFrozenFrame
open IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem Descriptor.atomic_pointData (d : Descriptor n m)
    (g j : Fin (n+1)) (hg : g∉d.frame.frozen) (hj : j∉d.frame.frozen) :
    (d.atomic.pointData g j hg hj)=IntegralMixedChronologicalFrameCode.data d g j hg hj :=by
  unfold AtomicRows.pointData IntegralMixedChronologicalFrameCode.data
  have HE : (fun i=>Row.single (d.atomic.atom i))=(fun i=>Row.single (d.atom i)):=by
    funext i
    exact congrArg Row.single (IntegralMixedChronologicalEndpoint.atomic_atom d d.frame d.atomic rfl i)
  rw [HE]

theorem Descriptor.atomic_pointData_code (d : Descriptor n m)
    (g j : Fin (n+1)) (hg : g∉d.frame.frozen) (hj : j∉d.frame.frozen) :
    (d.atomic.pointData g j hg hj).code=IntegralMixedChronologicalFrameCode.code n
      (IntegralMixedChronologicalFrameCode.labels d) g.val j.val :=by
  rw [d.atomic_pointData]
  exact IntegralMixedChronologicalFrameCode.data_code d g j hg hj

end LeanCanny.Geometry.IntegralMixedChronologicalFrame
