/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleContextProjectionChoice

/-! # Re-encoding complete root labels in their original source context

A composed sampler at `c` and its original sampler at `f c` have the same
polynomial equations. Their native label enumerations need not be identified:
this native conversion explicitly finds the unique original-context label
with the same point, including singular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleContextRebase
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs comp)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def value (F : Inputs) (f : List Bool → List Bool) : List Bool → List Bool :=
  SquareSampleContextProjectionChoice.value (comp F f) F f (fun _ i => i)

theorem coordinate_unary {F : Inputs} (hF : F.Access) {f : List Bool → List Bool} (hf : f ∈ FP) :
    UnaryFn (fun z => (SquareSampleContextThom.coordinate (comp F f) F f (fun _ i => i)
      (pairFst z) (pairSnd z)).val) := by
  have H : (fun z => pairFst (pairSnd (pairSnd z))) ∈ FP := by polytime
  exact UnaryFn.fromBitsLE_min H
    (((hF.count.comp hf).comp pairFst_mem_FP).sub (UnaryFn.const 1))

theorem evaluator {F : Inputs} (hF : F.Access) {f : List Bool → List Bool} (hf : f ∈ FP) :
    SpaceFunction (value F f) :=
  SquareSampleContextProjectionChoice.evaluator (SquareSampleInput.access_comp hF hf) hF hf
    (fun _ i => i) (coordinate_unary hF hf)

theorem projects (F : Inputs) (f : List Bool → List Bool) (c : List Bool)
    (x : SquareSampleComplete.Roots (comp F f) c) :
    ∀ i, (F.system (f c) i).eval₂ (Int.castRingHom ℝ) (x.val ∘ (fun i => i)) = 0 :=
  x.property

theorem value_valid (F : Inputs) (hF : SquareSampleComplete.Complete F) (f : List Bool → List Bool)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (comp F f) c w) :
    SquareSampleCompleteVertices.Valid F (f c) (value F f (pair c w)) :=
  SquareSampleContextProjectionChoice.value_valid (comp F f) F hF f (fun _ i => i) (projects F f) c w hw

theorem value_point (F : Inputs) (hF : SquareSampleComplete.Complete F) (f : List Bool → List Bool)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (comp F f) c w) :
    (SquareSampleCompleteVertices.candidate F (f c) (value F f (pair c w)) (value_valid F hF f c w hw)).val =
      (SquareSampleCompleteVertices.candidate (comp F f) c w hw).val :=
  SquareSampleContextProjectionChoice.value_point (comp F f) F hF f (fun _ i => i) (projects F f) c w hw

theorem unique (F : Inputs) (hF : SquareSampleComplete.Complete F) (f : List Bool → List Bool)
    (c w v : List Bool) (hw : SquareSampleCompleteVertices.Valid (comp F f) c w)
    (hv : SquareSampleCompleteVertices.Valid F (f c) v)
    (he : (SquareSampleCompleteVertices.candidate F (f c) v hv).val =
      (SquareSampleCompleteVertices.candidate (comp F f) c w hw).val) : value F f (pair c w) = v :=
  SquareSampleCompleteVertices.candidate_injective F (f c) _ v (value_valid F hF f c w hw) hv
    (Subtype.ext ((value_point F hF f c w hw).trans he.symm))

end LeanCanny.Encoding.SquareSampleContextRebase
