/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleDoubleAccess
public import LeanCanny.Encoding.SquareSampleProjectionChoice

/-! # Computing either member of a paired finite sample

Native projection search recovers an original-context word for each member.
Every pair of original roots has a paired word, including singular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleDouble
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] SquareSampleProjectionChoice.value SquareSampleCompleteVertices.Valid

def projection (F : Inputs) (right : Bool) (u : List Bool) : Fin (F.count u) → Fin (F.count u + F.count u) :=
  slot (F.count u) right

theorem projection_unary {F : Inputs} (hF : F.Access) (hC : SquareSampleComplete.Complete F) (right : Bool) :
    UnaryFn (fun q => (SquareSampleProjectedThom.coordinate (input F hC) F (projection F right)
      (LeanCanny.pairFst q) (LeanCanny.pairSnd q)).val) := by
  have hn := hF.count.comp pairFst_mem_FP
  have hi := UnaryFn.fromBitsLE_min (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (hn.sub (UnaryFn.const 1))
  have ho : UnaryFn (fun q => offset (F.count (LeanCanny.pairFst q)) right) := by
    cases right
    · exact UnaryFn.const 0
    · exact hn
  apply (ho.add hi).of_eq
  intro q
  rfl

noncomputable def value (F : Inputs) (hC : SquareSampleComplete.Complete F) (right : Bool) : List Bool → List Bool :=
  SquareSampleProjectionChoice.value (input F hC) F (projection F right)

theorem evaluator {F : Inputs} (hF : F.Access) (hC : SquareSampleComplete.Complete F) (right : Bool) :
    SpaceFunction (value F hC right) :=
  SquareSampleProjectionChoice.evaluator (access hF hC) hF (projection F right) (projection_unary hF hC right)

theorem projects (F : Inputs) (hC : SquareSampleComplete.Complete F) (right : Bool) (u : List Bool)
    (z : SquareSampleComplete.Roots (input F hC) u) :
    ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) (z.val ∘ projection F right u) = 0 :=
  (roots_iff F u z.val).mp z.property right

theorem value_valid (F : Inputs) (hC : SquareSampleComplete.Complete F) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input F hC) u w) :
    SquareSampleCompleteVertices.Valid F u (value F hC right (LeanCanny.pair u w)) :=
  SquareSampleProjectionChoice.value_valid (input F hC) F hC (projection F right) (projects F hC right) u w hw

theorem value_point (F : Inputs) (hC : SquareSampleComplete.Complete F) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input F hC) u w) :
    (SquareSampleCompleteVertices.candidate F u (value F hC right (LeanCanny.pair u w))
      (value_valid F hC right u w hw)).val =
        (SquareSampleCompleteVertices.candidate (input F hC) u w hw).val ∘ projection F right u :=
  SquareSampleProjectionChoice.value_point (input F hC) F hC (projection F right) (projects F hC right) u w hw

theorem value_root (F : Inputs) (hC : SquareSampleComplete.Complete F) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input F hC) u w) :
    SquareSampleCompleteVertices.candidate F u (value F hC right (LeanCanny.pair u w)) (value_valid F hC right u w hw) =
      project F hC u right (SquareSampleCompleteVertices.candidate (input F hC) u w hw) :=
  Subtype.ext (value_point F hC right u w hw)

noncomputable def wordPair (F : Inputs) (hC : SquareSampleComplete.Complete F) (u : List Bool)
    (x y : SquareSampleComplete.Roots F u) : List Bool :=
  SquareSampleCompleteVertices.word (input F hC) (complete F hC) u (pair F hC u x y)

theorem wordPair_valid (F : Inputs) (hC : SquareSampleComplete.Complete F) (u : List Bool)
    (x y : SquareSampleComplete.Roots F u) : SquareSampleCompleteVertices.Valid (input F hC) u (wordPair F hC u x y) :=
  SquareSampleCompleteVertices.word_valid (input F hC) (complete F hC) u (pair F hC u x y)

theorem value_wordPair (F : Inputs) (hC : SquareSampleComplete.Complete F) (u : List Bool) (right : Bool)
    (x y : SquareSampleComplete.Roots F u) :
    SquareSampleCompleteVertices.candidate F u (value F hC right (LeanCanny.pair u (wordPair F hC u x y)))
        (value_valid F hC right u (wordPair F hC u x y) (wordPair_valid F hC u x y)) =
      if right then y else x :=
  (value_root F hC right u (wordPair F hC u x y) (wordPair_valid F hC u x y)).trans
    ((congrArg (project F hC u right)
      (SquareSampleCompleteVertices.candidate_word (input F hC) (complete F hC) u (pair F hC u x y))).trans
        (project_pair F hC u right x y))

end LeanCanny.Encoding.SquareSampleDouble
