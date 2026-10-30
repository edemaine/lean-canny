/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Computing both original parents of a paired critical sample

Each native member word projects through the original next-stage sampler.
The resulting word is decoded in the original parent context, retaining the
complete original ancestry, including multiplier coordinates.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
open LeanCanny.Algebra LeanCanny.Computation
open CoordinateDoubleAffineChildRecords (criticalInput parentInput)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] memberWord FlatAffinePowerPrefix.value SquareSampleCompleteVertices.Valid

theorem prefix_le (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    depth u ≤ (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)).depth u := by
  change depth u ≤ depth u + 1
  omega

noncomputable def parentWord (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (right : Bool) (q : List Bool) : List Bool :=
  FlatAffinePowerPrefix.value
    (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
    (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level) depth
    (prefix_le P depth old level) (LeanCanny.pair (LeanCanny.pairFst q) (memberWord P depth old level right q))

theorem parentWord_evaluator {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) (right : Bool) :
    SpaceFunction (parentWord P depth old level right) := by
  have W := (SpaceFunction.ofFP pairFst pairFst_mem_FP).pairOutputs (memberWord_evaluator hP hd ho hl hA right)
  have E := FlatAffinePowerPrefix.evaluator
    (FlatAffineCompleteRootStages.access (CoordinateDoubleAffinePrefix.access hP hd ho hl hA) (hd.add (UnaryFn.const 1)))
    (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level) hd
    (prefix_le P depth old level)
  exact (W.chain E).congr (funext fun _ => rfl)

theorem parentWord_valid (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) :
    SquareSampleCompleteVertices.Valid (parentInput P depth old level) u
      (parentWord P depth old level right (LeanCanny.pair u w)) := by
  have H := FlatAffinePowerPrefix.value_valid
    (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
    (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level) depth
    (prefix_le P depth old level) u (memberWord P depth old level right (LeanCanny.pair u w))
    (memberWord_valid P depth old level right u w hw)
  simp only [parentWord, pairFst_pair]
  exact H

theorem parentWord_point (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) :
    (SquareSampleCompleteVertices.candidate (parentInput P depth old level) u
      (parentWord P depth old level right (LeanCanny.pair u w)) (parentWord_valid P depth old level right u w hw)).val =
      (SquareSampleCompleteVertices.candidate (criticalInput P depth old level) u
        (memberWord P depth old level right (LeanCanny.pair u w)) (memberWord_valid P depth old level right u w hw)).val ∘
          FlatAffinePowerPrefix.projection
            (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) depth
            (prefix_le P depth old level) u := by
  have H := FlatAffinePowerPrefix.value_point
    (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
    (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level) depth
    (prefix_le P depth old level) u (memberWord P depth old level right (LeanCanny.pair u w))
    (memberWord_valid P depth old level right u w hw)
  simp only [parentWord, pairFst_pair]
  exact H

noncomputable def memberRoot (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) :
    FlatAffinePowerSampleInput.OriginalRoots
      (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) u :=
  FlatAffineCompleteVertices.vertexEquiv
    (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level))
    (CoordinateDoubleAffinePrefix.coneCertificate P (fun u => depth u + 1) old level) u
    ⟨memberWord P depth old level right (LeanCanny.pair u w), memberWord_valid P depth old level right u w hw⟩

theorem parentWord_root (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) :
    FlatAffineCompleteVertices.vertexEquiv (CoordinateDoubleAffinePrefix.inputs P depth old level)
        (CoordinateDoubleAffinePrefix.coneCertificate P depth old level) u
        ⟨parentWord P depth old level right (LeanCanny.pair u w), parentWord_valid P depth old level right u w hw⟩ =
      FlatAffineCompleteRootStages.project
        (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) depth u
        (prefix_le P depth old level u) (memberRoot P depth old level right u w hw) := by
  have HP := parentWord_point P depth old level right u w hw
  have HE := congrArg (fun z : Fin ((parentInput P depth old level).count u) → ℝ =>
    FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree (CoordinateDoubleAffinePrefix.inputs P depth old level) u)
      (z ∘ Fin.castSucc)) HP
  apply Subtype.ext
  exact HE.trans ((CoordinateDoubleAffineChildRecords.powerPoint_projection
    (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) depth
    (prefix_le P depth old level) u
    (SquareSampleCompleteVertices.candidate (criticalInput P depth old level) u
      (memberWord P depth old level right (LeanCanny.pair u w)) (memberWord_valid P depth old level right u w hw)).val).trans
        (CoordinateDoubleAffineChildRecords.project_val
          (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) depth u
          (prefix_le P depth old level u) (memberRoot P depth old level right u w hw)).symm)

end LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
