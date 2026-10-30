/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineAncestorLabels

/-! # Native child selection retaining singular affine roots

Queries contain a next-stage complete label and a parent complete label.
The native test checks their exact ancestry. Every frozen-stage root over
that parent is accepted, with no regularity assumption on either point.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineCompleteChildLabels
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

lemma depth_le (F : Inputs) (u : List Bool) : F.depth u ≤ (next F).depth u := Nat.le_succ _

theorem nextAccess {F : Inputs} (h : F.Access) : (next F).Access :=
  FlatAffineCompleteRootStages.access h (h.depth.add (UnaryFn.const 1))

theorem parentCone (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    FlatAffinePowerPositive.ConeCertificate F :=
  FlatAffineCompleteRootStages.cone_prefix (next F) cone F.depth (depth_le F)

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) : Language :=
  SquareSampleProjectionEquality.language (FlatAffinePowerSampleInput.input (next F) cone)
    (FlatAffinePowerSampleInput.input F (parentCone F cone))
    (FlatAffinePowerPrefix.projection (next F) F.depth (depth_le F))

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    SpaceDecider (language F cone) :=
  SquareSampleProjectionEquality.decider (FlatAffinePowerSampleInput.access (nextAccess h) cone)
    (FlatAffinePowerSampleInput.access h (parentCone F cone))
    (FlatAffinePowerPrefix.projection (next F) F.depth (depth_le F))
    (FlatAffinePowerPrefix.coordinate_unary (nextAccess h) h.depth (depth_le F) cone)

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) :
    language F cone ∈ PSPACE := (decider h cone).mem_PSPACE

theorem valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (u w v : List Bool)
    (h : pair u (pair w v) ∈ language F cone) :
    FlatAffineCompleteVertices.Valid (next F) cone u w ∧ FlatAffineCompleteVertices.Valid F (parentCone F cone) u v :=
  SquareSampleProjectionEquality.valid (FlatAffinePowerSampleInput.input (next F) cone)
    (FlatAffinePowerSampleInput.input F (parentCone F cone))
    (FlatAffinePowerPrefix.projection (next F) F.depth (depth_le F)) u w v h

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (u w v : List Bool)
    (hw : FlatAffineCompleteVertices.Valid (next F) cone u w)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v) :
    pair u (pair w v) ∈ language F cone ↔
      FlatAffineCompleteRootStages.project (next F) F.depth u (depth_le F u)
        (FlatAffineCompleteVertices.vertexEquiv (next F) cone u ⟨w, hw⟩) =
      FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩ := by
  have H := SquareSampleProjectionEquality.packet (FlatAffinePowerSampleInput.input (next F) cone)
    (FlatAffinePowerSampleInput.input F (parentCone F cone))
    (FlatAffinePowerSampleInput.complete F (parentCone F cone))
    (FlatAffinePowerPrefix.projection (next F) F.depth (depth_le F)) u w v hw hv
  rw [show (pair u (pair w v) ∈ language F cone) ↔ _ from H]
  let z := SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input (next F) cone) u w hw
  let p := SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F cone)) u v hv
  let projected : SquareSampleComplete.Roots (FlatAffinePowerSampleInput.input F (parentCone F cone)) u :=
    ⟨z.val ∘ FlatAffinePowerPrefix.projection (next F) F.depth (depth_le F) u,
      FlatAffinePowerPrefix.roots_prefix (Int.castRingHom ℝ) (next F) F.depth (depth_le F) u z.val z.property⟩
  have HP := FlatAffineAncestorLabels.original_projection (next F) F.depth (depth_le F) u z
  change z.val ∘ FlatAffinePowerPrefix.projection (next F) F.depth (depth_le F) u = p.val ↔ _
  constructor
  · intro E
    have EP : projected = p := Subtype.ext E
    change FlatAffineCompleteRootStages.project (next F) F.depth u (depth_le F u)
      (FlatAffinePowerSampleInput.originalRootsEquiv (next F) u z) = FlatAffinePowerSampleInput.originalRootsEquiv F u p
    exact HP.symm.trans (congrArg (FlatAffinePowerSampleInput.originalRootsEquiv F u) EP)
  · intro E
    have EP : FlatAffinePowerSampleInput.originalRootsEquiv F u projected = FlatAffinePowerSampleInput.originalRootsEquiv F u p :=
      HP.trans E
    exact congrArg (fun x : SquareSampleComplete.Roots (FlatAffinePowerSampleInput.input F (parentCone F cone)) u => x.val)
      ((FlatAffinePowerSampleInput.originalRootsEquiv F u).injective EP)

theorem exists_child (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F)) (u v : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F cone) u v)
    (y : FlatAffineCriticalStage.Variables (FlatAffineFullSourceTower.arity F u) → ℝ)
    (hy : ∀ i, (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial F.source u)
      (FlatAffineFullSourceTower.free F u (F.depth u)) (FlatAffineFullSourceTower.direction F u (F.depth u))
      (fun j => (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial) i).eval₂ (Int.castRingHom ℝ)
      (Sum.elim ((FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩).val ∘
        TriangularPolynomialIndexing.enumerate (FlatAffineFullSourceTower.stageWidth F u) (F.depth u)) y) = 0) :
    ∃ w : {w : List Bool // FlatAffineCompleteVertices.Valid (next F) cone u w},
      pair u (pair w.val v) ∈ language F cone ∧
      FlatAffineCompleteRootStages.newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u w).val = y := by
  let x := FlatAffineCompleteVertices.vertexEquiv F (parentCone F cone) u ⟨v, hv⟩
  let root := FlatAffineCompleteRootStages.extend F u x y hy
  let w := (FlatAffineCompleteVertices.vertexEquiv (next F) cone u).symm root
  have HW : FlatAffineCompleteVertices.vertexEquiv (next F) cone u w = root := Equiv.apply_symm_apply _ _
  refine ⟨w, ?_, ?_⟩
  · apply (packet F cone u w.val v w.property hv).mpr
    rw [HW]
    exact FlatAffineCompleteRootStages.extend_prefix F u x y hy
  · rw [HW]
    exact FlatAffineCompleteRootStages.extend_newest F u x y hy

end LeanCanny.Encoding.FlatAffineCompleteChildLabels
