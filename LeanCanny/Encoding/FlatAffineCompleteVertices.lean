/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteVertices
public import LeanCanny.Encoding.FlatAffinePowerOriginalSamples

/-! # Short native vertices for every original real affine critical root -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineCompleteVertices
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def width (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F) :=
  SquareSampleCompleteVertices.width (FlatAffinePowerSampleInput.input F hcone)

def Valid (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F) :=
  SquareSampleCompleteVertices.Valid (FlatAffinePowerSampleInput.input F hcone)

noncomputable def language (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F) : Language :=
  SquareSampleCompleteVertices.language (FlatAffinePowerSampleInput.input F hcone)

theorem width_unary {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F) :
    UnaryFn (width F hcone) := SquareSampleCompleteVertices.width_unary (FlatAffinePowerSampleInput.access h hcone)

theorem mem_PSPACE {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F) :
    language F hcone ∈ PSPACE := SquareSampleCompleteVertices.mem_PSPACE (FlatAffinePowerSampleInput.access h hcone)

noncomputable def vertexEquiv (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F) (u : List Bool) :
    {w : List Bool // Valid F hcone u w} ≃ FlatAffinePowerSampleInput.OriginalRoots F u :=
  (SquareSampleCompleteVertices.vertexEquiv (FlatAffinePowerSampleInput.input F hcone)
    (FlatAffinePowerSampleInput.complete F hcone) u).trans (FlatAffinePowerSampleInput.originalRootsEquiv F u)

lemma word_length (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F) (u w : List Bool)
    (hw : Valid F hcone u w) : w.length = width F hcone u := (Classical.choose hw).1

lemma ambient_coordinate (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F) (u w : List Bool)
    (hw : Valid F hcone u w) (t : Fin (F.depth u)) (i : Fin (FlatAffineFullSourceTower.arity F u)) :
    (vertexEquiv F hcone u ⟨w, hw⟩).val (FlatAffinePowerTower.current t i) =
      (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F hcone) u w hw).val
        (FlatAffinePowerTower.current t i).castSucc :=
  FlatAffinePowerSampleInput.originalRootsEquiv_current F u _ t i

end LeanCanny.Encoding.FlatAffineCompleteVertices
