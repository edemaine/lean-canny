/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineCompleteVertices

/-! # Recognizing powered roots from their original point and zero coordinate -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerSampleInput
open LeanCanny.Algebra
open FlatAffineFullSourceTower (Inputs count)
set_option backward.isDefEq.respectTransparency false

theorem roots_of_original_point (F : Inputs) (u : List Bool)
    (z : Fin (FlatAffineFullSourcePositive.count F u) → ℝ) (r : OriginalRoots F u)
    (hp : FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree F u) (z ∘ Fin.castSucc) = r.val)
    (hz : z (Fin.last (count F u)) = 0) :
    ∀ i, (FlatAffinePowerPositive.system F u i).eval₂ (Int.castRingHom ℝ) z = 0 := by
  apply (PositivePolynomialSystem.roots_iff (Int.castRingHom ℝ) (FlatAffinePowerPositive.rawSystem F u) z).mpr
  refine ⟨?_, hz⟩
  have hD : 1 < FlatAffinePowerControls.degree F u := by
    have H := FlatAffinePowerRowReaders.power_ne_zero F u
    unfold FlatAffinePowerRowReaders.power at H
    omega
  apply (FlatAffinePowerTower.roots_iff_original (Int.castRingHom ℝ) (BoundedFullCriticalSamples.polynomial F.source u)
    (FlatAffinePowerControls.degree F u) hD (FlatAffineFullSourceTower.free F u)
    (FlatAffineFullSourceTower.direction F u) (FlatAffineFullSourceTower.level F u) (z ∘ Fin.castSucc)).mpr
  intro i
  exact (congrArg (fun x : Fin (count F u) → ℝ => (FlatAffineFullSourceTower.system F u i).eval₂ (Int.castRingHom ℝ) x) hp).trans
    (r.property i)

end LeanCanny.Encoding.FlatAffinePowerSampleInput

namespace LeanCanny.Encoding.FlatAffineCompleteVertices
open LeanCanny.Algebra

theorem vertexEquiv_val (F : FlatAffineFullSourceTower.Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate F) (u w : List Bool) (hw : Valid F C u w) :
    (vertexEquiv F C u ⟨w, hw⟩).val =
      FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree F u)
        ((SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F C) u w hw).val ∘ Fin.castSucc) := rfl

end LeanCanny.Encoding.FlatAffineCompleteVertices
