/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerShiftPrefix
public import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Ancestry is constant along a continuous varying-height root branch

Earlier blocks remain roots of the original frozen prefix. Its complete
sampler has finitely many roots under the original cone certificate. A
continuous map from a connected parameter space into that finite root set is
constant, including when the prefix or shifted root is singular.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineFrozenPrefixCurves
open LeanCanny.Algebra LeanCanny.Encoding MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineCompleteRootStages (truncate)
open FlatAffinePowerPrefix (projection)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem prefix_constant {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (row : Fin (FlatAffineFullSourcePositive.count F u))
    (hlo : FlatAffineFullSourceTower.count (truncate F d) u ≤ row.val)
    (hhi : row.val < FlatAffineFullSourceTower.count F u)
    (parameter : T → ℝ) (curve : T → Fin (FlatAffineFullSourcePositive.count F u) → ℝ)
    (hc : Continuous curve)
    (hroot : ∀ t i, (FlatAffinePowerPositive.system F u i).eval₂ (Int.castRingHom ℝ) (curve t) =
      if i = row then parameter t else 0) (s t : T) :
    curve s ∘ projection F d hd u = curve t ∘ projection F d hd u := by
  let G := truncate F d
  let C := FlatAffineCompleteRootStages.cone_prefix F cone d hd
  let I := FlatAffinePowerSampleInput.input G C
  let z (t : T) : SquareSampleComplete.Roots I u :=
    ⟨curve t ∘ projection F d hd u, FlatAffinePowerShiftPrefix.roots_prefix F d hd u row hlo hhi (parameter t) (curve t) (hroot t)⟩
  have HP : Continuous (fun t : T => curve t ∘ projection F d hd u) :=
    continuous_pi (fun i => (continuous_apply (projection F d hd u i)).comp hc)
  have HZ : Continuous z := HP.subtype_mk (fun t =>
    FlatAffinePowerShiftPrefix.roots_prefix F d hd u row hlo hhi (parameter t) (curve t) (hroot t))
  let : Finite (SquareSampleComplete.Roots I u) :=
    (SquareSampleComplete.finite_roots I (FlatAffinePowerSampleInput.complete G C) u).1
  let : TotallyDisconnectedSpace (SquareSampleComplete.Roots I u) := inferInstance
  exact congrArg (fun x : SquareSampleComplete.Roots I u => x.val)
    (TotallyDisconnectedSpace.eq_of_continuous z HZ s t)

end LeanCanny.Geometry.FlatAffineFrozenPrefixCurves
