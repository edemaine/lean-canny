/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineShiftedSingularLift

/-! # Exact ancestry and spatial coordinates of lifted shifted critical roots -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineShiftedSlice
open LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCompleteRootStages (next)
open FlatAffinePowerSingularHeightCurves (lastStage rowIndex)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

noncomputable def originalPoint (F : Inputs) (u : List Bool)
    (z : Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ) :
    Fin (FlatAffineFullSourceTower.count (next F) u) → ℝ :=
  FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree F u) (z ∘ Fin.castSucc)

noncomputable def ancestorPoint (F : Inputs) (u : List Bool)
    (z : Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ) :
    Fin (FlatAffineFullSourceTower.count F u) → ℝ :=
  originalPoint F u z ∘ TriangularPolynomialRows.prefixIndex (stageWidth F u) (F.depth u) (F.depth u + 1) (by omega)

def spatialPoint (F : Inputs) (u : List Bool)
    (z : Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ) : Fin (arity F u) → ℝ :=
  fun i => z (FlatAffinePowerTower.current (lastStage F u) i).castSucc

theorem spatial_original (F : Inputs) (u : List Bool)
    (z : Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ) (i : Fin (arity F u)) :
    originalPoint F u z (FlatAffineCriticalIndexedRows.current (F.depth u) (Nat.lt_succ_self _) i) =
      spatialPoint F u z i := by
  have HI := congrArg (originalPoint F u z) (FlatAffinePowerTower.current_eq (lastStage F u) i)
  exact HI.symm.trans (FlatAffinePowerTower.powerPoint_current (FlatAffinePowerControls.degree F u) (z ∘ Fin.castSucc) (lastStage F u) i)

theorem exists_power_lift (F : Inputs) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots F u) (h : Fin (arity F u))
    (hs : h ∈ FlatAffineFullSourceTower.free F u (F.depth u)) (v : ℝ)
    (y : Fin (arity F u) → ℝ) (mu : Fin (arity F u + 1) → ℝ)
    (hy : ∀ j, (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial F.source u)
      (FlatAffineFullSourceTower.free F u (F.depth u)) (FlatAffineFullSourceTower.direction F u (F.depth u))
      (fun i => (FlatAffineFullSourceTower.level F u (F.depth u) i).polynomial) j).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)) (Sum.elim y mu)) =
        if j = Sum.inr h.succ then v else 0) :
    ∃ z : Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ,
      (∀ i, (FlatAffinePowerPositive.system (next F) u i).eval₂ (Int.castRingHom ℝ) z =
        if i = rowIndex F u h then v else 0) ∧ ancestorPoint F u z = x.val ∧ spatialPoint F u z = y := by
  let p := BoundedFullCriticalSamples.polynomial F.source u
  let D := FlatAffinePowerControls.degree F u
  let s := FlatAffineFullSourceTower.free F u
  let a := FlatAffineFullSourceTower.direction F u
  let b := FlatAffineFullSourceTower.level F u
  let W := FlatAffineTowerRegularity.appendPoint (F.depth u) x.val (Sum.elim y mu)
  have HW := FlatAffineTowerPartialRoots.append_values (Int.castRingHom ℝ) p s a b h v x.val (Sum.elim y mu) x.property hy
  obtain ⟨q, hq⟩ := FlatAffinePowerTower.real_powerPoint_surjective (n := arity F u) (k := F.depth u + 1)
    D (FlatAffinePowerSampleInput.multiplier_power_odd F u) W
  let R := FlatAffinePowerTower.multiplier (n := arity F u) (lastStage F u) h.succ
  have HO : ∀ i, (FlatAffineCriticalTower.system p s a b (F.depth u + 1) i).eval₂ (Int.castRingHom ℝ)
      (FlatAffinePowerTower.powerPoint D q) = if i = R then v else 0 := by
    rw [hq]
    have HRI : R = FlatAffineCriticalIndexedRows.multiplier (F.depth u) (Nat.lt_succ_self _) h.succ :=
      FlatAffinePowerTower.multiplier_eq (lastStage F u) h.succ
    rw [HRI]
    exact HW
  have HD : 1 < D := BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size F.source u)
  have HQ := FlatAffinePowerTower.shifted_of_original p D HD s a b q (lastStage F u) h hs v HO
  have Hraw : ∀ i, (FlatAffinePowerPositive.rawSystem (next F) u i).eval₂ (Int.castRingHom ℝ) q =
      if i = R then v else 0 := HQ
  let z := PositivePolynomialSystem.extend q
  have HZ : originalPoint F u z = W := by
    have HE : z ∘ Fin.castSucc = q := funext (PositivePolynomialSystem.extend_old q)
    exact (congrArg (FlatAffinePowerTower.powerPoint D) HE).trans hq
  refine ⟨z, PositivePolynomialSystem.extend_shifted (Int.castRingHom ℝ)
    (FlatAffinePowerPositive.rawSystem (next F) u) q R v Hraw, ?_, ?_⟩
  · exact (congrArg (fun f => f ∘ TriangularPolynomialRows.prefixIndex (stageWidth F u)
      (F.depth u) (F.depth u + 1) (by omega)) HZ).trans (FlatAffineTowerRegularity.appendPoint_prefix (F.depth u) x.val _)
  · funext i
    exact (spatial_original F u z i).symm.trans
      ((congrFun HZ (FlatAffineCriticalIndexedRows.current (F.depth u) (Nat.lt_succ_self _) i)).trans
        (FlatAffineTowerRegularity.appendPoint_new (F.depth u) x.val (Sum.elim y mu) (Sum.inl i)))

end LeanCanny.Encoding.FlatAffineShiftedSlice
