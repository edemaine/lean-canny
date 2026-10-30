/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerSingularHeightCurves
public import LeanCanny.Geometry.FlatAffineShiftedSingularCriticalRoot
public import LeanCanny.Algebra.PositivePolynomialShift

/-! # Every singular point of a varying slice lifts to the actual power system

The frozen ancestry remains a root of the original tower. Singular
multipliers extend it to a shifted critical root. Odd real powers and the
forced-zero completion then give a root of exactly the sampled equations,
with zero newest objective coordinate.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineShiftedSlice
open LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCompleteRootStages (next)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

noncomputable def slice (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (v : ℝ) : Set (Fin (arity F u) → ℝ) :=
  {y | (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) y = 0 ∧
    ∀ j ∈ FlatAffineFullSourceTower.free F u (F.depth u),
      (∑ i, (FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i : ℝ) * y i) =
        (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial.eval₂ (Int.castRingHom ℝ)
          (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)) + if j = h then v else 0}

theorem exists_singular_power_root (F : Inputs) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots F u) (h : Fin (arity F u))
    (hs : h ∈ FlatAffineFullSourceTower.free F u (F.depth u)) (v : ℝ)
    (y : Fin (arity F u) → ℝ) (hy : y ∈ slice F u x h v)
    (hindependent : ∀ c : FlatAffineFullSourceTower.free F u (F.depth u) → ℝ,
      (∀ i, ∑ j : FlatAffineFullSourceTower.free F u (F.depth u),
        c j * (FlatAffineFullSourceTower.direction F u (F.depth u) j.val.succ i : ℝ) = 0) → ∀ j, c j = 0)
    (hsingular : ¬Function.Surjective (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
      (BoundedFullCriticalSamples.polynomial F.source u) (FlatAffineFullSourceTower.free F u (F.depth u))
      (FlatAffineFullSourceTower.direction F u (F.depth u)) y)) :
    ∃ z : Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ,
      (∀ i, (FlatAffinePowerPositive.system (next F) u i).eval₂ (Int.castRingHom ℝ) z =
        if i = FlatAffinePowerSingularHeightCurves.rowIndex F u h then v else 0) ∧
      z (FlatAffinePowerSingularHeightCurves.objectiveIndex F u) = 0 := by
  let p := BoundedFullCriticalSamples.polynomial F.source u
  let D := FlatAffinePowerControls.degree F u
  let s := FlatAffineFullSourceTower.free F u
  let a := FlatAffineFullSourceTower.direction F u
  let b := FlatAffineFullSourceTower.level F u
  obtain ⟨mu, hmu, hstage⟩ := FlatAffineSingularCriticalRoot.exists_shifted_stage_root (Int.castRingHom ℝ)
    p (s (F.depth u)) (a (F.depth u)) (fun i => (b (F.depth u) i).polynomial)
    (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)) y h hs v
    hy.1 hy.2 hindependent hsingular
  let W := FlatAffineTowerRegularity.appendPoint (F.depth u) x.val (Sum.elim y mu)
  have HW := FlatAffineTowerPartialRoots.append_values (Int.castRingHom ℝ) p s a b h v x.val (Sum.elim y mu) x.property hstage
  obtain ⟨q, hq⟩ := FlatAffinePowerTower.real_powerPoint_surjective (n := arity F u) (k := F.depth u + 1)
    D (FlatAffinePowerSampleInput.multiplier_power_odd F u) W
  let R := FlatAffinePowerTower.multiplier (n := arity F u) (FlatAffinePowerSingularHeightCurves.lastStage F u) h.succ
  have HO : ∀ i, (FlatAffineCriticalTower.system p s a b (F.depth u + 1) i).eval₂ (Int.castRingHom ℝ)
      (FlatAffinePowerTower.powerPoint D q) = if i = R then v else 0 := by
    rw [hq]
    have HRI : R = FlatAffineCriticalIndexedRows.multiplier (F.depth u) (Nat.lt_succ_self _) h.succ :=
      FlatAffinePowerTower.multiplier_eq (FlatAffinePowerSingularHeightCurves.lastStage F u) h.succ
    rw [HRI]
    exact HW
  have HD : 1 < D := BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size F.source u)
  have HQ := FlatAffinePowerTower.shifted_of_original p D HD s a b q
    (FlatAffinePowerSingularHeightCurves.lastStage F u) h hs v HO
  have Hraw : ∀ i, (FlatAffinePowerPositive.rawSystem (next F) u i).eval₂ (Int.castRingHom ℝ) q =
      if i = R then v else 0 := HQ
  refine ⟨PositivePolynomialSystem.extend q, PositivePolynomialSystem.extend_shifted (Int.castRingHom ℝ)
    (FlatAffinePowerPositive.rawSystem (next F) u) q R v Hraw, ?_⟩
  apply (PositivePolynomialSystem.extend_old q
    (FlatAffinePowerTower.multiplier (FlatAffinePowerSingularHeightCurves.lastStage F u) 0)).trans
  have Hpow := FlatAffinePowerTower.powerPoint_multiplier D q (FlatAffinePowerSingularHeightCurves.lastStage F u) 0
  have Hidx := FlatAffinePowerTower.multiplier_eq (n := arity F u) (FlatAffinePowerSingularHeightCurves.lastStage F u) 0
  have Hzero : W (FlatAffinePowerTower.multiplier (FlatAffinePowerSingularHeightCurves.lastStage F u) 0) = 0 :=
    (congrArg W Hidx).trans ((FlatAffineTowerRegularity.appendPoint_new (F.depth u) x.val (Sum.elim y mu) (Sum.inr 0)).trans hmu)
  have HE := (congrFun hq (FlatAffinePowerTower.multiplier (FlatAffinePowerSingularHeightCurves.lastStage F u) 0)).trans Hzero
  exact (pow_eq_zero_iff (by omega : D - 1 ≠ 0)).mp (Hpow.symm.trans HE)

end LeanCanny.Encoding.FlatAffineShiftedSlice
