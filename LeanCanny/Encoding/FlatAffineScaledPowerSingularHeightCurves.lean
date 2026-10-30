/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineScaledCoarserRoots
public import LeanCanny.Geometry.FlatAffineCoarsenedCurveConstancy
public import LeanCanny.Encoding.FlatAffineShiftedRootGeometry

/-! # Zero-objective height constancy with independently scaled coordinate rows -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineScaledPowerSingularHeightCurves
open LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCompleteRootStages (next)
open FlatAffinePowerSingularHeightCurves (lastStage rowIndex objectiveIndex)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem parameter_constant {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F) (u : List Bool) (h : Fin (arity F u))
    (scale : Fin (arity F u) → ℤ) (hscale : ∀ j, scale j ≠ 0)
    (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = scale j * FermatCoordinateCone.normal j i)
    (hactive : h ∈ FlatAffineFullSourceTower.free F u (F.depth u))
    (parameter : T → ℝ) (curve : T → Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ)
    (hc : Continuous curve) (hz : ∀ t, curve t (objectiveIndex F u) = 0)
    (hroot : ∀ t i, (FlatAffinePowerPositive.system (next F) u i).eval₂ (Int.castRingHom ℝ) (curve t) =
      if i = rowIndex F u h then parameter t else 0) (r t : T) : parameter r = parameter t := by
  let p := BoundedFullCriticalSamples.polynomial F.source u
  let s := FlatAffineFullSourceTower.free F u
  let a := FlatAffineFullSourceTower.direction F u
  let b := FlatAffineFullSourceTower.level F u
  let D := FlatAffinePowerControls.degree F u
  let Z (t : T) := FlatAffineShiftedSlice.originalPoint F u (curve t)
  let X (t : T) := FlatAffineShiftedSlice.ancestorPoint F u (curve t)
  let Y (t : T) := FlatAffineTowerPartialRoots.current (Z t)
  let Mu (t : T) := FlatAffineTowerPartialRoots.multipliers (Z t)
  have HD : 1 < D := BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size F.source u)
  have HCraw : Continuous (fun t => curve t ∘ Fin.castSucc) := continuous_pi (fun i => (continuous_apply i.castSucc).comp hc)
  have HCZ : Continuous Z := FlatAffinePowerTower.continuous_powerPoint D _ HCraw
  have HCX : Continuous X := FlatAffineShiftedSlice.continuous_ancestorPoint F u curve hc
  have HCY : Continuous Y := continuous_pi (fun i => (continuous_apply
    (FlatAffineCriticalIndexedRows.current (F.depth u) (Nat.lt_succ_self _) i)).comp HCZ)
  have HCM : Continuous Mu := continuous_pi (fun j => (continuous_apply
    (FlatAffineCriticalIndexedRows.multiplier (F.depth u) (Nat.lt_succ_self _) j)).comp HCZ)
  have HP (t : T) := FlatAffineShiftedSlice.ancestor_roots F u h hactive (parameter t) (curve t) (hroot t)
  have HM (t : T) : Mu t 0 = 0 := by
    have HI := congrArg (Z t) (FlatAffinePowerTower.multiplier_eq (n := arity F u) (lastStage F u) 0)
    calc
      _ = Z t (FlatAffinePowerTower.multiplier (lastStage F u) 0) := HI.symm
      _ = curve t (objectiveIndex F u) ^ (D - 1) :=
        FlatAffinePowerTower.powerPoint_multiplier D (curve t ∘ Fin.castSucc) (lastStage F u) 0
      _ = 0 := (congrArg (fun v : ℝ => v ^ (D - 1)) (hz t)).trans (zero_pow (by omega : D - 1 ≠ 0))
  have HR (t : T) (j : FlatAffineCriticalStage.Variables (arity F u)) (hj : j ≠ Sum.inr h.succ) :
      (FlatAffineCriticalStage.row p (s (F.depth u)) (a (F.depth u)) (fun i => (b (F.depth u) i).polynomial) j).eval₂
        (Int.castRingHom ℝ) (Sum.elim (X t ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u))
          (Sum.elim (Y t) (Mu t))) = 0 :=
    (FlatAffineShiftedSlice.stage_values F u h hactive (parameter t) (curve t) (hroot t) j).trans (ite_eq_right hj)
  have HE := FlatAffineCoarsenedCurveConstancy.constant p s a b h
    (FlatAffineScaledCoarserRoots.finite_roots F cone u (F.depth u) le_rfl h scale hscale hnormal)
    X Y Mu HCX HCY HCM HP HM HR r t
  have HV := FlatAffineSingularHeightCurves.height_value_eq p (s (F.depth u)) (a (F.depth u))
    (fun i => (b (F.depth u) i).polynomial) h hactive _ _ (Y r) (Y t) (Mu r) (Mu t)
    (congrArg (fun f => f ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)) HE.1) HE.2
  have HLr := (FlatAffineShiftedSlice.stage_values F u h hactive (parameter r) (curve r) (hroot r) (Sum.inr h.succ)).trans (ite_eq_left rfl)
  have HLt := (FlatAffineShiftedSlice.stage_values F u h hactive (parameter t) (curve t) (hroot t) (Sum.inr h.succ)).trans (ite_eq_left rfl)
  exact HLr.symm.trans (HV.trans HLt)

end LeanCanny.Encoding.FlatAffineScaledPowerSingularHeightCurves
