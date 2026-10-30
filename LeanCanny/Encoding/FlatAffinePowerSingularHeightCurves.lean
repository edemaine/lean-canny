/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSingularHeightCurves
public import LeanCanny.Encoding.FlatAffineCompleteRootStages
public import LeanCanny.Algebra.FlatAffineTowerPartialRoots
public import LeanCanny.Algebra.FlatAffinePowerShiftOriginal

/-! # A varying actual power branch cannot have zero objective multiplier

The positive completion and multiplier powers are removed explicitly.
Coarsening the newest height then proves its parameter constant whenever
the newest objective multiplier vanishes throughout the branch.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerSingularHeightCurves
open LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity count stageWidth)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

private theorem eval_old {n : ℕ} (p : Fin n → MvPolynomial (Fin n) ℤ)
    (z : Fin (n + 1) → ℝ) (i : Fin n) :
    (PositivePolynomialSystem.system p i.castSucc).eval₂ (Int.castRingHom ℝ) z =
      (p i).eval₂ (Int.castRingHom ℝ) (z ∘ Fin.castSucc) := by
  rw [PositivePolynomialSystem.old_row, eval₂_rename]

def lastStage (F : Inputs) (u : List Bool) : Fin (F.depth u + 1) := ⟨F.depth u, Nat.lt_succ_self _⟩

def rowIndex (F : Inputs) (u : List Bool) (h : Fin (arity F u)) :
    Fin (FlatAffineFullSourcePositive.count (next F) u) :=
  (FlatAffinePowerTower.multiplier (lastStage F u) h.succ).castSucc

def objectiveIndex (F : Inputs) (u : List Bool) : Fin (FlatAffineFullSourcePositive.count (next F) u) :=
  (FlatAffinePowerTower.multiplier (n := arity F u) (lastStage F u) 0).castSucc

variable {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]

theorem parameter_constant (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (u : List Bool) (h : Fin (arity F u))
    (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = FermatCoordinateCone.normal j i)
    (hactive : h ∈ FlatAffineFullSourceTower.free F u (F.depth u))
    (parameter : T → ℝ) (curve : T → Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ)
    (hc : Continuous curve) (hz : ∀ t, curve t (objectiveIndex F u) = 0)
    (hroot : ∀ t i, (FlatAffinePowerPositive.system (next F) u i).eval₂ (Int.castRingHom ℝ) (curve t) =
      if i = rowIndex F u h then parameter t else 0) (r t : T) : parameter r = parameter t := by
  dsimp +instances only [FlatAffineFullSourcePositive.count, FlatAffineFullSourceTower.count,
    FlatAffineFullSourceTower.stageWidth, FlatAffineFullSourceTower.arity,
    FlatAffineCompleteRootStages.next, FlatAffineCompleteRootStages.truncate] at *
  let p := BoundedFullCriticalSamples.polynomial F.source u
  let D := FlatAffinePowerControls.degree F u
  let s := FlatAffineFullSourceTower.free F u
  let a := FlatAffineFullSourceTower.direction F u
  let b := FlatAffineFullSourceTower.level F u
  let raw (t : T) : Fin ((F.depth u + 1) * FlatAffineCriticalTower.width (arity F u)) → ℝ := curve t ∘ Fin.castSucc
  let z (t : T) : Fin ((F.depth u + 1) * FlatAffineCriticalTower.width (arity F u)) → ℝ :=
    FlatAffinePowerTower.powerPoint D (raw t)
  let R := FlatAffinePowerTower.multiplier (n := arity F u) (lastStage F u) h.succ
  have HD : 1 < D := BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size F.source u)
  have Hraw (t : T) (i : Fin (count (next F) u)) :
      (FlatAffinePowerPositive.rawSystem (next F) u i).eval₂ (Int.castRingHom ℝ) (raw t) =
        if i = R then parameter t else 0 := by
    have H := hroot t i.castSucc
    have HE := eval_old (FlatAffinePowerPositive.rawSystem (next F) u) (curve t) i
    have HV := HE.symm.trans H
    simpa only [rowIndex, Fin.castSucc_inj] using HV
  have Hexcept (t : T) : ∀ i, i ≠ R →
      (FlatAffineCriticalTower.system p s a b (F.depth u + 1) i).eval₂ (Int.castRingHom ℝ) (z t) = 0 := by
    apply FlatAffinePowerTower.roots_except_original (Int.castRingHom ℝ) p D HD s a b (raw t) R
    intro i hi
    exact (Hraw t i).trans (ite_eq_right hi)
  have HRI : R = FlatAffineCriticalIndexedRows.multiplier (F.depth u) (Nat.lt_succ_self _) h.succ :=
    FlatAffinePowerTower.multiplier_eq (lastStage F u) h.succ
  rw [HRI] at Hexcept
  have HP (t : T) := FlatAffineTowerPartialRoots.prefix_roots (Int.castRingHom ℝ) p s a b h (z t) (Hexcept t)
  have HR (t : T) := FlatAffineTowerPartialRoots.stage_roots (Int.castRingHom ℝ) p s a b h (z t) (Hexcept t)
  have HCraw : Continuous raw := continuous_pi (fun i => (continuous_apply i.castSucc).comp hc)
  have HCz : Continuous z := FlatAffinePowerTower.continuous_powerPoint D raw HCraw
  let x (t : T) := FlatAffineTowerPartialRoots.ancestorPoint (z t)
  let y (t : T) := FlatAffineTowerPartialRoots.current (z t)
  let mu (t : T) := FlatAffineTowerPartialRoots.multipliers (z t)
  have HX : Continuous x := continuous_pi (fun i => (continuous_apply
    (TriangularPolynomialRows.prefixIndex (stageWidth F u) (F.depth u) (F.depth u + 1) (by omega) i)).comp HCz)
  have HY : Continuous y := continuous_pi (fun i => (continuous_apply
    (FlatAffineCriticalIndexedRows.current (F.depth u) (Nat.lt_succ_self _) i)).comp HCz)
  have HM : Continuous mu := continuous_pi (fun j => (continuous_apply
    (FlatAffineCriticalIndexedRows.multiplier (F.depth u) (Nat.lt_succ_self _) j)).comp HCz)
  have Hzero (t : T) : mu t 0 = 0 := by
    have HI := congrArg (z t) (FlatAffinePowerTower.multiplier_eq (n := arity F u) (lastStage F u) 0)
    calc
      _ = z t (FlatAffinePowerTower.multiplier (lastStage F u) 0) := HI.symm
      _ = curve t (objectiveIndex F u) ^ (D - 1) := FlatAffinePowerTower.powerPoint_multiplier D (raw t) (lastStage F u) 0
      _ = 0 := (congrArg (fun v : ℝ => v ^ (D - 1)) (hz t)).trans (zero_pow (by omega : D - 1 ≠ 0))
  have HE (t : T) : (FlatAffineCriticalStage.row p (s (F.depth u)) (a (F.depth u))
      (fun i => (b (F.depth u) i).polynomial) (Sum.inr h.succ)).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (x t ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u))
        (Sum.elim (y t) (mu t))) = parameter t := by
    have HS := FlatAffineTowerPartialRoots.stage_value (Int.castRingHom ℝ) p s a b (z t) (Sum.inr h.succ)
    have HV := FlatAffinePowerTower.height_value_original (Int.castRingHom ℝ) p D s a b (raw t) (lastStage F u) h hactive
    rw [FlatAffinePowerTower.multiplier_eq] at HV
    apply HS.trans (HV.trans ?_)
    have HVraw := Hraw t R
    rw [ite_eq_left rfl] at HVraw
    have Hrow : FlatAffinePowerPositive.rawSystem (next F) u R =
        FlatAffinePowerTower.row p D (fun t : Fin (F.depth u + 1) => s t.val) (fun t => a t.val)
          (fun t => b t.val) (lastStage F u) (Sum.inr h.succ) :=
      FlatAffinePowerTower.system_row p D _ _ _ (lastStage F u) (Sum.inr h.succ)
    exact (congrArg (fun q => q.eval₂ (Int.castRingHom ℝ) (raw t)) Hrow).symm.trans HVraw
  exact FlatAffineSingularHeightCurves.height_constant F cone u (F.depth u) le_rfl h hnormal
    x y mu HX HY HM HP Hzero HR hactive parameter HE r t

end LeanCanny.Encoding.FlatAffinePowerSingularHeightCurves
