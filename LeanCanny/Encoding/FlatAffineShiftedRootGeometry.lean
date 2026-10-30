/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineShiftedRootLift

/-! # Original equations and frozen ancestry of arbitrary shifted power roots -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineShiftedSlice
open LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffineCompleteRootStages (next)
open FlatAffinePowerSingularHeightCurves (lastStage rowIndex)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

private theorem eval_old {n : ℕ} (p : Fin n → MvPolynomial (Fin n) ℤ)
    (z : Fin (n + 1) → ℝ) (i : Fin n) :
    (PositivePolynomialSystem.system p i.castSucc).eval₂ (Int.castRingHom ℝ) z =
      (p i).eval₂ (Int.castRingHom ℝ) (z ∘ Fin.castSucc) := by
  rw [PositivePolynomialSystem.old_row, eval₂_rename]

theorem original_values (F : Inputs) (u : List Bool) (h : Fin (arity F u))
    (hs : h ∈ FlatAffineFullSourceTower.free F u (F.depth u)) (v : ℝ)
    (z : Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ)
    (hz : ∀ i, (FlatAffinePowerPositive.system (next F) u i).eval₂ (Int.castRingHom ℝ) z =
      if i = rowIndex F u h then v else 0) :
    ∀ i, (FlatAffineFullSourceTower.system (next F) u i).eval₂ (Int.castRingHom ℝ) (originalPoint F u z) =
      if i = FlatAffineCriticalIndexedRows.multiplier (F.depth u) (Nat.lt_succ_self _) h.succ then v else 0 := by
  let p := BoundedFullCriticalSamples.polynomial F.source u
  let D := FlatAffinePowerControls.degree F u
  let s := FlatAffineFullSourceTower.free F u
  let a := FlatAffineFullSourceTower.direction F u
  let b := FlatAffineFullSourceTower.level F u
  let raw := z ∘ Fin.castSucc
  let R := FlatAffinePowerTower.multiplier (n := arity F u) (lastStage F u) h.succ
  have HR (i : Fin (FlatAffineFullSourceTower.count (next F) u)) :
      (FlatAffinePowerPositive.rawSystem (next F) u i).eval₂ (Int.castRingHom ℝ) raw = if i = R then v else 0 := by
    have HE := (eval_old (FlatAffinePowerPositive.rawSystem (next F) u) z i).symm.trans (hz i.castSucc)
    simpa only [rowIndex, Fin.castSucc_inj] using HE
  have HD : 1 < D := BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size F.source u)
  have HO : ∀ i, (FlatAffineCriticalTower.system p s a b (F.depth u + 1) i).eval₂ (Int.castRingHom ℝ)
      (originalPoint F u z) = if i = R then v else 0 := by
    intro i
    by_cases hi : i = R
    · subst i
      have HV := FlatAffinePowerTower.height_value_original (Int.castRingHom ℝ) p D s a b raw (lastStage F u) h hs
      have HE := FlatAffinePowerTower.system_row p D (fun t : Fin (F.depth u + 1) => s t.val)
        (fun t => a t.val) (fun t => b t.val) (lastStage F u) (Sum.inr h.succ)
      exact HV.trans ((congrArg (fun q => q.eval₂ (Int.castRingHom ℝ) raw) HE).symm.trans (HR R))
    · exact (FlatAffinePowerTower.roots_except_original (Int.castRingHom ℝ) p D HD s a b raw R
        (fun i hi => (HR i).trans (ite_eq_right hi)) i hi).trans (ite_eq_right hi).symm
  have HRI : R = FlatAffineCriticalIndexedRows.multiplier (F.depth u) (Nat.lt_succ_self _) h.succ :=
    FlatAffinePowerTower.multiplier_eq (lastStage F u) h.succ
  rw [HRI] at HO
  exact HO

theorem ancestor_roots (F : Inputs) (u : List Bool) (h : Fin (arity F u))
    (hs : h ∈ FlatAffineFullSourceTower.free F u (F.depth u)) (v : ℝ)
    (z : Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ)
    (hz : ∀ i, (FlatAffinePowerPositive.system (next F) u i).eval₂ (Int.castRingHom ℝ) z =
      if i = rowIndex F u h then v else 0) :
    ∀ i, (FlatAffineFullSourceTower.system F u i).eval₂ (Int.castRingHom ℝ) (ancestorPoint F u z) = 0 := by
  apply FlatAffineTowerPartialRoots.prefix_roots (Int.castRingHom ℝ)
    (BoundedFullCriticalSamples.polynomial F.source u) (FlatAffineFullSourceTower.free F u)
    (FlatAffineFullSourceTower.direction F u) (FlatAffineFullSourceTower.level F u) h (originalPoint F u z)
  intro i hi
  exact (original_values F u h hs v z hz i).trans (ite_eq_right hi)

theorem continuous_ancestorPoint {T : Type*} [TopologicalSpace T] (F : Inputs) (u : List Bool)
    (z : T → Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ) (hz : Continuous z) :
    Continuous (fun t => ancestorPoint F u (z t)) := by
  have HR : Continuous (fun t => z t ∘ Fin.castSucc) := continuous_pi (fun i => (continuous_apply i.castSucc).comp hz)
  have HP := FlatAffinePowerTower.continuous_powerPoint (FlatAffinePowerControls.degree F u) _ HR
  exact continuous_pi (fun i => (continuous_apply
    (TriangularPolynomialRows.prefixIndex (stageWidth F u) (F.depth u) (F.depth u + 1) (by omega) i)).comp HP)

private theorem block_eq_multiplier_iff {n k : ℕ} (h : Fin n) (j : FlatAffineCriticalStage.Variables n) :
    TriangularPolynomialRows.block (FlatAffineCriticalTower.width n) k (k + 1) (by omega)
      (FlatAffineCriticalTower.blockEquiv n j) =
        FlatAffineCriticalIndexedRows.multiplier k (Nat.lt_succ_self k) h.succ ↔ j = Sum.inr h.succ := by
  constructor
  · intro he
    have HV := congrArg Fin.val he
    change k * FlatAffineCriticalTower.width n + (FlatAffineCriticalTower.blockEquiv n j).val =
      k * FlatAffineCriticalTower.width n + (FlatAffineCriticalTower.blockEquiv n (Sum.inr h.succ)).val at HV
    exact (FlatAffineCriticalTower.blockEquiv n).injective (Fin.ext (by omega))
  · intro he
    simp only [he, FlatAffineCriticalIndexedRows.multiplier]

private theorem source_eval {ι : Type*} {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (s : Finset (Fin n)) (a : Fin (n + 1) → Fin n → ℤ) (b : Fin n → MvPolynomial ι ℤ)
    (x : ι → ℝ) (y : Fin n → ℝ) (mu : Fin (n + 1) → ℝ) :
    (FlatAffineCriticalStage.row p s a b (Sum.inr 0)).eval₂ (Int.castRingHom ℝ) (Sum.elim x (Sum.elim y mu)) =
      p.eval₂ (Int.castRingHom ℝ) y := by
  rw [FlatAffineCriticalStage.row, Fin.cases_zero, eval₂_rename]
  rfl

private theorem height_eval {ι : Type*} {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (s : Finset (Fin n)) (a : Fin (n + 1) → Fin n → ℤ) (b : Fin n → MvPolynomial ι ℤ)
    (x : ι → ℝ) (y : Fin n → ℝ) (mu : Fin (n + 1) → ℝ) (j : Fin n) (hj : j ∈ s) :
    (FlatAffineCriticalStage.row p s a b (Sum.inr j.succ)).eval₂ (Int.castRingHom ℝ) (Sum.elim x (Sum.elim y mu)) =
      (∑ i, (a j.succ i : ℝ) * y i) - (b j).eval₂ (Int.castRingHom ℝ) x := by
  rw [FlatAffineCriticalStage.row, Fin.cases_succ, ite_eq_left hj, eval₂_sub, AffineHeightPolynomial.eval, eval₂_rename]
  rfl

theorem stage_values (F : Inputs) (u : List Bool) (h : Fin (arity F u))
    (hs : h ∈ FlatAffineFullSourceTower.free F u (F.depth u)) (v : ℝ)
    (z : Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ)
    (hz : ∀ i, (FlatAffinePowerPositive.system (next F) u i).eval₂ (Int.castRingHom ℝ) z =
      if i = rowIndex F u h then v else 0) (j : FlatAffineCriticalStage.Variables (arity F u)) :
    (FlatAffineCriticalStage.row (BoundedFullCriticalSamples.polynomial F.source u)
      (FlatAffineFullSourceTower.free F u (F.depth u)) (FlatAffineFullSourceTower.direction F u (F.depth u))
      (fun i => (FlatAffineFullSourceTower.level F u (F.depth u) i).polynomial) j).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (ancestorPoint F u z ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u))
        (Sum.elim (FlatAffineTowerPartialRoots.current (originalPoint F u z))
          (FlatAffineTowerPartialRoots.multipliers (originalPoint F u z)))) = if j = Sum.inr h.succ then v else 0 := by
  have HS := FlatAffineTowerPartialRoots.stage_value (Int.castRingHom ℝ)
    (BoundedFullCriticalSamples.polynomial F.source u) (FlatAffineFullSourceTower.free F u)
    (FlatAffineFullSourceTower.direction F u) (FlatAffineFullSourceTower.level F u) (originalPoint F u z) j
  have HV := original_values F u h hs v z hz
    (TriangularPolynomialRows.block (stageWidth F u) (F.depth u) (F.depth u + 1) (by omega)
      (FlatAffineCriticalTower.blockEquiv (arity F u) j))
  have HE := block_eq_multiplier_iff (k := F.depth u) h j
  have H := HS.trans HV
  by_cases hj : j = Sum.inr h.succ
  · exact H.trans ((ite_eq_left (HE.mpr hj)).trans (ite_eq_left hj).symm)
  · exact H.trans ((ite_eq_right (fun hi => hj (HE.mp hi))).trans (ite_eq_right hj).symm)

theorem spatial_mem_slice (F : Inputs) (u : List Bool) (h : Fin (arity F u))
    (hs : h ∈ FlatAffineFullSourceTower.free F u (F.depth u)) (v : ℝ)
    (z : Fin (FlatAffineFullSourcePositive.count (next F) u) → ℝ)
    (hz : ∀ i, (FlatAffinePowerPositive.system (next F) u i).eval₂ (Int.castRingHom ℝ) z =
      if i = rowIndex F u h then v else 0)
    (x : FlatAffinePowerSampleInput.OriginalRoots F u) (hx : ancestorPoint F u z = x.val) :
    spatialPoint F u z ∈ slice F u x h v := by
  let y := FlatAffineTowerPartialRoots.current (originalPoint F u z)
  let mu := FlatAffineTowerPartialRoots.multipliers (originalPoint F u z)
  let p := BoundedFullCriticalSamples.polynomial F.source u
  let s := FlatAffineFullSourceTower.free F u (F.depth u)
  let a := FlatAffineFullSourceTower.direction F u (F.depth u)
  let b (i : Fin (arity F u)) := (FlatAffineFullSourceTower.level F u (F.depth u) i).polynomial
  let old := ancestorPoint F u z ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u)
  have HY : y = spatialPoint F u z := funext (spatial_original F u z)
  have HP := stage_values F u h hs v z hz (Sum.inr 0)
  simp only [Sum.inr.injEq, (Fin.succ_ne_zero h).symm, ite_false] at HP
  have Hmem : y ∈ slice F u x h v := by
    refine ⟨(source_eval p s a b old y mu).symm.trans HP, ?_⟩
    intro j hj
    have HL := stage_values F u h hs v z hz (Sum.inr j.succ)
    simp only [Sum.inr.injEq, Fin.succ_inj] at HL
    have HD := (height_eval p s a b old y mu j hj).symm.trans HL
    have HE := congrArg (fun f => (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial.eval₂
      (Int.castRingHom ℝ) (f ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u))) hx
    change (∑ i, (a j.succ i : ℝ) * y i) - (b j).eval₂ (Int.castRingHom ℝ) old = _ at HD
    change _ = _ + _
    linarith
  exact HY ▸ Hmem

end LeanCanny.Encoding.FlatAffineShiftedSlice
