/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPrefix
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendOwnPoint
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPaddingPoint
/-! # Actual source-critical seed points exist for every prepared proper provider root -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem critical_transport {n m : ℕ} (Q : SpatialSource n) (V : SpatialSource m)
    (hn : n=m) (hq : HEq Q V)
    (H : ∃p : Fin (n+1)→ℝ,
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
      ∀i,i≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    ∃p : Fin (m+1)→ℝ,
      (FermatCriticalHomogenization.polynomial V.low V.leading V.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
      ∀i,i≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial V.low V.leading V.degree)).eval₂
        (Int.castRingHom ℝ) p=0 := by
  subst m
  cases eq_of_heq hq
  exact H
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

theorem exists_padding_critical (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (l r : List Bool) (side : Bool) :
    ∃p : Fin (FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (preparedRoot old l r side)+1)→ℝ,
      (FermatCriticalHomogenization.polynomial
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old l r side)).low
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old l r side)).leading
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old l r side)).degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
      ∀i,i≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old l r side)).low
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old l r side)).leading
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old l r side)).degree)).eval₂ (Int.castRingHom ℝ) p=0 := by
  have H := FormulaSignSlotRadialProviderRetainedAppend.exists_padding_critical old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old) (FormulaSignSlotRadialProviderRetainedAppend.ownPoint old hv)
    (FormulaSignSlotRadialProviderRetainedAppend.own_occurrence old hv).zero
  have HP := (FormulaSignSlotRadialProviderRetainedAppend.prepared_provider old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old)).trans (prepared_provider old l r side).symm
  exact critical_transport _ _ (FormulaSignSlotRadialProviderRecordPrefix.ambient _ _ HP)
    (FormulaSignSlotRadialProviderRecordPrefix.source_heq _ _ HP) H

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
