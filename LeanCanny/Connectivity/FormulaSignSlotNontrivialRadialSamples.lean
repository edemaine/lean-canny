/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotCandidateRadialDescriptor
public import Mathlib.Topology.Order.IntermediateValue
/-! # Radial samples also exist at interior points of nontrivial pieces -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotNontrivialRadialSamples
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR Set
open FormulaSignSlotMarginProjection FormulaSignSlotComponentMaxima FormulaSignSlotMarginMaxima
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial

private theorem positive_lift (c : List Bool) (i : Vertex (CanonicalAuxiliaryCandidateCover.width c))
    (x : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (hx : x ∈ FormulaSignSlotRadialAccess.projectedPiece c
      ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i)) :
    ∃ p : Positive c, p ∈ (CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i ∧
      (projection c p.val).val = x := by
  obtain ⟨s,⟨p,hp,rfl⟩,hx⟩ := hx
  exact ⟨p,hp,hx⟩

theorem arbitrarily_small_samples (c : List Bool) (i : Vertex (CanonicalAuxiliaryCandidateCover.width c))
    (a : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (ha : a ∈ FormulaSignSlotRadialAccess.projectedPiece c
      ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i))
    (hn : ∃ z ∈ FormulaSignSlotRadialAccess.projectedPiece c
      ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i), z ≠ a)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < ε ∧ r ∉ FormulaSignSlotRadialParameterEliminant.bad c a ∧
      ∃ z : FormulaSignSlotTiltedRadialGrid.OldPositive c a r,
        FormulaSignSlotTiltedRadialGrid.originalPositive c a r z ∈
          (CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i ∧
        z.val.val ∈ FormulaSignSlotRadialParameterGrid.grid c a r := by
  obtain ⟨p0,hp0,HP0⟩ := positive_lift c i a ha
  obtain ⟨z,hz,hza⟩ := hn
  obtain ⟨p1,hp1,HP1⟩ := positive_lift c i z hz
  let f : Positive c → ℝ := fun p => SquaredDistanceFibers.value a (projection c p.val).val
  have HF : Continuous f := (SquaredDistanceFibers.continuous_value a).comp
    (continuous_subtype_val.comp ((proper_projection c).continuous.comp continuous_subtype_val))
  have H0 : f p0 = 0 := (SquaredDistanceFibers.zero_iff a _).mpr HP0
  have H1 : 0 < f p1 := by
    have HN : f p1 ≠ 0 := fun h => hza (HP1.symm.trans ((SquaredDistanceFibers.zero_iff a _).mp h))
    exact lt_of_le_of_ne (SquaredDistanceFibers.nonneg a _) HN.symm
  have HC : IsPreconnected ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i) := by
    have HPath : IsPathConnected ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i) :=
      isPathConnected_iff.mpr ⟨⟨p0,hp0⟩,fun x hx y hy =>
        (CanonicalAuxiliaryCandidateLabelLock.positiveCover c).paths i x hx y hy⟩
    exact HPath.isConnected.isPreconnected
  obtain ⟨b,hb,HB⟩ := FormulaSignSlotRadialParameterGrid.small_interval c a
  let r := min ε (min b (f p1))/2
  have HM : 0 < min ε (min b (f p1)) := lt_min hε (lt_min hb H1)
  have HR : 0 < r := by dsimp [r]; positivity
  have HRM : r < min ε (min b (f p1)) := by dsimp [r]; linarith
  have HRE : r < ε := HRM.trans_le (min_le_left _ _)
  have HRB : r < b := HRM.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have HRF : r < f p1 := HRM.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have HI : r ∈ Icc (f p0) (f p1) := ⟨by rw [H0]; exact HR.le, HRF.le⟩
  obtain ⟨p,hp,HP⟩ := HC.intermediate_value hp0 hp1 HF.continuousOn HI
  have HBad := HB r ⟨HR,HRB⟩
  have HS : p.val ∈ sourceSphere c a r := HP
  obtain ⟨w,hw,_,hgrid⟩ := FormulaSignSlotRadialParameterGrid.sample_same_piece c a r HR.le HBad
    ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i)
    ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).clopen i) p hp HS
  exact ⟨r,HR,HRE,HBad,w,hw,hgrid⟩

end LeanCanny.Connectivity.FormulaSignSlotNontrivialRadialSamples
