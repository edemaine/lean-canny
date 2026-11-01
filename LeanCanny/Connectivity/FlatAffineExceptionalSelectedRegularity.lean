/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineExceptionalCriticalHeightParameter
public import LeanCanny.Geometry.CoordinateConstraintSingularity
public import LeanCanny.Connectivity.FlatAffineSlabRegularSampling
/-! # Nonvanishing selected critical-height cuts imply full-slice regularity -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalSelectedRegularity
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)
open FlatAffineExceptionalCoarseRule (state)
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
  (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
  (hh : h u ∈ FlatAffineExceptionalOrderedRule.frozen F u)
  (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
  (φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
  (H : ∀ j, φ ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.numerator j) /
    ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.denominator j : ℝ) =
      FlatAffineExceptionalParentBank.values F C h u v a hv j)
  (hn : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = 2 * FermatCoordinateCone.normal j i)

include hh H hn in
theorem regular_of_values (t : ℝ)
    (ht : (FlatAffineExceptionalCriticalHeight.cut F C h S u hm).eval₂ φ.toRingHom t ≠ 0)
    (y : Fin (arity F u) → ℝ)
    (hy : y ∈ FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
      (FlatAffineExceptionalSliceFrame.scalar F C h u a+t)) :
    Function.Surjective (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
      (BoundedFullCriticalSamples.polynomial F.source u) (FlatAffineExceptionalOrderedRule.frozen F u)
      (FlatAffineFullSourceTower.direction F u (F.depth u)) y) := by
  by_contra HS
  apply ht
  apply FlatAffineExceptionalCriticalHeightParameter.cut_root F C h S u v a hm hh hv φ H hn t y hy
  apply CoordinateConstraintSingularity.outside_zero (BoundedFullCriticalSamples.polynomial F.source u)
    (FlatAffineExceptionalOrderedRule.frozen F u) (FlatAffineFullSourceTower.direction F u (F.depth u))
    (fun _ => 2) (fun _ => by decide) _ y hy.1 HS
  intro j i
  simpa only [FermatCoordinateCone.normal, mul_ite, mul_one, mul_zero] using hn j i

include hh H hn in
theorem regular_on (A B : ℝ)
    (ht : ∀ t ∈ Ioo A B, (FlatAffineExceptionalCriticalHeight.cut F C h S u hm).eval₂ φ.toRingHom t ≠ 0) :
    FlatAffineSlabRegularData.RegularOn F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
      (FlatAffineExceptionalSliceFrame.scalar F C h u a+A) (FlatAffineExceptionalSliceFrame.scalar F C h u a+B) := by
  intro t y hy
  let δ := t.val-FlatAffineExceptionalSliceFrame.scalar F C h u a
  have Hδ : δ ∈ Ioo A B := by dsimp only [δ]; constructor <;> linarith [t.property.1,t.property.2]
  have HE : FlatAffineExceptionalSliceFrame.scalar F C h u a+δ = t.val := by dsimp only [δ]; ring
  exact regular_of_values F C h S u v a hm hh hv φ H hn δ (ht δ Hδ) y (by simpa only [HE] using hy)

end LeanCanny.Connectivity.FlatAffineExceptionalSelectedRegularity
