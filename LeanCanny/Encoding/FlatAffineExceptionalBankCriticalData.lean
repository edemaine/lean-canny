/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalBankLevels
public import LeanCanny.Encoding.FlatAffineExceptionalBankDenominator

/-! # Concrete critical data over the actual exceptional parent bank

The integer low polynomial and Fermat degree remain the original source.
All frozen levels are the constructed integral affine numerators, and the
coordinate scales include their actual nonzero common denominator. Thus
an exceptional norm degree controls the coefficient prefix, while the next
spatial critical problem retains the original source degree.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalParentBank
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births width)
open scoped Classical BigOperators

private theorem coordinateNormal_succ {n : ℕ} (b : ℤ) (c : Fin (n + 1) → ℤ)
    (r j i : Fin (n + 1)) : PhysicalPowerCriticalRows.coordinateNormals b c r j.succ i =
      if i = j then c j else 0 := rfl

noncomputable def sourceLeading (F : Inputs) (u : List Bool) : ℤ :=
  IntegerRegularSource.leading (F.source.dim u + 3) 1 (FlatAffinePowerControls.degree F u)
    (BoundedRegularSource.sourceMassExponent (F.source.dim u) (BoundedFullWriter.size F.source u)
      (BoundedFullWriter.size F.source u) (F.source.radius u))

noncomputable def criticalData (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (r : Fin (arity F u)) (hr : r ∉ FlatAffineFullSourceTower.free F u (F.depth u)) :
    IntegralHistorySampler.CriticalData
      (bank F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix (F.source.dim u + 3) where
  heights := shiftedNumerator F C h S u (hm.trans (Nat.le_succ S))
  low := FlatAffinePowerPositive.lower F u
  leading := sourceLeading F u
  objective := 2
  scales _ := 2 * denominator F C h S u (hm.trans (Nat.le_succ S))
  frozen := FlatAffineFullSourceTower.free F u (F.depth u)
  free := r
  degree := FlatAffinePowerControls.degree F u
  birth_bound := hm
  degree_two := by
    change 2 ≤ BoundedZeroSource.powerDegree (BoundedFullWriter.size F.source u)
    have H := BoundedRegularSource.powerDegree_gt_one (BoundedFullWriter.size F.source u)
    omega
  low_degree := FlatAffinePowerPositive.lower_degree F u
  leading_ne := IntegerRegularSource.leading_ne_zero 1 _ _ (by decide)
  objective_ne := by decide
  scales_ne _ := mul_ne_zero (by decide) (denominator_ne_zero F C h S u _)
  free_not_frozen := hr

theorem criticalData_source (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (r : Fin (arity F u)) (hr : r ∉ FlatAffineFullSourceTower.free F u (F.depth u)) :
    FermatCriticalHomogenization.polynomial (criticalData F C h S u hm r hr).low
      (criticalData F C h S u hm r hr).leading (criticalData F C h S u hm r hr).degree =
        BoundedFullCriticalSamples.polynomial F.source u :=
  (FlatAffinePowerPositive.source_eq F u).symm

theorem criticalData_degree (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (r : Fin (arity F u)) (hr : r ∉ FlatAffineFullSourceTower.free F u (F.depth u)) :
    (criticalData F C h S u hm r hr).degree = FlatAffinePowerControls.degree F u := rfl

theorem critical_arity (F : Inputs) (u : List Bool) :
    Fintype.card (IntegralIntegerRootBank.Index (Fin (FlatAffineFullSourcePositive.count F u)) (births F u) ⊕
      FlatAffineCriticalStage.Variables (arity F u)) =
        2 * FlatAffineFullSourcePositive.count F u + 2 * arity F u + 2 := by
  calc
    _ = Fintype.card (IntegralIntegerRootBank.Index (Fin (FlatAffineFullSourcePositive.count F u)) (births F u)) +
      (arity F u + (arity F u + 1)) := by simp only [Fintype.card_sum, FlatAffineCriticalStage.Variables, Fintype.card_fin]
    _ = _ := by rw [physical_arity]; omega

/-- The constructed critical slice is exactly the independently represented
exceptional slice whenever the source has the actual doubled coordinate normals. -/
theorem criticalData_slice (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
    (r : Fin (arity F u)) (hr : r ∉ FlatAffineFullSourceTower.free F u (F.depth u))
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (φ : (bank F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (H : ∀ i, φ ((bank F C h S u (hm.trans (Nat.le_succ S))).bank.numerator i) /
      ((bank F C h S u (hm.trans (Nat.le_succ S))).bank.denominator i : ℝ) = values F C h u v a hv i)
    (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = 2 * FermatCoordinateCone.normal j i) :
    @FlatAffineSlicePresentation.set (arity F u) (BoundedFullCriticalSamples.polynomial F.source u)
      (criticalData F C h S u hm r hr).frozen
      (fun j i => PhysicalPowerCriticalRows.coordinateNormals (criticalData F C h S u hm r hr).objective
        (criticalData F C h S u hm r hr).scales (criticalData F C h S u hm r hr).free j.succ i)
      (fun j => φ ((criticalData F C h S u hm r hr).heights j)) =
        FlatAffineExceptionalSliceFrame.slice F C h u v a hv := by
  rw [FlatAffineExceptionalSliceFrame.slice_eq]
  let Q := denominator F C h S u (hm.trans (Nat.le_succ S))
  have HQ : (Q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (denominator_ne_zero F C h S u _)
  have HA (j i : Fin (arity F u)) :
      ((PhysicalPowerCriticalRows.coordinateNormals (criticalData F C h S u hm r hr).objective
        (criticalData F C h S u hm r hr).scales (criticalData F C h S u hm r hr).free j.succ i : ℤ) : ℝ) =
      (Q : ℝ) * (FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i : ℝ) := by
    have HN : PhysicalPowerCriticalRows.coordinateNormals (criticalData F C h S u hm r hr).objective
        (criticalData F C h S u hm r hr).scales (criticalData F C h S u hm r hr).free j.succ i =
        if i = j then 2 * Q else 0 := coordinateNormal_succ _ _ _ _ _
    rw [HN, hnormal]
    by_cases hi : i = j <;> simp only [FermatCoordinateCone.normal, hi, ite_true, ite_false,
      Int.cast_mul, Int.cast_ofNat, Int.cast_zero, mul_zero]; ring
  ext y
  change ((_ = 0 ∧ ∀ j ∈ FlatAffineFullSourceTower.free F u (F.depth u), _) ↔
    (_ = 0 ∧ ∀ j ∈ FlatAffineFullSourceTower.free F u (F.depth u), _))
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  simp only []
  rw [show φ ((criticalData F C h S u hm r hr).heights j) = _ from
    shiftedNumerator_eval F C h S u v a (hm.trans (Nat.le_succ S)) hv φ H j]
  simp only [HA]
  rw [show (∑ i, (Q : ℝ) * (FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i : ℝ) * y i) =
      (Q : ℝ) * ∑ i, (FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i : ℝ) * y i by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
  constructor
  · exact mul_left_cancel₀ HQ
  · exact congrArg ((Q : ℝ) * ·)

end LeanCanny.Encoding.FlatAffineExceptionalParentBank
