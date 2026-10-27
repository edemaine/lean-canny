/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalProjection
public import LeanCanny.Encoding.BoundedFullComplexSamples
public import LeanCanny.Geometry.LinearProjectionFinite

/-! # Uniform annihilators for arbitrary bounded critical projections

Every raw weight record determines bounded integer projection weights. The
resulting nonzero polynomial annihilates all complex critical samples, even
when the weights do not separate them. Coordinate projections are included.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionFamily
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra BoundedFullWriter
open scoped Classical BigOperators

noncomputable def weights (P : Readers) (r : List Bool → List Bool) (c : List Bool)
    (i : Fin (P.dim c + 4)) : ℤ := BoundedCriticalSeparator.weight P r c i.val

noncomputable def polynomial (P : Readers) (r : List Bool → List Bool) (c : List Bool) : Polynomial ℤ :=
  LinearProjectionEliminant.polynomial (BoundedFullCriticalSamples.equations P c)
    (fun _ => degree P c) (weights P r c) (BoundedCriticalProjection.systemWidth P c)

theorem weight_bound (P : Readers) (r : List Bool → List Bool) (c : List Bool) (i : Fin (P.dim c + 4)) :
    (weights P r c i).natAbs ≤ 2 ^ BoundedCriticalSeparator.width P c :=
  (BoundedCriticalProjection.record_coordinate_lt _ (r c) i.val).le

theorem ne_zero (P : Readers) (r : List Bool → List Bool) (c : List Bool) : polynomial P r c ≠ 0 :=
  LinearProjectionEliminant.ne_zero _ _ _ _

theorem degree_le (P : Readers) (r : List Bool → List Bool) (c : List Bool) :
    (polynomial P r c).natDegree ≤ 2 ^ BoundedCriticalProjection.labelWidth P c := by
  simpa only [polynomial, FixedWidthPolynomial.count, ← pow_mul,
    BoundedCriticalProjection.labelWidth, Nat.mul_comm] using
    LinearProjectionEliminant.degree_le (BoundedFullCriticalSamples.equations P c)
      (fun _ => degree P c) (weights P r c) (BoundedCriticalProjection.systemWidth P c)

theorem coefficient_bits (P : Readers) (r : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    ((polynomial P r c).coeff k).natAbs.size ≤ BoundedCriticalProjection.coefficientBits P c := by
  have he := LinearProjectionEliminant.coefficient_size_le (BoundedFullCriticalSamples.equations P c)
    (fun _ => degree P c) (weights P r c) (BoundedCriticalProjection.systemWidth P c)
    (BoundedCriticalProjection.projectionBits P c) (BoundedCriticalProjection.equationBits P c)
    (BoundedCriticalSeparator.width P c)
    (fun j e => (MvMass.coeff_le _ _).trans (BoundedCriticalProjection.equations_mass P c j))
    (weight_bound P r c) (BoundedCriticalProjection.projection_mass_bound P c) k
  simpa only [FixedWidthPolynomial.count, ← pow_mul, polynomial,
    BoundedCriticalProjection.coefficientBits, BoundedCriticalProjection.labelWidth,
    Nat.mul_comm, Nat.add_assoc, Nat.reduceAdd] using he

theorem eval_sample (P : Readers) (r : List Bool → List Bool) (c : List Bool)
    (x : BoundedFullComplexSamples.Samples P c) :
    (polynomial P r c).eval₂ (Int.castRingHom ℂ) (BoundedFullComplexSamples.value P r c x.val) = 0 := by
  have hpos : 0 < degree P c := by
    have := BoundedRegularSource.powerDegree_gt_one (size P c)
    change 0 < BoundedZeroSource.powerDegree (size P c)
    omega
  have hlevel : Macaulay.level (AffineCoordinateSystem.degrees (fun _ : Fin (P.dim c + 4) => degree P c)) =
      (P.dim c + 4) * (degree P c - 1) + 1 := by
    simp [Macaulay.level, AffineCoordinateSystem.degrees, Fin.sum_univ_succ]
  have hf : {y : Fin (P.dim c + 4) → ℂ | ∀ j,
      (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom ℂ) y = 0}.Finite := by
    have := (BoundedFullComplexSamples.finite_samples P c).1
    exact Set.toFinite _
  have he := LinearProjectionEliminant.eval_eq_zero_of_finite (Int.castRingHom ℂ)
    (BoundedFullCriticalSamples.equations P c) (fun _ => degree P c)
    (BoundedFullCriticalSamples.equations_degree P c) (fun _ => hpos) (weights P r c)
    (BoundedCriticalProjection.systemWidth P c) (by rw [hlevel]; exact Nat.lt_size_self _)
    hf x.val x.property
  simpa only [polynomial, BoundedFullComplexSamples.value, weights, Int.coe_castRingHom,
    Int.cast_natCast, mul_comm] using he

end LeanCanny.Encoding.BoundedProjectionFamily
