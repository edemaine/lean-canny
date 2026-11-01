/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCriticalSweep

/-! # The actual original source and gradient tests on the relative grid

The tests are the immutable integer Fermat source and its free gradients,
cleared by the current frozen coordinates. Specialization is proved equal
to the original selected-parent equation at the reconstructed spatial point,
times one explicit nonzero denominator power. Thus grid pruning is exact.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSweepRows
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedCriticalSweep
open MvPolynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def integerRow (P : SpatialSource n) (r : Rule n) (i : Fin (n - r.critical.offset.val + 1)) :
    MvPolynomial (Fin (n + 1)) ℤ :=
  if i = objective r then FermatCriticalHomogenization.polynomial P.low P.leading P.degree else
    pderiv (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i)
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)

noncomputable def denominator (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) : ℤ :=
  CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales

noncomputable def numerators (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) :=
  CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r)

noncomputable def row (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) :
    MvPolynomial (Fin (n - r.critical.offset.val + 1)) (Polynomial x.sampler.scalarPrefix.carrier) :=
  ClearedCoordinateBlock.specialize P.degree (denominator x hm r : Polynomial x.sampler.scalarPrefix.carrier)
    (numerators x hm r) r.critical.offset.val (n - r.critical.offset.val + 1)
    ((integerRow P r i).map (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier)))

noncomputable def point (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ)
    (z : Fin (n - r.critical.offset.val + 1) → ℝ) : Fin (n + 1) → ℝ :=
  ClearedCoordinateBlock.point (evaluation x φ t)
    (denominator x hm r : Polynomial x.sampler.scalarPrefix.carrier) (numerators x hm r) r.critical.offset.val z

theorem denominator_ne_zero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) : denominator x hm r ≠ 0 :=
  CoordinateFrozenCriticalElimination.denominator_ne_zero _ (data x hm r.critical).scales_ne

theorem integerRow_degree (P : SpatialSource n) (r : Rule n) (i : Fin (n - r.critical.offset.val + 1)) :
    (integerRow P r i).totalDegree ≤ P.degree := by
  have H := FermatCriticalHomogenization.polynomial_degree P.low P.leading P.degree P.low_degree
  unfold integerRow
  split_ifs
  · exact H
  · exact (PartialDerivativeDegree.degree_le _ _).trans ((Nat.sub_le _ _).trans H)

theorem row_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) : (row x hm r i).totalDegree ≤ P.degree :=
  (ClearedCoordinateBlock.degree _ _ _ _ _ _).trans
    ((PolynomialMapDegree.degree_le _ _).trans (integerRow_degree P r i))

theorem numerators_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (i : ℕ) :
    (numerators x hm r i).natDegree ≤ 1 := by
  unfold numerators CoordinateFrozenCriticalElimination.numerators
  split_ifs with hi
  · unfold CommonIntegerDenominator.numerator
    exact Polynomial.natDegree_mul_le.trans (by
      rw [Polynomial.natDegree_intCast, Nat.add_zero]
      exact heights_degree x r ⟨i, hi⟩)
  · simp only [Polynomial.natDegree_zero, Nat.zero_le]

theorem row_parameter_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) : PolynomialCoefficientDegree.Bound (row x hm r i) P.degree := by
  have Hlow : PolynomialCoefficientDegree.Bound
      ((integerRow P r i).map (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier))) 0 := by
    intro v
    rw [MvPolynomial.coeff_map]
    exact (Polynomial.natDegree_intCast _).le
  have HQ : (denominator x hm r : Polynomial x.sampler.scalarPrefix.carrier) =
      Polynomial.C (denominator x hm r : x.sampler.scalarPrefix.carrier) := (Polynomial.C_eq_intCast _).symm
  unfold row
  rw [HQ]
  simpa only [Nat.mul_one, Nat.zero_add] using ClearedCoordinateParameterDegree.specialize P.degree
    (denominator x hm r : x.sampler.scalarPrefix.carrier) (numerators x hm r) r.critical.offset.val
    (n - r.critical.offset.val + 1) 0 1 _
    ((PolynomialMapDegree.degree_le _ _).trans (integerRow_degree P r i)) Hlow (numerators_degree x hm r)

theorem row_specialization (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (t : ℝ) (z : Fin (n - r.critical.offset.val + 1) → ℝ) :
    (row x hm r i).eval₂ (evaluation x φ t) z =
      (denominator x hm r : ℝ) ^ P.degree * (integerRow P r i).eval₂ (Int.castRingHom ℝ) (point x hm r φ t z) := by
  have HQ : evaluation x φ t (denominator x hm r : Polynomial x.sampler.scalarPrefix.carrier) ≠ 0 := by
    rw [map_intCast]
    exact Int.cast_ne_zero.mpr (denominator_ne_zero x hm r)
  have H := ClearedCoordinateBlock.eval (evaluation x φ t) P.degree
    (denominator x hm r : Polynomial x.sampler.scalarPrefix.carrier) (numerators x hm r)
    r.critical.offset.val
    ((integerRow P r i).map (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier)))
    ((PolynomialMapDegree.degree_le _ _).trans (integerRow_degree P r i)) HQ z
  rw [map_intCast, evaluation_integer_source] at H
  exact H

theorem row_zero_iff (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (t : ℝ) (z : Fin (n - r.critical.offset.val + 1) → ℝ) :
    (row x hm r i).eval₂ (evaluation x φ t) z = 0 ↔
      (integerRow P r i).eval₂ (Int.castRingHom ℝ) (point x hm r φ t z) = 0 := by
  rw [row_specialization]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero _ (Int.cast_ne_zero.mpr (denominator_ne_zero x hm r))))

end LeanCanny.Algebra.IntegralMixedSweepRows
