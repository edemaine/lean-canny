/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCoordinateSquarefree
public import LeanCanny.Algebra.IntegralMixedValueTrailing
public import LeanCanny.Geometry.PolynomialCoordinateProper
/-! # Proper selected-parent grids and their literal physical critical points

The old algebra homomorphism remains fixed throughout. The physical point
uses the same cleared frozen heights and the actual free coordinates.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedGeometry
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

abbrev Free (r : Rule n) := Fin (n - r.critical.offset.val + 1)

noncomputable def rows (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (i : Free r) :=
  (IntegralMixedSweepRows.row x hm r i).map (Polynomial.mapRingHom φ.toRingHom)

noncomputable def original (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) := PolynomialRootFamily.value (rows x hm r φ)

theorem original_apply (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (z : Free r → ℝ) (i : Free r) :
    original x hm r φ (t,z) i = (IntegralMixedSweepRows.row x hm r i).eval₂ (evaluation x φ t) z := by
  unfold original PolynomialRootFamily.value rows
  rw [MvPolynomial.eval₂_map]
  rfl

theorem original_zero_iff (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (z : Free r → ℝ) :
    original x hm r φ (t,z) = 0 ↔ ∀ i,
      (IntegralMixedSweepRows.integerRow P r i).eval₂ (Int.castRingHom ℝ) (IntegralMixedSweepRows.point x hm r φ t z) = 0 := by
  constructor
  · intro H i
    apply (IntegralMixedSweepRows.row_zero_iff x hm r i φ t z).mp
    simpa only [original_apply, Pi.zero_apply] using congrFun H i
  · intro H
    funext i
    rw [original_apply]
    exact (IntegralMixedSweepRows.row_zero_iff x hm r i φ t z).mpr (H i)

theorem point_free (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (z : Free r → ℝ) (i : Free r) :
    IntegralMixedSweepRows.point x hm r φ t z (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i) = z i := by
  unfold IntegralMixedSweepRows.point ClearedCoordinateBlock.point ClearedCoordinateCritical.freeIndex
  rw [dite_eq_left (by change r.critical.offset.val ≤ r.critical.offset.val + i.val ∧ r.critical.offset.val + i.val < r.critical.offset.val + (n - r.critical.offset.val + 1); have H := i.isLt; constructor <;> omega)]
  congr 1
  apply Fin.ext
  simp

theorem point_frozen (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (z : Free r → ℝ) (i : Fin (n+1))
    (hi : i.val < r.critical.offset.val) :
    ((data x hm r.critical).scales i : ℝ) * IntegralMixedSweepRows.point x hm r φ t z i = heightValue x r φ t i := by
  unfold IntegralMixedSweepRows.point ClearedCoordinateBlock.point
  rw [dite_eq_right (by omega)]
  unfold IntegralMixedSweepRows.numerators CoordinateFrozenCriticalElimination.numerators
  rw [dite_eq_left i.isLt, map_intCast]
  change ((data x hm r.critical).scales i : ℝ) * ((evaluation x φ t)
    (CommonIntegerDenominator.numerator Finset.univ (data x hm r.critical).scales (heights x r) i) /
      (CommonIntegerDenominator.denominator Finset.univ (data x hm r.critical).scales : ℝ)) = _
  rw [CommonIntegerDenominator.recover (evaluation x φ t) Finset.univ (data x hm r.critical).scales
    (heights x r) (fun j _ => (data x hm r.critical).scales_ne j) i (Finset.mem_univ i), evaluation_heights]
  exact mul_div_cancel₀ _ (Int.cast_ne_zero.mpr ((data x hm r.critical).scales_ne i))

theorem capture (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (z : Free r → ℝ)
    (hz : original x hm r φ (t,z) = 0) (j : Free r) :
    (selected x hm r j φ).eval₂ (Polynomial.evalRingHom t) (z j) = 0 := by
  have H := (original_zero_iff x hm r φ t z).mp hz
  have HP := H (objective r)
  simp only [IntegralMixedSweepRows.integerRow, ite_true] at HP
  have HR := coordinate_root x hm r j φ t (IntegralMixedSweepRows.point x hm r φ t z)
    (fun i hi => point_frozen x hm r φ t z i hi) HP (fun i hi => by
      simpa only [IntegralMixedSweepRows.integerRow, ite_eq_right hi] using H i)
  rwa [point_free] at HR

theorem selected_leading (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (j : Free r) (t : ℝ) :
    (selected x hm r j φ).leadingCoeff.eval t ≠ 0 := by
  have HD := specialized_degree x hm r j φ t
  have HS := IntegralMixedCoordinateSquarefree.selected_degree x hm r j φ
  have HE : ((selected x hm r j φ).map (Polynomial.evalRingHom t)).natDegree = (selected x hm r j φ).natDegree := HD.trans HS.symm
  rcases Polynomial.natDegree_map_eq_iff.mp HE with HL | HZ
  · exact HL
  · have HP : 0 < IntegralMixedCoordinateSquarefree.coordinateDegree P r := pow_pos (Nat.two_pow_pos _) _
    omega

theorem proper (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    IsProperMap (RootProjection.projection (PolynomialRootFamily.value (UnivariateRootFamily.diagonal (fun j => selected x hm r j φ)))) :=
  PolynomialCoordinateProper.proper _ (fun j t => selected_leading x hm r φ j t)

end LeanCanny.Connectivity.IntegralMixedSelectedGeometry
