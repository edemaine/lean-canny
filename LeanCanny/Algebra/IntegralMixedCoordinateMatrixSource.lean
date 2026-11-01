/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCutNilpotent

/-! # Actual relative action matrices behind coordinate cut coefficients

The nilpotent coordinate-factor value is one RELATIVE characteristic
coefficient, followed by the original integer clearing-leading power.
The displayed action matrix uses the original spatial source and actual
swept retained heights. Its relative dimension is fixed by the spatial
source; the old algebra only enters the eventual block representation.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoordinateMatrixSource
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCoordinateTrailing
open IntegralCoordinateBasis FixedWidthPolynomial Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def denominator (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) : ℤ :=
  CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales

noncomputable def leading (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) : ℤ :=
  (P.leading * denominator x hm r ^ P.degree) * P.degree

noncomputable def action (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) :
    Matrix (Fin (PurePowerReductionBounds.dimension (n - r.critical.offset.val + 1) P.degree))
      (Fin (PurePowerReductionBounds.dimension (n - r.critical.offset.val + 1) P.degree))
      (Polynomial x.sampler.scalarPrefix.carrier) :=
  PurePowerRelativeAnnihilator.actionMatrix (objective r)
    (FermatCoordinateCriticalReduction.degrees (objective r) P.degree)
    (ClearedCoordinateCritical.lower P.degree (denominator x hm r : Polynomial x.sampler.scalarPrefix.carrier)
      (CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r))
      r.critical.offset.val (fit r).le
      (P.low.map (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier)))
      (P.leading : Polynomial x.sampler.scalarPrefix.carrier) (objective r))
    (leading x hm r : Polynomial x.sampler.scalarPrefix.carrier)
    (PurePowerReductionBounds.bound (n - r.critical.offset.val + 1) P.degree)
    (ClearedCoordinateCritical.grid_bound (objective r) P.degree)
    (PurePowerReductionBounds.bound_lt _ _) j

theorem coordinate_eq (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) :
    coordinate x hm r j = ScaledGradedReductionAnnihilator.polynomial (action x hm r j)
      (leading x hm r : Polynomial x.sampler.scalarPrefix.carrier)
      (PurePowerReductionBounds.bound (n - r.critical.offset.val + 1) P.degree + 1) := by
  unfold coordinate CoordinateFrozenCriticalElimination.polynomial ClearedCoordinateCritical.annihilator
    PurePowerRelativeAnnihilator.polynomial action leading denominator
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rfl

theorem nilpotent_value (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (ChoiceBound P r)) :
    IntegralMixedCutNilpotent.value x hm r (.coordinate j i) =
      ((action x hm r j).map (AdjoinRoot.mk (X ^ (2 ^ B)))).charpoly.coeff i.val *
        (leading x hm r : AdjoinRoot (X ^ (2 ^ B) : Polynomial x.sampler.scalarPrefix.carrier)) ^
          ((PurePowerReductionBounds.bound (n - r.critical.offset.val + 1) P.degree + 1) * i.val) := by
  change AdjoinRoot.mk _ ((coordinate x hm r j).coeff i.val) = _
  rw [coordinate_eq, ScaledGradedReductionAnnihilator.coefficient, map_mul, map_pow, map_intCast,
    Matrix.charpoly_map, Polynomial.coeff_map]

theorem nilpotent_matrix (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (ChoiceBound P r)) :
    Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
      (IntegralMixedCutNilpotent.value x hm r (.coordinate j i)) =
      leading x hm r ^ ((PurePowerReductionBounds.bound (n - r.critical.offset.val + 1) P.degree + 1) * i.val) •
        Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
          (((action x hm r j).map (AdjoinRoot.mk (X ^ (2 ^ B)))).charpoly.coeff i.val) := by
  rw [nilpotent_value, mul_comm, ← Int.cast_pow]
  change (Algebra.leftMulMatrix _)
    ((algebraMap ℤ _) (leading x hm r ^ _) * _) = _
  rw [map_mul, AlgHom.commutes, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

end LeanCanny.Algebra.IntegralMixedCoordinateMatrixSource
