/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerModel
/-! # Root, word, and rank bounds for the lower native child writers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank

theorem birth_le (F : Scripts) (q : List Bool) : birth F.toParameters q ≤ birthCap F.toParameters (RankedHistoryTask.root q) :=
  min_le_right _ _

theorem frame_matrix (F : Scripts) (p : Phase) (z : List Bool) (hp : p.code < phase (pairFst z)) :
    Frame F (pairFst z) (IntegralCriticalFlatMatrixQuery.writer F.toParameters p z) :=
  ⟨IntegralCriticalFlatMatrixQuery.writer_root F.toParameters p z,
    IntegralCriticalFlatMatrixQuery.writer_length F.toParameters p z, IntegralCriticalFlatMatrixQuery.writer_lower_rank F.toParameters p z hp⟩

theorem frame_grid (F : Scripts) (p : Phase) (z : List Bool) (hp : p.code < phase (pairFst z)) :
    Frame F (pairFst z) (IntegralCriticalFlatGridBits.writer F.toParameters p z) :=
  ⟨IntegralCriticalFlatGridBits.writer_root F.toParameters p z,
    IntegralCriticalFlatGridBits.writer_length F.toParameters p z, IntegralCriticalFlatGridBits.writer_lower_rank F.toParameters p z hp⟩

theorem frame_factor (F : Scripts) (p : Phase) (z : List Bool) (hp : p.code < phase (pairFst z)) :
    Frame F (pairFst z) (IntegralCriticalFlatFactorQuery.writer F.toParameters p z) :=
  ⟨IntegralCriticalFlatFactorQuery.writer_root F.toParameters p z,
    IntegralCriticalFlatFactorQuery.writer_length F.toParameters p z, IntegralCriticalFlatFactorQuery.writer_lower_rank F.toParameters p z hp⟩

theorem frame_coordinate (F : Scripts) (p : Phase) (z : List Bool) (hp : p.code < phase (pairFst z)) :
    Frame F (pairFst z) (IntegralCriticalFlatCoordinateQuery.writer F.toParameters p z) :=
  ⟨IntegralCriticalFlatCoordinateQuery.writer_root F.toParameters p z,
    IntegralCriticalFlatCoordinateQuery.writer_length F.toParameters p z, IntegralCriticalFlatCoordinateQuery.writer_lower_rank F.toParameters p z hp⟩

theorem frame_next (F : Scripts) (p : Phase) (q : List Bool) (hp : p.code < phase q) :
    Frame F q (IntegralCriticalFlatEulerBits.next F.toParameters p q) := by
  refine ⟨IntegralCriticalFlatEulerBits.next_root F.toParameters p q, ?_,
    IntegralCriticalFlatEulerBits.next_lower_rank F.toParameters p q hp⟩
  exact child_length F.toParameters id (birth F.toParameters) p
    (RankedHistoryFields.read (numericCap F.toParameters) 16) q (birth_le F q)

theorem frame_spatial (F : Scripts) (p : Phase) (e : ℕ) (z : List Bool) (hp : p.code < phase (pairFst z)) :
    Frame F (pairFst z) (IntegralCriticalFlatEulerRowsBits.spatial F.toParameters p e z) := by
  refine ⟨IntegralCriticalFlatEulerRowsBits.spatial_root F.toParameters p e z, ?_,
    IntegralCriticalFlatEulerRowsBits.spatial_lower_rank F.toParameters p e z hp⟩
  exact child_length F.toParameters pairFst (birth F.toParameters ∘ pairFst) p
    (IntegralCriticalFlatEulerRowsBits.spatialReader F.toParameters e) z (birth_le F (pairFst z))

theorem frame_derivative (F : Scripts) (z : List Bool) (hp : isPhase .derivativeCoefficient (IntegralDerivativeBits.original z)) :
    Frame F (IntegralDerivativeBits.original z) (IntegralCriticalFlatDerivativeQuery.writer F.toParameters z) :=
  ⟨IntegralCriticalFlatDerivativeQuery.writer_root F.toParameters z,
    IntegralCriticalFlatDerivativeQuery.writer_length F.toParameters z,
    IntegralCriticalFlatDerivativeQuery.writer_lower_rank F.toParameters z hp⟩

end LeanCanny.Algebra.IntegralCriticalNativeLowerBits
