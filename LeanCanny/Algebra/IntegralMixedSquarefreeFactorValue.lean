/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSquarefreeLeading
public import LeanCanny.Algebra.IntegralMixedPscCharacteristicOutput
public import LeanCanny.Algebra.IntegralMixedPscCharacteristicDeterminant
/-! # Actual squarefree matrix entries are scalar times PSC determinant entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
attribute [local irreducible] IntegralMixedCutNilpotent.basis IntegralMixedSquarefreeMatrixSource.matrix

noncomputable def integer (P : Parameters) (F : Family) (q : List Bool) : ℤ :=
  IntegralMixedSquarefreeLeading.integer ((IntegralMixedVirtualTaskBits.family P F).state q)
    ((IntegralMixedVirtualTaskBits.family P F).birth_bound q) ((IntegralMixedVirtualTaskBits.family P F).rule q)
noncomputable def integerValue (P : Parameters) (F : Family) (q : List Bool) : ℤ :=
  Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)).finBasis
    (IntegralMixedCutNilpotent.value ((IntegralMixedVirtualTaskBits.family P F).state q)
      ((IntegralMixedVirtualTaskBits.family P F).birth_bound q) ((IntegralMixedVirtualTaskBits.family P F).rule q)
      (.squarefree ((IntegralMixedVirtualTaskBits.indices P F).coordinate q) (IntegralMixedPscEntryBits.index P F q)))
    ((IntegralMixedVirtualTaskBits.indices P F).row q) ((IntegralMixedVirtualTaskBits.indices P F).col q)
noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (integerValue P F q : ZMod (modulus P q))

theorem value_length (P : Parameters) (F : Family) (q : List Bool) [NeZero (modulus P q)] :
    (value P F q).length ≤ (modulus P q).size := residueBits_length_le _ _

theorem product_integer (P : Parameters) (F : Family) (q : List Bool)
    (hr : get P .row q < (IntegralMixedPscUpperBits.characteristic P F).rank q)
    (ht : get P .col q < (IntegralMixedPscUpperBits.characteristic P F).rank q) :
    integerValue P F q = integer P F q * IntegralCriticalTotalSnapshotBits.integerEntry
      ((IntegralMixedPscUpperBits.characteristic P F).coefficientMatrix q 0) (get P .row q) (get P .col q) := by
  have H := congrArg (fun M => M ((IntegralMixedVirtualTaskBits.indices P F).row q)
    ((IntegralMixedVirtualTaskBits.indices P F).col q))
    (IntegralMixedSquarefreeLeading.matrix_scalar ((IntegralMixedVirtualTaskBits.family P F).state q)
      ((IntegralMixedVirtualTaskBits.family P F).birth_bound q) ((IntegralMixedVirtualTaskBits.family P F).rule q)
      ((IntegralMixedVirtualTaskBits.indices P F).coordinate q) (IntegralMixedPscEntryBits.index P F q))
  have HR : ((IntegralMixedVirtualTaskBits.indices P F).row q).val = get P .row q := Nat.mod_eq_of_lt hr
  have HT : ((IntegralMixedVirtualTaskBits.indices P F).col q).val = get P .col q := Nat.mod_eq_of_lt ht
  have HE := IntegralCriticalTotalSnapshotBits.integerEntry_fin
    ((IntegralMixedPscUpperBits.characteristic P F).coefficientMatrix q 0)
    ((IntegralMixedVirtualTaskBits.indices P F).row q) ((IntegralMixedVirtualTaskBits.indices P F).col q)
  rw [HR, HT] at HE
  rw [HE]
  change integerValue P F q = integer P F q *
    (IntegralMixedPscCharacteristicBits.source P F).coefficientMatrix q 0
      ((IntegralMixedVirtualTaskBits.indices P F).row q) ((IntegralMixedVirtualTaskBits.indices P F).col q)
  rw [IntegralMixedPscCharacteristicBits.coefficient_zero]
  exact H

theorem coordinate_top (F : Family) (key : List Bool) (j : ℕ) :
    IntegralMixedVirtualQueryBits.matrixCoefficient F key j
      (IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial key) (F.rule key)) 0 0 =
      IntegralMixedSquarefreeLeading.integer (F.state key) (F.birth_bound key) (F.rule key) := by
  rw [IntegralMixedValueCoordinateChild.matrixCoefficient_eq, IntegralMixedSquarefreeLeading.image_top,
    map_intCast, Matrix.intCast_apply, ite_eq_left rfl, Int.cast_id]

end LeanCanny.Algebra.IntegralMixedSquarefreeFactorBits
