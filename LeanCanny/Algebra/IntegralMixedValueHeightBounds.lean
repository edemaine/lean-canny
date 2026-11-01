/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueSystemBounds
public import LeanCanny.Algebra.IntegralMixedValueDeterminantMetadata

/-! # Original-root raw heights for the actual equation-value cut

The literal mapped system supplies every Macaulay entry bound. Its actual
Gram determinant and the two nilpotent digit selections then bound every
raw old-bank coefficient, including label zero and out-of-cap queries.
All budgets have native metadata computations. No raw value-factor height
or Gram matrix reader is an input to this construction.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueHeightBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial IntegralCoordinateBasis
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedCoordinateBounds
open IntegralMixedVirtualSweepSource
open scoped Classical

def columns (F : Family) (q : List Bool) : ℕ := count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
  (IntegralMixedGridValue.width (F.spatial q) (F.rule q))

def rank (F : Family) (q : List Bool) : ℕ := count (F.birth q + 2) (F.width q)

def rows (F : Family) (q : List Bool) : ℕ := (F.ambient q - (F.rule q).critical.offset.val + 1 + 2) * columns F q

noncomputable def height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool) : ℕ :=
  IntegralRelativeCharacteristicBounds.determinantHeight (columns F q) (rank F q)
    (IntegralMacaulayGramBounds.gramHeight (rows F q) (rank F q) (IntegralMixedValueSystemBounds.height F I H q))

theorem determinant_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (i : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (u v : Fin (count (F.birth q + 2) (F.width q))) :
    (Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
      (IntegralMixedValueDoubleNilpotent.matrix (F.state q) (F.birth_bound q) (F.rule q) i).det u v).natAbs ≤
        2 ^ height F I H q := by
  rw [IntegralMixedValueDoubleSystem.matrix_eq]
  exact IntegralMacaulayGramBounds.determinant_height (IntegralMixedValueDoubleNilpotent.basis (F.state q))
    (IntegralMixedValueDoubleSystem.mappedSystem F q i)
    (RelativeProjectiveValueGram.degrees
      (fun _ => IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)) (F.spatial q).degree)
    (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) (IntegralMixedValueSystemBounds.height F I H q)
    (IntegralMixedValueSystemBounds.mapped_coefficient_height F I H q i) u v

theorem coefficient_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (index : Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (k : ℕ) (u v : Fin (count (F.birth q) (F.width q))) :
    (IntegralMixedCutMatrix.coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q)
      (.value (I.coordinate q) index) k u v).natAbs ≤ 2 ^ height F I H q := by
  by_cases Hk : k < 2 ^ F.width q
  · by_cases Hzero : index.val = 0
    · have HE : index = ⟨0, by change 0 < IntegralMixedGridValue.dimension (F.spatial q) (F.rule q) + 2; omega⟩ := Fin.ext Hzero
      have HZ : IntegralMixedCutNilpotent.value (F.state q) (F.birth_bound q) (F.rule q)
          (.value (I.coordinate q) index) = 0 := by
        rw [HE]
        exact IntegralMixedValueMatrixSource.nilpotent_value_zero _ _ _ _
      rw [← IntegralMixedCutNilpotent.coefficient (F.state q) (F.birth_bound q) (F.rule q)
        (.value (I.coordinate q) index) (F.scalar_cap q) ⟨k, Hk⟩ u v, HZ, map_zero, Matrix.zero_apply, Int.natAbs_zero]
      exact Nat.zero_le _
    · rw [← IntegralMixedValueDoubleNilpotent.raw_coefficient (F.state q) (F.birth_bound q) (F.rule q)
        (I.coordinate q) index (by omega) (F.scalar_cap q) ⟨k, Hk⟩ u v]
      exact determinant_height F I H q (I.coordinate q) _ _
  · rw [IntegralMixedCutNilpotent.coefficient_outside _ _ _ _ (F.scalar_cap q) k (by omega),
      Matrix.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _

noncomputable def rawBounds (F : Family) (I : Indices F) (H : OriginalBounds F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (hkind : ∀ q, F.kind q = .value (I.coordinate q) (index q)) : RawBounds F where
  height := height F I H
  bound q k u v := by
    rw [hkind]
    exact coefficient_height F I H q (index q) k u v

theorem height_binary (F : Family) (I : Indices F) (H : OriginalBounds F)
    (h : IntegralMixedVirtualNativeBits.Metadata F I) (hM : BinaryFn H.rank) (hW : UnaryFn H.sourceWidth)
    (hD : BinaryFn H.spatialDegree) (hS : BinaryFn F.cap) (hL : BinaryFn H.nodes) (hG : BinaryFn H.bankHeight) :
    BinaryFn (height F I H) := by
  have HC : BinaryFn (columns F) := IntegralMixedValueDeterminantMetadata.columns_binary F I h
  have HR : BinaryFn (rank F) := ((BinaryFn.const 2).powUnary h.width).powUnary (h.birth.add (UnaryFn.const 2))
  have HA : BinaryFn (rows F) := ((BinaryFn.ofUnary (IntegralMixedVirtualNativeBits.free_unary F I h)).add
    (BinaryFn.const 2)).mul HC
  have HP := IntegralMixedValueSystemBounds.height_binary F I H h hM hW hD hS hL hG
  exact IntegralRelativeCharacteristicBounds.determinantHeight_binary HC HR
    (IntegralMacaulayGramBounds.gramHeight_binary HA HR HP)

theorem rawBounds_height_binary (F : Family) (I : Indices F) (H : OriginalBounds F)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound (F.spatial q) (F.rule q)))
    (hkind : ∀ q, F.kind q = .value (I.coordinate q) (index q))
    (h : IntegralMixedVirtualNativeBits.Metadata F I) (hM : BinaryFn H.rank) (hW : UnaryFn H.sourceWidth)
    (hD : BinaryFn H.spatialDegree) (hS : BinaryFn F.cap) (hL : BinaryFn H.nodes) (hG : BinaryFn H.bankHeight) :
    BinaryFn (rawBounds F I H index hkind).height := height_binary F I H h hM hW hD hS hL hG

end LeanCanny.Algebra.IntegralMixedValueHeightBounds
