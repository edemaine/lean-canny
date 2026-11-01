/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueDoubleSystem
public import LeanCanny.Algebra.IntegralMixedVirtualCoordinateBounds
public import LeanCanny.Algebra.IntegralMixedVirtualOriginalRowBounds
public import LeanCanny.Algebra.IntegralMacaulayGramBounds
public import LeanCanny.Algebra.IntegralReciprocalSystemBounds

/-! # Actual double-nilpotent system coefficient bounds

Coordinate and full original-row bounds pass through homogenization and
the reciprocal equation. The integer constant term is included. The
second nilpotent matrix reads one of these same coefficients, so no new
row or system height assumption is introduced.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueSystemBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial IntegralCoordinateBasis Polynomial MvPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedCoordinateBounds
open IntegralMixedVirtualSweepSource IntegralMixedValueDoubleSystem
open scoped Classical

noncomputable def height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool) : ℕ :=
  IntegralMixedVirtualCoordinateBounds.height F H q + IntegralMixedVirtualOriginalRowBounds.height F I H q + 1

theorem coordinate_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1) →₀ ℕ)
    (u v : Fin (count (F.birth q + 1) (F.width q))) :
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      ((coordinates F q j).coeff e) u v).natAbs ≤ 2 ^ IntegralMixedVirtualCoordinateBounds.height F H q := by
  rw [coordinates, DiagonalParameterBits.coefficient]
  split_ifs
  · exact IntegralMixedVirtualCoordinateBounds.coefficient_height F I H q j _ u v
  · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _

theorem system_coefficient_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (i : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1))
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1) →₀ ℕ) (k : ℕ)
    (u v : Fin (count (F.birth q + 1) (F.width q))) :
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      (((system F q i j).coeff e).coeff k) u v).natAbs ≤ 2 ^ height F I H q := by
  let b := (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
  unfold system
  exact IntegralReciprocalSystemBounds.coefficient_height b
    (AffineRingCoordinates.homogeneousRows (coordinates F q)
      (fun _ => IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)))
    (RelativeValueSystemMap.homogeneousTest (IntegralMixedVirtualOriginalRows.row F q i) (F.spatial q).degree)
    (F.spatial q).degree (IntegralMixedVirtualCoordinateBounds.height F H q)
    (IntegralMixedVirtualOriginalRowBounds.height F I H q)
    (fun j => IntegralMacaulayGramBounds.homogeneous_height b (coordinates F q j) _ _ (coordinate_height F I H q j))
    (IntegralMacaulayGramBounds.homogeneous_height b _ _ _
      (IntegralMixedVirtualOriginalRowBounds.coefficient_height F I H q i)) j e k u v


theorem mapped_coefficient_height (F : Family) (I : Indices F) (H : OriginalBounds F) (q : List Bool)
    (i : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1))
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1) →₀ ℕ)
    (u v : Fin (count (F.birth q + 2) (F.width q))) :
    (Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
      ((mappedSystem F q i j).coeff e) u v).natAbs ≤ 2 ^ height F I H q := by
  obtain ⟨⟨u, a⟩, rfl⟩ := (pairIndex (F.birth q + 1) (F.width q)).surjective u
  obtain ⟨⟨v, c⟩, rfl⟩ := (pairIndex (F.birth q + 1) (F.width q)).surjective v
  rw [mappedSystem, MvPolynomial.coeff_map, IntegralMixedValueDoubleNilpotent.basis_matrix]
  split_ifs
  · exact system_coefficient_height F I H q i j e _ u v
  · exact Nat.zero_le _

theorem height_binary (F : Family) (I : Indices F) (H : OriginalBounds F)
    (h : IntegralMixedVirtualNativeBits.Metadata F I) (hM : BinaryFn H.rank) (hW : UnaryFn H.sourceWidth)
    (hD : BinaryFn H.spatialDegree) (hS : BinaryFn F.cap) (hL : BinaryFn H.nodes) (hG : BinaryFn H.bankHeight) :
    BinaryFn (height F I H) :=
  ((IntegralMixedVirtualCoordinateBounds.height_binary F H h.ambient hM hW hD hS hL hG).add
    (IntegralMixedVirtualOriginalRowBounds.height_binary F I H h hS hL hG)).add (BinaryFn.const 1)

end LeanCanny.Algebra.IntegralMixedValueSystemBounds
