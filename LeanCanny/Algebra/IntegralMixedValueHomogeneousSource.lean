/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogeneousSystemCoefficientSemantics
public import LeanCanny.Algebra.IntegralMixedValueSystemActual

/-! # Actual homogeneous value rows use restored rows or virtual coordinates

The original source supplies the value-test row. Coordinate requests read
the actual virtual critical coordinate polynomial of that same source.
Degrees and both widths derive from the fixed original spatial source.
Only the emitted current coefficient reply is used in each proof.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueHomogeneousSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedVirtualSweepSource
open IntegralMixedVirtualNativeBits IntegralMixedValueDoubleSystem
open scoped Classical

noncomputable abbrev parameters (F : Family) : HomogeneousSystemCoefficientRequest.Parameters where
  free q := F.ambient q - (F.rule q).critical.offset.val + 1
  width q := IntegralMixedGridValue.width (F.spatial q) (F.rule q)
  degree q := (F.spatial q).degree
  coordinateDegree q := IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)
  rank q := count (F.birth q + 1) (F.width q)

theorem controls (F : Family) (I : Indices F) (h : Metadata F I) : HomogeneousSystemCoefficientRequest.Controls (parameters F) where
  free := free_unary F I h
  width := IntegralMixedValueDeterminantMetadata.width_unary F I h
  degree := h.degree
  coordinateDegree := IntegralMixedValueDeterminantMetadata.coordinateDegree_binary F I h
  rank := rank_binary F I h

noncomputable abbrev program (F : Family) := HomogeneousSystemCoefficientRequest.program (parameters F)

theorem program_controls (F : Family) (I : Indices F) (h : Metadata F I) : (program F).Controls :=
  HomogeneousSystemCoefficientRequest.controls _ (controls F I h)

theorem value_zero (F : Family) (I : Indices F) (reply : List Bool → List Bool) (q : List Bool)
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q)))
    (ha : HomogenizationLayout.weightedSum (F.ambient q - (F.rule q).critical.offset.val + 1)
        (F.ambient q - (F.rule q).critical.offset.val + 1)
        (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val = (F.spatial q).degree →
      reply (HomogeneousSystemCoefficientRequest.query (parameters F)
        (MacaulayFullBoxBits.entryPacket q 0 k.val u.val v.val)) =
        residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
          ((IntegralMixedVirtualOriginalRows.row F q (I.coordinate q)).coeff
            (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q))
              (Nat.fromBitsLE (k.val.bits.drop (IntegralMixedGridValue.width (F.spatial q) (F.rule q)))))) u v : ℤ) :
                ZMod (I.modulus q))) :
    (program F).value reply (MacaulayFullBoxBits.entryPacket q 0 k.val u.val v.val) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        ((RelativeValueSystemMap.homogeneousTest (IntegralMixedVirtualOriginalRows.row F q (I.coordinate q))
          (F.spatial q).degree).coeff
            (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val)) u v : ℤ) :
              ZMod (I.modulus q)) := by
  exact HomogeneousSystemCoefficientSemantics.value_zero (parameters F) q k u v
    (IntegralMixedVirtualOriginalRows.row F q (I.coordinate q))
    (fun z => residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis z u v : ℤ) :
      ZMod (I.modulus q)))
    (by simp only [map_zero, Matrix.zero_apply, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits])
    reply (by
      intro H
      have HA := ha H
      rw [HomogeneousSystemCoefficientSemantics.query_zero_packet] at HA
      exact HA)

theorem coordinate_row (F : Family) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1)) :
    AffineRingCoordinates.homogeneousRows (coordinates F q)
      (fun _ => IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)) j =
      RelativeValueSystemMap.homogeneousTest
        ((IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q) (F.rule q) j).toMvPolynomial j)
          (IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)) := by
  rw [HomogeneousCoefficientRequest.homogeneousRows_eq]
  rfl

theorem coordinate_entry (F : Family) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (e : Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1) →₀ ℕ)
    (u v : Fin (count (F.birth q + 1) (F.width q))) :
    Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      ((AffineRingCoordinates.homogeneousRows (coordinates F q)
        (fun _ => IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)) j).coeff e) u v =
    Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      ((RelativeValueSystemMap.homogeneousTest
        ((IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q) (F.rule q) j).toMvPolynomial j)
          (IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q))).coeff e) u v :=
  congrArg (fun p : MvPolynomial (Fin (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)) (Coefficient F q) =>
    Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis (p.coeff e) u v) (coordinate_row F q j)

theorem value_succ (F : Family) (I : Indices F) (reply : List Bool → List Bool) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q)))
    (ha : HomogeneousSystemCoefficientRequest.request (parameters F)
        (MacaulayFullBoxBits.entryPacket q j.succ.val k.val u.val v.val) →
      reply (HomogeneousSystemCoefficientRequest.query (parameters F)
        (MacaulayFullBoxBits.entryPacket q j.succ.val k.val u.val v.val)) =
        residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
          ((IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q) (F.rule q) j).coeff
            (entry (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val (j.val + 1))) u v : ℤ) : ZMod (I.modulus q))) :
    (program F).value reply (MacaulayFullBoxBits.entryPacket q j.succ.val k.val u.val v.val) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        ((RelativeValueSystemMap.homogeneousTest
          ((IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q) (F.rule q) j).toMvPolynomial j)
          (IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q))).coeff
            (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val)) u v : ℤ) : ZMod (I.modulus q)) := by
  exact HomogeneousSystemCoefficientSemantics.value_succ (parameters F) q j k u v
    (IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q) (F.rule q) j)
    (fun z => residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis z u v : ℤ) :
      ZMod (I.modulus q)))
    (by simp only [map_zero, Matrix.zero_apply, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits])
    reply (by
      intro H
      have HA := ha ((HomogeneousSystemCoefficientSemantics.request_succ_packet (parameters F) q j k u v).mpr H)
      rw [HomogeneousSystemCoefficientSemantics.query_succ_packet] at HA
      exact HA)

end LeanCanny.Algebra.IntegralMixedValueHomogeneousSource
