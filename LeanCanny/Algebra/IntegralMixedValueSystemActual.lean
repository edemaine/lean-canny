/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueSystemSemantics

/-! # The native reciprocal selector reads the actual mapped system

The requested homogeneous row retains the same original source and value
test. Its old basis indices are exactly those obtained by deleting the
second nilpotent digit. The only reply premise concerns that one emitted
homogeneous coefficient, without a Gram or system coefficient evaluator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueSystemActual
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCoordinateBasis
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource IntegralMixedVirtualSweepSource
open IntegralMixedValueSystemControls IntegralMixedValueSystemSemantics IntegralMixedValueDoubleSystem
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis

theorem value_zero (F : Family) (I : Indices F) (reply : List Bool → List Bool) (q : List Bool)
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q))
    (ha : c.val ≤ a.val ∧ a.val - c.val = 1 →
      reply (MacaulayFullBoxBits.entryPacket q 0 k.val u.val v.val) = residueBits
        ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
          ((RelativeValueSystemMap.homogeneousTest (IntegralMixedVirtualOriginalRows.row F q (I.coordinate q)) (F.spatial q).degree).coeff
            (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val)) u v : ℤ) :
              ZMod (I.modulus q))) :
    (program F I).value reply (packet F I q 0 k u v a c) = residueBits
      ((Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
        ((mappedSystem F q (I.coordinate q) 0).coeff
          (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val))
        (pairIndex (F.birth q + 1) (F.width q) (u, a))
        (pairIndex (F.birth q + 1) (F.width q) (v, c)) : ℤ) : ZMod (I.modulus q)) := by
  let x : ℤ := Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
    ((RelativeValueSystemMap.homogeneousTest (IntegralMixedVirtualOriginalRows.row F q (I.coordinate q)) (F.spatial q).degree).coeff
      (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val)) u v
  have H := zero_value F I reply q k u v a c x ha
  have HE := IntegralReciprocalEntry.mapped_zero F q (I.coordinate q)
    (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val) u v a c
  have HE' : Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
      ((mappedSystem F q (I.coordinate q) 0).coeff
        (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val))
      (pairIndex (F.birth q + 1) (F.width q) (u, a))
      (pairIndex (F.birth q + 1) (F.width q) (v, c)) =
      if c.val ≤ a.val then (if a.val - c.val = 1 then x else 0) -
        (if a.val - c.val = 0 ∧ k.val = (F.spatial q).degree ∧ u = v then 1 else 0) else 0 := by
    simpa only [chart_target F I q k] using HE
  exact H.trans (congrArg (fun z : ℤ => residueBits (z : ZMod (I.modulus q))) HE'.symm)

theorem value_succ (F : Family) (I : Indices F) (reply : List Bool → List Bool) (q : List Bool)
    (j : Fin (F.ambient q - (F.rule q).critical.offset.val + 1))
    (k : Fin (count (F.ambient q - (F.rule q).critical.offset.val + 1 + 1)
      (IntegralMixedGridValue.width (F.spatial q) (F.rule q))))
    (u v : Fin (count (F.birth q + 1) (F.width q))) (a c : Fin (2 ^ F.width q))
    (ha : a.val = c.val → reply (MacaulayFullBoxBits.entryPacket q j.succ.val k.val u.val v.val) =
      residueBits ((Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        ((AffineRingCoordinates.homogeneousRows (coordinates F q) (fun _ => IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)) j).coeff
          (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val)) u v : ℤ) :
            ZMod (I.modulus q))) :
    (program F I).value reply (packet F I q j.succ k u v a c) = residueBits
      ((Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
        ((mappedSystem F q (I.coordinate q) j.succ).coeff
          (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val))
        (pairIndex (F.birth q + 1) (F.width q) (u, a))
        (pairIndex (F.birth q + 1) (F.width q) (v, c)) : ℤ) : ZMod (I.modulus q)) := by
  let x : ℤ := Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
    ((AffineRingCoordinates.homogeneousRows (coordinates F q) (fun _ => IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial q) (F.rule q)) j).coeff
      (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val)) u v
  have H := succ_value F I reply q j k u v a c x ha
  have HE := IntegralReciprocalEntry.mapped_succ F q (I.coordinate q) j
    (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val) u v a c
  have HT : c.val ≤ a.val ∧ a.val - c.val = 0 ↔ a.val = c.val := by omega
  have HE' : Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis (F.state q))
      ((mappedSystem F q (I.coordinate q) j.succ).coeff
        (nativeExponent (Equiv.refl _) (IntegralMixedGridValue.width (F.spatial q) (F.rule q)) k.val))
      (pairIndex (F.birth q + 1) (F.width q) (u, a))
      (pairIndex (F.birth q + 1) (F.width q) (v, c)) = if a.val = c.val then x else 0 := by
    simpa only [HT] using HE
  exact H.trans (congrArg (fun z : ℤ => residueBits (z : ZMod (I.modulus q))) HE'.symm)

end LeanCanny.Algebra.IntegralMixedValueSystemActual
