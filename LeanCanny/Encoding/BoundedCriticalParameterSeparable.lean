/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleLabels

/-! # Simplicity of the constructed parent parameter roots

The native parameter is the polynomial of a separable integer primitive
element. Its derivative is nonzero at every root, including roots removed
later by the actual-sample filter. No new squarefree computation is needed.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalRationalCoordinates
open LeanCanny.Algebra BoundedFullWriter Polynomial

theorem parameter_separable {L : Type*} [Field L] [CharZero L] (P : Readers) (c : List Bool) :
    ((parameter P c).map (Int.castRingHom L)).Separable :=
  (FiniteAnnihilatorTree.parameter
    (fun i => (BoundedCriticalLeafSource.family P).polynomial
      (pair (BoundedCriticalLeafSource.prepare P c) (BinaryNatCode.encode i)))
    (count P (BoundedCriticalLeafSource.prepare P c)) (nonzero P (BoundedCriticalLeafSource.prepare P c))).separable_in_field

theorem parameter_derivative_ne_zero {L : Type*} [Field L] [CharZero L]
    (P : Readers) (c : List Bool) (t : L) (ht : (parameter P c).eval₂ (Int.castRingHom L) t = 0) :
    (parameter P c).derivative.eval₂ (Int.castRingHom L) t ≠ 0 := by
  have H := (parameter_separable (L := L) P c).eval₂_derivative_ne_zero (RingHom.id L)
    (x := t) (by simpa only [Polynomial.eval₂_map, RingHom.id_comp] using ht)
  simpa only [Polynomial.derivative_map, Polynomial.eval₂_map, RingHom.id_comp] using H

theorem parameter_derivative_at_sample (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    (parameter P c).derivative.eval₂ (Int.castRingHom ℝ) (BoundedCriticalSampleLabels.parameter P c x).val ≠ 0 :=
  parameter_derivative_ne_zero P c _
    ((BoundedCriticalSampleLabels.mem_rootSet P c _).mp (BoundedCriticalSampleLabels.parameter P c x).property).1

end LeanCanny.Encoding.BoundedCriticalRationalCoordinates
