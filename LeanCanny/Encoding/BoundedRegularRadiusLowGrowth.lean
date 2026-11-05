/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedRegularRadiusLowModel
public import LeanCanny.Encoding.BoundedRegularLowHeight

/-! # Actual original-source coefficient growth in the dyadic radius

Only the value of the retained parameter varies. The source coefficient
height has an affine bound whose slope and offset use original syntax alone.
This supplies actual evaluation estimates for subsequent interpolation.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedRegularRadiusLowModel
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation Polynomial

def heightOffset (n D b : ℕ) := BoundedRegularSource.regularizationExponent n D b 0 +
  BoundedRegularSource.lowMassExponent n D b 0 + 1

def heightSlope (n D : ℕ) :=
  BoundedRegularRadius.regularizationSlope n D + BoundedRegularRadius.sourceMassSlope n D

theorem native_height_affine (n D b R : ℕ) :
    BoundedRegularSource.regularizationExponent n D b R +
      BoundedRegularSource.lowMassExponent n D b R + 1 = heightSlope n D * R + heightOffset n D b := by
  have h := BoundedRegularRadius.source_mass_affine n D b R
  unfold BoundedRegularSource.sourceMassExponent at h
  rw [BoundedRegularRadius.regularization_affine]
  unfold heightSlope heightOffset
  rw [Nat.add_mul]
  omega

theorem source_coefficient_growth (n : ℕ) (t : ETR.Term) (R : ℕ) (e : Fin (n + 4) →₀ ℕ) :
    (((low (t.finitePolynomial n) t.toData.size t.toData.size).coeff e).eval ((2 : ℤ) ^ R)).natAbs ≤
      2 ^ (heightSlope n t.toData.size * R + heightOffset n t.toData.size t.toData.size) := by
  have HF := source_fields (fun _ => n) (fun _ => t) (fun _ => R) []
  have HC := congrArg (fun p => p.coeff e) HF.1
  rw [MvPolynomial.coeff_map] at HC
  change ((Polynomial.evalRingHom ((2 : ℤ) ^ R))
    ((low (t.finitePolynomial n) t.toData.size t.toData.size).coeff e)).natAbs ≤ _
  rw [HC]
  have h := BoundedRegularLowHeight.coefficient
    (BoundedRegularLowCoefficient.readers (fun _ => n) (fun _ => t) (fun _ => R)) [] e
  convert h using 1
  simp only [BoundedRegularLowHeight.height, BoundedRegularLowHeight.lowMass,
    BoundedRegularLowCoefficient.readers, BoundedFullWriter.regularizationExponent,
    BoundedFullWriter.size, BoundedSourceWriter.regularizationExponent, BoundedSourceWriter.size,
    BoundedFullWriter.controls, ETR.TermView.term_toBits]
  rw [native_height_affine]

theorem heightSlope_binary {n D : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn D) :
    BinaryFn (fun q => heightSlope (n q) (D q)) :=
  (BoundedRegularRadius.regularizationSlope_binary hn hD).add
    (((BoundedRegularRadius.perturbationSlope_binary hn hD).add (BinaryFn.const 4)).add
      (BoundedZeroControls.powerDegree_binary hD))

theorem heightOffset_binary {n D b : List Bool → ℕ}
    (hn : UnaryFn n) (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (fun q => heightOffset (n q) (D q) (b q)) :=
  ((BoundedRegularControls.regularizationExponent_binary hn hD hb (BinaryFn.const 0)).add
    ((((BoundedZeroControls.perturbationExponent_binary hn hD hb (BinaryFn.const 0)).add
      (BoundedZeroControls.massExponent_binary hn hb (BinaryFn.const 0))).add
      (BoundedZeroControls.penaltyExponent_binary hn hD (BinaryFn.const 0))).add (BinaryFn.const 1))).add
    (BinaryFn.const 1)

end LeanCanny.Encoding.BoundedRegularRadiusLowModel
