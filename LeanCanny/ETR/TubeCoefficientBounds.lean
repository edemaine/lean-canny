/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeSource
public import LeanCanny.ETR.PolynomialMass
public import LeanCanny.Geometry.TubeCoefficientMass

/-! # FP coefficient bit budgets for the encoded ETR tube systems

The expanded integer tube and projection polynomials have coefficient mass
at most `2^(20*N^2+6*N+21)`, where `N` is the normalized compiled term size.
Every coefficient therefore needs at most `20*N^2+6*N+22` magnitude bits.
The bound has an FP writer and is uniform over active sets and equation rows.
It does not yet supply a coefficient-access machine.
-/

@[expose] public section

namespace LeanCanny.ETR.CompactSource

theorem polynomial_mass (bits : List Bool) :
    Algebra.MvMass.mass (polynomial bits) ≤ 2 ^ (size bits + 2 * size bits ^ 2) := by
  rw [size_eq]
  exact (term bits).compactPolynomial_mass

end LeanCanny.ETR.CompactSource

namespace LeanCanny.ETR.TubeSource

open LeanCanny.Encoding
open Geometry Algebra.MvMass

def massBudget (N : ℕ) : ℕ := 20 * N ^ 2 + 6 * N + 21
def coefficientBits (bits : List Bool) : List Bool := BinaryNatCode.encode (massBudget (CompactSource.size bits) + 1)

theorem coefficientBits_FP : coefficientBits ∈ FP := by
  have h := bits_mem_FP ((((UnaryFn.const 20).mul (CompactSource.size_unary.pow_const 2)).add
    ((UnaryFn.const 6).mul CompactSource.size_unary)).add (UnaryFn.const 22))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem constraint_count_le_size (bits : List Bool) :
    Fintype.card (PerturbedSource.Index bits) ≤ 2 + 2 * CompactSource.size bits := by
  have ha := (CompactSource.term bits).arity_le_dataSize
  rw [← CompactSource.size_eq] at ha
  change Fintype.card (PolynomialPerturbation.Constraint (Fin (CompactSource.term bits).arity)) ≤ _
  rw [PolynomialPerturbation.constraint_card, Fintype.card_fin]
  omega

theorem integer_polynomial_mass_le (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    mass (integerPolynomial bits s) ≤ 2 ^ massBudget (CompactSource.size bits) := by
  have h := (TubePolynomial.integer_polynomial_mass (CompactSource.polynomial bits) s).trans
    (TubePolynomial.massBound_le_pow _ _ _ (CompactSource.polynomial_mass bits))
  apply h.trans
  apply Nat.pow_le_pow_right (by decide)
  have hc := constraint_count_le_size bits
  unfold massBudget
  change 2 * (CompactSource.size bits + 2 * CompactSource.size bits ^ 2) +
    2 * Fintype.card (PerturbedSource.Index bits) + 8 ≤ _
  omega

theorem integer_projection_mass_le (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : ProjectionIndex bits) : mass (integerProjection bits s j) ≤ 2 ^ massBudget (CompactSource.size bits) := by
  have h := TubePolynomial.integer_projection_mass (CompactSource.polynomial bits) s j
  have hm := TubePolynomial.massBound_le_pow
    (Fintype.card (PerturbedSource.Index bits)) _ _ (CompactSource.polynomial_mass bits)
  let D := 4 * max (CompactSource.polynomial bits).totalDegree 2 + 1
  have hD : D ≤ 2 ^ D := Nat.lt_two_pow_self.le
  apply h.trans (Nat.mul_le_mul hD hm) |>.trans
  rw [← pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have hc := constraint_count_le_size bits
  have hd := CompactSource.polynomial_degree bits
  rw [← CompactSource.size_eq] at hd
  unfold massBudget D
  have hmax : max (CompactSource.polynomial bits).totalDegree 2 ≤ 4 * CompactSource.size bits ^ 2 + 2 := by omega
  omega

theorem integer_polynomial_coefficient_bits (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (m : TubePolynomial.IntegerCoordinate (Fin (CompactSource.term bits).arity) →₀ ℕ) :
    ((integerPolynomial bits s).coeff m).natAbs.size ≤ Nat.fromBitsLE (coefficientBits bits) := by
  have h := Nat.size_le_size ((coeff_le _ m).trans (integer_polynomial_mass_le bits s))
  simpa only [Nat.size_pow, coefficientBits, BinaryNatCode.encode, Nat.fromBitsLE_bits] using h

theorem integer_projection_coefficient_bits (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : ProjectionIndex bits) (m : IntegerProjectionVariable bits →₀ ℕ) :
    ((integerProjection bits s j).coeff m).natAbs.size ≤ Nat.fromBitsLE (coefficientBits bits) := by
  have h := Nat.size_le_size ((coeff_le _ m).trans (integer_projection_mass_le bits s j))
  simpa only [Nat.size_pow, coefficientBits, BinaryNatCode.encode, Nat.fromBitsLE_bits] using h

end LeanCanny.ETR.TubeSource
