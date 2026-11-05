/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicSquarefreeExceptional
public import LeanCanny.Algebra.SymbolicScaledSquarefreeBounds
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Parameter coefficient mass of the actual squarefree exceptional cut

The selected unsigned PSC is bounded by its actual subresultant determinant.
The exponent is affine in the input coefficient-height bound and independent
of which GCD order the polynomial selects.
-/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicScaledSquarefree
open Polynomial PrincipalSubresultant
open scoped Classical

def exceptionalMassBound (D H : ℕ) : ℕ := H + gcdMassExponent D H

theorem gcdMassExponent_mono {D E H G : ℕ} (hD : D ≤ E) (hH : H ≤ G) :
    gcdMassExponent D H ≤ gcdMassExponent E G := by
  have h2 : 2 * D ≤ 2 * E := Nat.mul_le_mul_left 2 hD
  exact Nat.add_le_add
    (Nat.mul_le_mul (Nat.size_le_size h2) h2)
    (Nat.mul_le_mul h2 (Nat.add_le_add hH (Nat.size_le_size hD)))

theorem exceptionalMassBound_mono {D E H G : ℕ} (hD : D ≤ E) (hH : H ≤ G) :
    exceptionalMassBound D H ≤ exceptionalMassBound E G :=
  Nat.add_le_add hH (gcdMassExponent_mono hD hH)

theorem exceptional_mass (p : Polynomial Coefficient) (H : ℕ)
    (hH : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ H) :
    coefficientMass (exceptional p) ≤ 2 ^ exceptionalMassBound p.natDegree H := by
  have hl : coefficientMass p.leadingCoeff ≤ 2 ^ H := hH p.natDegree
  have hs : coefficientMass (if p.natDegree = 0 then (1 : Coefficient) else
      psc p p.derivative p.natDegree p.derivative.natDegree (degree p)) ≤
      2 ^ gcdMassExponent p.natDegree H := by
    split_ifs
    · simpa only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one] using
        Nat.one_le_two_pow (n := gcdMassExponent p.natDegree H)
    · simpa only [subresultantCoeff_self] using
        subresultant_coefficient_mass p H hH (degree p) (degree p)
  exact (coefficientMass_mul_le _ _).trans
    ((Nat.mul_le_mul hl hs).trans_eq (pow_add 2 H (gcdMassExponent p.natDegree H)).symm)

theorem exceptional_mass_le (p : Polynomial Coefficient) (D H : ℕ)
    (hD : p.natDegree ≤ D) (hH : ∀ k, coefficientMass (p.coeff k) ≤ 2 ^ H) :
    coefficientMass (exceptional p) ≤ 2 ^ exceptionalMassBound D H :=
  (exceptional_mass p H hH).trans
    (Nat.pow_le_pow_right (by decide) (exceptionalMassBound_mono hD le_rfl))

theorem exceptionalMassBound_linear (D H : ℕ) :
    exceptionalMassBound D H = (2 * D + 1) * H +
      (2 * D).size * (2 * D) + (2 * D) * D.size := by
  unfold exceptionalMassBound gcdMassExponent
  ring

theorem exceptionalMassBound_binary {D H : List Bool → ℕ} (hD : BinaryFn D) (hH : BinaryFn H) :
    BinaryFn (fun q => exceptionalMassBound (D q) (H q)) := by
  have h2 := (BinaryFn.const 2).mul hD
  exact hH.add ((h2.size.mul h2).add (h2.mul (hH.add hD.size)))

end LeanCanny.Algebra.SymbolicScaledSquarefree
