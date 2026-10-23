/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectionParameterAlgebraic
public import LeanCanny.Algebra.GenericProjectionFinite

/-! # Extended projection coordinates with fixed symbolic parameters

Coordinate derivations that fix the hypersurface polynomial make every
extended projection coordinate algebraic, including the reciprocal of the
base partial derivative. The polynomial itself may have symbolic coefficients
outside the derivations' base field.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionParameterCoordinates
open MvPolynomial

variable {K B L ι : Type*} [Field K] [Field B] [Field L] [CharZero B]
  [Algebra K B] [Algebra K L] [Algebra B L] [IsScalarTower K B L] [Fintype ι] [DecidableEq ι]

theorem algebraic_extended_coordinates (p : MvPolynomial ι B) (base : ι) (v : ι → B)
    (z : Option ι → L) (hbase : v base = 1)
    (D : {i : ι // i ≠ base} → Derivation K B B)
    (hfixed : ∀ j, MvCoefficientDerivation.derivation (D j) p = 0)
    (hcoord : ∀ j i, D j (v i) = if i = j.val then 1 else 0)
    (hz : ∀ j, aeval z (GenericProjectionFinite.equation p base v j) = 0) :
    ∀ j, IsAlgebraic B (z j) := by
  let x : ι → L := fun i => z (some i)
  obtain ⟨hp, hinv, hpartial⟩ := (GenericProjectionFinite.equations_iff p base v z).mp hz
  have hw (i : ι) : algebraMap B L (v i) = z none * aeval x (pderiv i p) := by
    calc
      _ = algebraMap B L (v i) * (z none * aeval x (pderiv base p)) := by rw [hinv, mul_one]
      _ = z none * aeval x (pderiv i p) := by rw [hpartial i]; ring
  have hc := ProjectionParameterAlgebraic.algebraic_normalized_coordinates (fun _ : Unit => p) x v
    (fun _ => z none) (fun _ => hp) (fun i => by simpa using hw i) base hbase D (fun j _ => hfixed j) hcoord
  intro j
  cases j with
  | some i => exact hc i
  | none =>
    rw [eq_inv_of_mul_eq_one_left hinv]
    exact (GenericProjectionFinite.algebraic_polynomial_value (K := B) (pderiv base p) x hc).inv

end LeanCanny.Algebra.ProjectionParameterCoordinates
