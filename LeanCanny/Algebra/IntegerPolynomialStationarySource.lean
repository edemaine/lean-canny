/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerPolynomialDerivativeRootQueriesSpace
public import LeanCanny.Algebra.PolynomialBinaryProductSpace

/-! # Native scalar sources retaining both roots and stationary values

The polynomial `p * p.derivative` retains every root of `p`, as well as the
derivative roots used to sample bounded gaps. Its degree and coefficient-mass
allowances remain binary, and both coefficient computations are charged.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialStationaryBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation
open IntegerPolynomialRootQueriesBits (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def source (S : Source) : Source where
  polynomial c := S.polynomial c * (S.polynomial c).derivative
  degree c := S.degree c + S.degree c
  mass c := S.mass c + ((S.degree c).size + S.mass c)
  degree_bound c := Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add (S.degree_bound c) ((IntegerPolynomialDerivativeBits.source S).degree_bound c))
  mass_bound c := (coefficientMass_mul_le _ _).trans
    ((Nat.mul_le_mul (S.mass_bound c) ((IntegerPolynomialDerivativeBits.source S).mass_bound c)).trans_eq (pow_add _ _ _).symm)

theorem evaluator (p : List Bool → ℤ[X]) (P : SpaceFunction (PrimitivePairBits.coefficient p)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => p c * (p c).derivative)) :=
  PolynomialBinaryProductBits.evaluator _ _ P (IntegerPolynomialDerivativeBits.evaluator p P)

theorem access {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) :
    IntegerPolynomialRootQueriesBits.Access (source S) :=
  ⟨evaluator S.polynomial A.coefficient, A.degree.add A.degree, A.mass.add (A.degree.size.add A.mass)⟩

theorem ne_zero (S : Source) (c : List Bool) (hp : S.polynomial c ≠ 0) (hD : 0 < (S.polynomial c).natDegree) :
    (source S).polynomial c ≠ 0 := mul_ne_zero hp (Polynomial.derivative_ne_zero.mpr hD.ne')

theorem retains_root {K : Type*} [CommRing K] (S : Source) (c : List Bool) (phi : ℤ →+* K) (a : K)
    (ha : (S.polynomial c).eval₂ phi a = 0) : ((source S).polynomial c).eval₂ phi a = 0 := by
  simp only [source, Polynomial.eval₂_mul, ha, zero_mul]

theorem retains_stationary {K : Type*} [CommRing K] (S : Source) (c : List Bool) (phi : ℤ →+* K) (a : K)
    (ha : (S.polynomial c).derivative.eval₂ phi a = 0) : ((source S).polynomial c).eval₂ phi a = 0 := by
  simp only [source, Polynomial.eval₂_mul, ha, mul_zero]

end LeanCanny.Algebra.IntegerPolynomialStationaryBits
