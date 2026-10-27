/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceUnit
import Mathlib.Tactic.FinCases

/-! # Products for simultaneous sign tests in algebraic slices

Original modular readers supply products and powers zero, one, and two.
Their degree and mass controls are derived here, rather than supplied with
the product-query answers.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical

noncomputable def product (F G : Family) : Family where
  polynomial c := F.polynomial c * G.polynomial c
  degree c := F.degree c + G.degree c
  parameterDegree c := F.parameterDegree c + G.parameterDegree c
  mass c := (F.mass c + (F.degree c + 1).size) + (G.mass c + (G.degree c + 1).size)
  polynomial_degree c := Polynomial.natDegree_mul_le.trans (Nat.add_le_add (F.polynomial_degree c) (G.polynomial_degree c))
  coefficient_degree c i := PseudoRemainder.mul_parameter_degree (F.polynomial c) (G.polynomial c)
    (F.parameterDegree c) (G.parameterDegree c) (F.coefficient_degree c) (G.coefficient_degree c) i
  coefficient_mass c i := by
    have hf := NestedMass.le_pow (F.polynomial c) (F.degree c) (F.mass c) (F.polynomial_degree c) (F.coefficient_mass c)
    have hg := NestedMass.le_pow (G.polynomial c) (G.degree c) (G.mass c) (G.polynomial_degree c) (G.coefficient_mass c)
    exact (NestedMass.coeff_le _ _).trans ((NestedMass.mul_le _ _).trans
      ((Nat.mul_le_mul hf hg).trans_eq (pow_add _ _ _).symm))

noncomputable def productAccess {F G : Family} (A : F.Access) (B : G.Access) : (product F G).Access where
  reader := CertifiedPolynomial.BivariateProduct.reader A.reader B.reader
  degree_binary := A.degree_binary.add B.degree_binary
  parameterDegree_binary := A.parameterDegree_binary.add B.parameterDegree_binary
  mass_binary := (A.mass_binary.add ((A.degree_binary.add (BinaryFn.const 1)).size)).add
    (B.mass_binary.add ((B.degree_binary.add (BinaryFn.const 1)).size))

theorem product_slice (F G : Family) (c : List Bool) (t : ℝ) :
    (product F G).slice c t = F.slice c t * G.slice c t := by
  simp only [Family.slice, product, Polynomial.map_mul]

noncomputable def smallPower (F : Family) (e : Fin 3) : Family :=
  match e.val with
  | 0 => unit
  | 1 => F
  | _ => square F

noncomputable def smallPowerAccess {F : Family} (A : F.Access) (e : Fin 3) : (smallPower F e).Access := by
  rcases e with ⟨e, he⟩
  cases e with
  | zero => exact unitAccess
  | succ e =>
    cases e with
    | zero => exact A
    | succ e => exact squareAccess A

theorem smallPower_slice (F : Family) (e : Fin 3) (c : List Bool) (t : ℝ) :
    (smallPower F e).slice c t = F.slice c t ^ e.val := by
  fin_cases e
  · change (ofTest unitTest).slice c t = F.slice c t ^ 0
    rw [ofTest_slice]
    simp only [unitTest, Polynomial.map_one, pow_zero]
  · simp only [smallPower, pow_one]
  · simp only [smallPower, Family.slice, square, Polynomial.map_pow]

end LeanCanny.Encoding.BoundedAlgebraicSlice
