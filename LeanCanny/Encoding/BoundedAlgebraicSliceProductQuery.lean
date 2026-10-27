/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceTarskiPSPACE
public import LeanCanny.Algebra.BivariateQueryProductSpace

/-! # Algebraic-slice tests built from indexed polynomial products

The indexed original readers provide a product family with constructed
degree, parameter-degree, and mass controls. The complete algebraic-slice
Tarski evaluator can therefore use it without a product-coefficient oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice
open LeanCanny.Algebra LeanCanny.Computation Polynomial

noncomputable def ofIndexedProduct (Q : BivariateQueryProductBits.Family) : Family where
  polynomial := Q.product
  degree c := 2 * Q.count c * Q.degree c
  parameterDegree c := 2 * Q.count c * Q.parameterDegree c
  mass c := 2 * Q.count c * (Q.mass c + (Q.degree c + 1).size)
  polynomial_degree := Q.product_degree
  coefficient_degree := Q.product_parameter_degree
  coefficient_mass c i := (NestedMass.coeff_le (Q.product c) i).trans (Q.product_mass c)

noncomputable def ofIndexedProductAccess {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) :
    (ofIndexedProduct Q).Access where
  reader := BivariateQueryProductBits.reader A
  degree_binary := ((BinaryFn.const 2).mul A.count_binary).mul A.degree_binary
  parameterDegree_binary := ((BinaryFn.const 2).mul A.count_binary).mul A.parameterDegree_binary
  mass_binary := ((BinaryFn.const 2).mul A.count_binary).mul
    (A.mass_binary.add ((A.degree_binary.add (BinaryFn.const 1)).size))

theorem ofIndexedProduct_slice (Q : BivariateQueryProductBits.Family) (c : List Bool) (t : ℝ) :
    (ofIndexedProduct Q).slice c t = RootSignQueries.queryPolynomial
      (fun i : Fin (Q.count c) => (Q.polynomial c i.val).map (ParameterTarski.evalHom t))
      (fun i => Q.exponent c i.val) := by
  simp only [Family.slice, ofIndexedProduct, BivariateQueryProductBits.Family.product]
  exact RootSignQueries.map_queryPolynomial (ParameterTarski.evalHom t)
    (fun i : Fin (Q.count c) => Q.polynomial c i.val) (fun i => Q.exponent c i.val)

end LeanCanny.Encoding.BoundedAlgebraicSlice
