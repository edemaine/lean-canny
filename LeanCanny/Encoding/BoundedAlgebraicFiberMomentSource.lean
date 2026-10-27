/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberThom
public import LeanCanny.Encoding.BoundedAlgebraicSliceProductQuery
public import LeanCanny.Encoding.TernaryFP

/-! # Original derivative sources for sparse fiber moments

A polynomially bounded feature list supplies binary derivative orders.
Ternary exponents select powers zero, one, and two. The complete product's
coefficient program is constructed from the original bivariate reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberMomentSource
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open BoundedAlgebraicSlice

def source (w : List Bool) : List Bool := pairFst (pairFst w)
def orderQuery (w : List Bool) : List Bool := pair (source w) (BinaryNat.normalize (pairSnd w))
theorem source_FP : source ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem orderQuery_FP : orderQuery ∈ FP := mem_FP_pair source_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)

noncomputable def family (F : Family) (features : List Bool → ℕ) (orders : List Bool → List Bool) :
    BivariateQueryProductBits.Family where
  polynomial q i := (Polynomial.derivative^[Nat.fromBitsLE (orders (pair (pairFst q) (BinaryNatCode.encode i)))])
    (F.polynomial (pairFst q))
  exponent q i := Ternary.exponent (features (pairFst q)) (Nat.fromBitsLE (pairSnd q)) i
  count q := features (pairFst q)
  degree q := F.degree (pairFst q)
  parameterDegree q := F.parameterDegree (pairFst q)
  mass q := IteratedDerivativeBits.massBudget (F.degree (pairFst q)) (F.mass (pairFst q))
  polynomial_degree q i := (Polynomial.natDegree_iterate_derivative (F.polynomial (pairFst q))
    (Nat.fromBitsLE (orders (pair (pairFst q) (BinaryNatCode.encode i))))).trans
    ((Nat.sub_le _ _).trans (F.polynomial_degree (pairFst q)))
  coefficient_degree q i j := CertifiedPolynomial.BivariateIteratedDerivative.parameter_degree
    (F.polynomial (pairFst q)) (F.parameterDegree (pairFst q)) (F.coefficient_degree (pairFst q))
    (Nat.fromBitsLE (orders (pair (pairFst q) (BinaryNatCode.encode i)))) j
  coefficient_mass q i j := CertifiedPolynomial.BivariateIteratedDerivative.coefficient_mass_budget
    (F.polynomial (pairFst q)) (F.degree (pairFst q)) (F.mass (pairFst q))
    (F.polynomial_degree (pairFst q)) (F.coefficient_mass (pairFst q))
    (Nat.fromBitsLE (orders (pair (pairFst q) (BinaryNatCode.encode i)))) j

noncomputable def exponentWord (features : List Bool → ℕ) (z : List Bool) : List Bool :=
  Ternary.digit (BinaryNatCode.encode (features (source z))) (pairSnd (pairFst z)) (pairSnd z)

theorem exponentWord_FP {features : List Bool → ℕ} (hc : UnaryFn features) : exponentWord features ∈ FP := by
  have hu : UnaryFn (fun z => features (source z)) := hc.comp source_FP
  apply Ternary.digit_mem_FP (bits_mem_FP hu) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
  exact hu.of_eq (fun z => (Nat.fromBitsLE_bits _).symm)

noncomputable def access {F : Family} (A : F.Access) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (hc : UnaryFn features) (ho : orders ∈ FP) : BivariateQueryProductBits.Access (family F features orders) := by
  let R := iterateDerivativeAccess (A.comp source source_FP) (orders ∘ orderQuery) (mem_FP_comp orderQuery_FP ho)
  exact {
    reader := {
      coefficient := R.reader.coefficient
      evaluator := R.reader.evaluator
      coefficient_eq q u v := by
        have H := R.reader.coefficient_eq q u v
        simpa only [iterateDerivative, Family.comp, family, Function.comp_apply, source, orderQuery,
          BinaryNat.normalize_eq_bits, BinaryNatCode.encode] using H }
    exponent := exponentWord features
    exponent_eq q i := by
      simp only [exponentWord, source, pairFst_pair, pairSnd_pair, Ternary.digit_exponent,
        BinaryNatCode.encode, Nat.fromBitsLE_bits, family]
    exponent_FP := exponentWord_FP hc
    count_binary := BinaryFn.ofUnary (hc.comp pairFst_mem_FP)
    degree_binary := A.degree_binary.comp pairFst_mem_FP
    parameterDegree_binary := A.parameterDegree_binary.comp pairFst_mem_FP
    mass_binary := (IteratedDerivativeBits.massBudget_binary A.degree_binary A.mass_binary).comp pairFst_mem_FP }

theorem polynomial_slice (F : Family) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (q : List Bool) (i : ℕ) (t : ℝ) :
    ((family F features orders).polynomial q i).map (ParameterTarski.evalHom t) =
      (Polynomial.derivative^[Nat.fromBitsLE (orders (pair (pairFst q) (BinaryNatCode.encode i)))])
        (F.slice (pairFst q) t) :=
  (Polynomial.iterate_derivative_map _ _ _).symm

theorem product_slice (F : Family) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (q : List Bool) (t : ℝ) :
    (ofIndexedProduct (family F features orders)).slice q t = RootSignQueries.queryPolynomial
      (fun i : Fin (features (pairFst q)) =>
        (Polynomial.derivative^[Nat.fromBitsLE (orders (pair (pairFst q) (BinaryNatCode.encode i.val)))])
          (F.slice (pairFst q) t))
      (fun i => Ternary.exponent (features (pairFst q)) (Nat.fromBitsLE (pairSnd q)) i.val) := by
  simp only [ofIndexedProduct_slice, polynomial_slice]
  rfl

end LeanCanny.Encoding.BoundedAlgebraicFiberMomentSource
