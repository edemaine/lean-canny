/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberRecords

/-! # Native bivariate products selected by sparse fiber records

Unit padding uses exponent zero. Other slots select one derivative sign.
Every source coefficient, slot, derivative order, and product coefficient
has a native certificate constructed from the original reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberRecordSource
open LeanCanny.Algebra LeanCanny.Computation Polynomial BoundedAlgebraicSlice
open BoundedAlgebraicFiberRecords

def orderQuery (w : List Bool) : List Bool := pair (pairFst w) (BinaryNat.normalize (pairSnd w))
theorem orderQuery_FP : orderQuery ∈ FP := mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)
theorem orderQuery_value (F : Family) (w : List Bool) :
    Nat.fromBitsLE (orderRead F (orderQuery w)) = order F (pairFst w) (Nat.fromBitsLE (pairSnd w)) := by
  have hq : orderQuery w = pair (pairFst w) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd w))) := by
    simp only [orderQuery, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]
  rw [hq, orderRead_packet]
  exact Nat.fromBitsLE_bits _

noncomputable def family (F : Family) : BivariateQueryProductBits.Family where
  polynomial q i := (Polynomial.derivative^[order F q i]) (F.polynomial (pairFst q))
  exponent := exponent F
  count := recordSlots F
  degree q := F.degree (pairFst q)
  parameterDegree q := F.parameterDegree (pairFst q)
  mass q := IteratedDerivativeBits.massBudget (F.degree (pairFst q)) (F.mass (pairFst q))
  polynomial_degree q i := (Polynomial.natDegree_iterate_derivative (F.polynomial (pairFst q)) (order F q i)).trans
    ((Nat.sub_le _ _).trans (F.polynomial_degree (pairFst q)))
  coefficient_degree q i j := CertifiedPolynomial.BivariateIteratedDerivative.parameter_degree
    (F.polynomial (pairFst q)) (F.parameterDegree (pairFst q)) (F.coefficient_degree (pairFst q)) (order F q i) j
  coefficient_mass q i j := CertifiedPolynomial.BivariateIteratedDerivative.coefficient_mass_budget
    (F.polynomial (pairFst q)) (F.degree (pairFst q)) (F.mass (pairFst q))
    (F.polynomial_degree (pairFst q)) (F.coefficient_mass (pairFst q)) (order F q i) j

noncomputable def access {F : Family} (A : F.Access) : BivariateQueryProductBits.Access (family F) := by
  let R := iterateDerivativeAccess (A.comp BoundedAlgebraicFiberMomentSource.source BoundedAlgebraicFiberMomentSource.source_FP)
    (orderRead F ∘ orderQuery) (mem_FP_comp orderQuery_FP (orderRead_FP A))
  exact {
    reader := {
      coefficient := R.reader.coefficient
      evaluator := R.reader.evaluator
      coefficient_eq q u v := by
        have H := R.reader.coefficient_eq q u v
        simpa only [iterateDerivative, Family.comp, family, Function.comp_apply,
          BoundedAlgebraicFiberMomentSource.source, orderQuery_value] using H }
    exponent := exponentRead F
    exponent_eq := exponentRead_packet F
    exponent_FP := exponentRead_FP A
    count_binary := BinaryFn.ofUnary (recordSlots_unary A)
    degree_binary := A.degree_binary.comp pairFst_mem_FP
    parameterDegree_binary := A.parameterDegree_binary.comp pairFst_mem_FP
    mass_binary := (IteratedDerivativeBits.massBudget_binary A.degree_binary A.mass_binary).comp pairFst_mem_FP }

theorem product_slice (F : Family) (q : List Bool) (t : ℝ) :
    (ofIndexedProduct (family F)).slice q t = RootSignQueries.queryPolynomial
      (fun i : Fin (recordSlots F q) => (Polynomial.derivative^[order F q i.val]) (F.slice (pairFst q) t))
      (fun i => exponent F q i.val) := by
  rw [ofIndexedProduct_slice]
  simp only [family, ← Polynomial.iterate_derivative_map, Family.slice]
  rfl

end LeanCanny.Encoding.BoundedAlgebraicFiberRecordSource
