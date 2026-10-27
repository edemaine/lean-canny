/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceJointCount
public import LeanCanny.Algebra.BivariateIteratedDerivativeBounds

/-! # Native derivative families in algebraic slices

Derivative orders are binary and may depend on the source context. The
original bivariate reader and its degree and mass controls supply the full
family, including orders beyond the actual specialized degree.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice
open LeanCanny.Algebra LeanCanny.Computation Polynomial

noncomputable def iterateDerivative (F : Family) (k : List Bool → List Bool) : Family where
  polynomial c := (Polynomial.derivative^[Nat.fromBitsLE (k c)]) (F.polynomial c)
  degree := F.degree
  parameterDegree := F.parameterDegree
  mass c := IteratedDerivativeBits.massBudget (F.degree c) (F.mass c)
  polynomial_degree c := (Polynomial.natDegree_iterate_derivative _ _).trans ((Nat.sub_le _ _).trans (F.polynomial_degree c))
  coefficient_degree c i := CertifiedPolynomial.BivariateIteratedDerivative.parameter_degree
    (F.polynomial c) (F.parameterDegree c) (F.coefficient_degree c) _ i
  coefficient_mass c i := CertifiedPolynomial.BivariateIteratedDerivative.coefficient_mass_budget
    (F.polynomial c) (F.degree c) (F.mass c) (F.polynomial_degree c) (F.coefficient_mass c) _ i

noncomputable def iterateDerivativeAccess {F : Family} (A : F.Access) (k : List Bool → List Bool) (hk : k ∈ FP) :
    (iterateDerivative F k).Access where
  reader := CertifiedPolynomial.BivariateIteratedDerivative.reader A.reader k hk
  degree_binary := A.degree_binary
  parameterDegree_binary := A.parameterDegree_binary
  mass_binary := IteratedDerivativeBits.massBudget_binary A.degree_binary A.mass_binary

theorem iterateDerivative_slice (F : Family) (k : List Bool → List Bool) (c : List Bool) (t : ℝ) :
    (iterateDerivative F k).slice c t = (Polynomial.derivative^[Nat.fromBitsLE (k c)]) (F.slice c t) := by
  exact (Polynomial.iterate_derivative_map _ _ _).symm

theorem iterateDerivative_specialized (P : BoundedFullWriter.Readers) (F : Family)
    (k : List Bool → List Bool) (u : List Bool) :
    specialized P (iterateDerivative F k) u = (Polynomial.derivative^[Nat.fromBitsLE (k (pairFst u))]) (specialized P F u) := by
  by_cases hu : u ∈ valid P
  · simp only [specialized, ite_eq_left hu, iterateDerivative_slice]
  · simp only [specialized, ite_eq_right hu, Polynomial.iterate_derivative_zero]

theorem iterateDerivative_above_degree (P : BoundedFullWriter.Readers) (F : Family)
    (k : List Bool → List Bool) (u : List Bool) (hk : F.degree (pairFst u) < Nat.fromBitsLE (k (pairFst u))) :
    specialized P (iterateDerivative F k) u = 0 := by
  rw [iterateDerivative_specialized]
  exact Polynomial.iterate_derivative_eq_zero ((specialized_degree P F u).trans_lt hk)

end LeanCanny.Encoding.BoundedAlgebraicSlice
