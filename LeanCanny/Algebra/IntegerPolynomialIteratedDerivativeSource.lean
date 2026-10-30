/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedIntegerDerivativeSpace
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace

/-! # Native bounded sources for all binary-indexed integer derivatives -/

@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialIteratedDerivativeBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation
open IntegerPolynomialRootQueriesBits (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def source (S : Source) : Source where
  polynomial z := IndexedIntegerDerivativeBits.polynomial (S.polynomial ∘ pairFst) pairSnd z
  degree z := S.degree (pairFst z)
  mass z := IteratedDerivativeBits.massBudget (S.degree (pairFst z)) (S.mass (pairFst z))
  degree_bound _ := (Polynomial.natDegree_iterate_derivative _ _).trans ((Nat.sub_le _ _).trans (S.degree_bound _))
  mass_bound _ := IteratedDerivativeBits.mass_bound _ _ _ (S.degree_bound _)
    (fun k => (coeff_natAbs_le_coefficientMass _ k).trans (S.mass_bound _)) _

theorem access {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) :
    IntegerPolynomialRootQueriesBits.Access (source S) :=
  ⟨IndexedIntegerDerivativeBits.evaluator _ (PolynomialFamilyProductBits.reindexEvaluator A.coefficient pairFst pairFst_mem_FP)
      pairSnd_mem_FP,
    A.degree.comp pairFst_mem_FP,
    IteratedDerivativeBits.massBudget_binary (A.degree.comp pairFst_mem_FP) (A.mass.comp pairFst_mem_FP)⟩

theorem packet (S : Source) (c : List Bool) (k : ℕ) :
    (source S).polynomial (pair c (BinaryNatCode.encode k)) = Polynomial.derivative^[k] (S.polynomial c) := by
  simp only [source, IndexedIntegerDerivativeBits.polynomial, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def comp (S : Source) (f : List Bool → List Bool) : Source where
  polynomial := S.polynomial ∘ f
  degree := S.degree ∘ f
  mass := S.mass ∘ f
  degree_bound c := S.degree_bound (f c)
  mass_bound c := S.mass_bound (f c)

theorem compAccess {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    {f : List Bool → List Bool} (hf : f ∈ FP) : IntegerPolynomialRootQueriesBits.Access (comp S f) :=
  ⟨PolynomialFamilyProductBits.reindexEvaluator A.coefficient f hf, A.degree.comp hf, A.mass.comp hf⟩

end LeanCanny.Algebra.IntegerPolynomialIteratedDerivativeBits
