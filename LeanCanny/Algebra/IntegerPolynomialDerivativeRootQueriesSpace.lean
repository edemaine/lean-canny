/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace
public import LeanCanny.Algebra.DerivativeProductBounds
public import LeanCanny.Algebra.ModularNatMulFP

/-! # Native derivative root queries from original integer coefficients

A single source query and modular multiplication compute each derivative
coefficient. Binary degree and mass budgets then supply distinct-root counts
and rational cell queries, including zero and constant source polynomials.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialDerivativeBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def query (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (BinaryNat.succ (pairSnd (pairFst q)))) (pairSnd q)
theorem query_FP : query ∈ FP := by polytime [query]

def finish (z : List Bool) : List Bool := BinaryNat.mulMod
  (pair (BinaryNat.succ (pairSnd (pairFst z)))
    (pair (pairSnd z) (BinaryNat.succ (pairSnd (pairFst (pairFst z))))))
theorem finish_FP : finish ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP
  have hk := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) BinaryNat.succ_mem_FP
  exact mem_FP_of_eq (mem_FP_comp (mem_FP_pair hm (mem_FP_pair pairSnd_mem_FP hk)) BinaryNat.mulMod_mem_FP)
    (fun z => by simp only [finish, Function.comp_apply])

theorem evaluator (p : List Bool → ℤ[X]) (P : SpaceFunction (PrimitivePairBits.coefficient p)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => (p c).derivative)) := by
  have E := (P.precompose query query_FP).withInput.postcompose finish finish_FP
  refine E.congr (funext fun q => ?_)
  simp only [Function.comp_apply, finish, query, PrimitivePairBits.coefficient,
    RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
    RationalSubstitution.IntegerBits.mValue,
    pairFst_pair, pairSnd_pair, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
  let m := Nat.fromBitsLE (pairSnd q) + 1
  let k := Nat.fromBitsLE (pairSnd (pairFst q))
  let a := (p (pairFst (pairFst q))).coeff (k + 1)
  have hd : (p (pairFst (pairFst q))).derivative.coeff k = a * ((k + 1 : ℕ) : ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Polynomial.coeff_derivative (p (pairFst (pairFst q))) k
  change BinaryNat.mulMod (pair (BinaryNatCode.encode m)
    (pair (residueBits (a : ZMod m)) (BinaryNatCode.encode (k + 1)))) =
      residueBits (((p (pairFst (pairFst q))).derivative.coeff k) : ZMod m)
  rw [hd, ArithmeticBits.mulMod_nat_residueBits, Int.cast_mul, Int.cast_natCast]

noncomputable def source (S : IntegerPolynomialRootQueriesBits.Source) : IntegerPolynomialRootQueriesBits.Source where
  polynomial c := (S.polynomial c).derivative
  degree := S.degree
  mass c := (S.degree c).size + S.mass c
  degree_bound c := (Polynomial.natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans (S.degree_bound c))
  mass_bound c := by
    apply (coefficientMass_derivative_le _).trans
    calc
      _ ≤ S.degree c * 2 ^ S.mass c := Nat.mul_le_mul (S.degree_bound c) (S.mass_bound c)
      _ ≤ 2 ^ (S.degree c).size * 2 ^ S.mass c := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
      _ = _ := (pow_add _ _ _).symm

theorem access {S : IntegerPolynomialRootQueriesBits.Source} (A : IntegerPolynomialRootQueriesBits.Access S) :
    IntegerPolynomialRootQueriesBits.Access (source S) :=
  ⟨evaluator S.polynomial A.coefficient, A.degree, A.degree.size.add A.mass⟩

theorem countEvaluator {S : IntegerPolynomialRootQueriesBits.Source} (A : IntegerPolynomialRootQueriesBits.Access S) :
    SpaceFunction (fun c => BinaryNatCode.encode (IntegerPolynomialRootQueriesBits.rootSet (source S) c).card) :=
  IntegerPolynomialRootQueriesBits.countEvaluator (access A)

end LeanCanny.Algebra.IntegerPolynomialDerivativeBits
