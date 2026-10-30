/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionTestMoments
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace

/-! # Canonical scalar sources from native polynomial-test readers

Normalize only coefficient indices and modulus predecessors. Original source
contexts remain unchanged, and the supplied coefficient machine is charged.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialTestSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open scoped Classical
set_option maxHeartbeats 300000

noncomputable def source (T : BoundedProjectionTestMoments.Test) : IntegerPolynomialRootQueriesBits.Source :=
  ⟨T.polynomial, T.degree, T.mass, T.polynomial_degree, T.polynomial_mass⟩

def query (q : List Bool) : List Bool := pair
  (pair (pairFst (pairFst q)) (BinaryNat.normalize (pairSnd (pairFst q)))) (BinaryNat.normalize (pairSnd q))
theorem query_FP : query ∈ FP := by polytime [query]

theorem access {T : BoundedProjectionTestMoments.Test} (A : T.Access) : IntegerPolynomialRootQueriesBits.Access (source T) := by
  refine ⟨(A.evaluator.precompose query query_FP).congr (funext fun q => ?_), A.degree_binary, A.mass_binary⟩
  have hq : query q = pair
      (pair (pairFst (pairFst q)) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd (pairFst q)))))
      (BinaryNatCode.encode ((Nat.fromBitsLE (pairSnd q) + 1) - 1)) := by
    simp only [query, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.add_sub_cancel]
  change A.coefficient (query q) = _
  rw [hq, A.coefficient_eq _ _ _ (by omega)]
  rfl

noncomputable def test (S : IntegerPolynomialRootQueriesBits.Source) : BoundedProjectionTestMoments.Test :=
  ⟨S.polynomial, S.degree, S.mass, S.degree_bound, S.mass_bound⟩

noncomputable def testAccess {S : IntegerPolynomialRootQueriesBits.Source}
    (A : IntegerPolynomialRootQueriesBits.Access S) : (test S).Access where
  degree_binary := A.degree
  mass_binary := A.mass
  coefficient := PrimitivePairBits.coefficient S.polynomial
  evaluator := A.coefficient
  coefficient_eq := IntegerPolynomialRootQueriesBits.coefficient_packet S.polynomial

end LeanCanny.Encoding.IntegerPolynomialTestSource
