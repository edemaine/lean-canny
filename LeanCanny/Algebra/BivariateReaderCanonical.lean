/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CertifiedPolynomial
public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace

/-! # Canonical raw coefficient access from certified bivariate readers

Normalizing just the two coefficient indices makes a reader certified on
canonical packets suitable for arbitrary raw coefficient queries. Context and
modulus words are preserved, and the original reader's workspace is charged.
-/

@[expose] public section
namespace LeanCanny.Algebra.BivariateReaderCanonical
open LeanCanny.Encoding LeanCanny.Computation

def query (q : List Bool) : List Bool := pair (pairFst q)
  (pair (BinaryNat.normalize (pairFst (pairSnd q))) (BinaryNat.normalize (pairSnd (pairSnd q))))

theorem query_FP : query ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair
    (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) BinaryNat.normalize_mem_FP)
    (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP))

theorem evaluator {p : List Bool → Polynomial (Polynomial ℤ)} (A : CertifiedPolynomial.BivariateReader p) :
    SpaceFunction (SymbolicFixedTableEntryBits.coefficient p) := by
  refine (A.evaluator.precompose query query_FP).congr (funext fun q => ?_)
  change A.coefficient (query q) = _
  rw [query, BinaryNat.normalize_eq_bits, BinaryNat.normalize_eq_bits]
  change A.coefficient (pair (pairFst q) (pair
    (BinaryNatCode.encode (Nat.fromBitsLE (pairFst (pairSnd q))))
    (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd (pairSnd q)))))) = _
  rw [A.coefficient_eq]
  rfl

end LeanCanny.Algebra.BivariateReaderCanonical
