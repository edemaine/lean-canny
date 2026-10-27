/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BivariateDerivativeSpace
public import LeanCanny.Algebra.BivariateProductSpace
public import LeanCanny.Algebra.PolynomialPseudoRemainderReader
public import LeanCanny.Algebra.PolynomialPseudoRemainderBounds

/-! # Native bivariate Tarski seeds from original head and query readers

The derivative product and fixed even pseudo-reduction are computed
internally. The supplied reduction degree need not be the symbolic degree;
only its positivity, reduction bound, and input-product bound are required.
-/

@[expose] public section
namespace LeanCanny.Algebra.BivariateTarskiSeedBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower

structure Family where
  head : List Bool → (ℤ[X])[X]
  query : List Bool → (ℤ[X])[X]
  degree : List Bool → ℕ
  bound : List Bool → ℕ
  degree_pos : ∀ c, 0 < degree c
  degree_le : ∀ c, degree c ≤ bound c
  input_degree : ∀ c, (query c * (head c).derivative).natDegree ≤ bound c

structure Access (F : Family) where
  head : CertifiedPolynomial.BivariateReader F.head
  query : CertifiedPolynomial.BivariateReader F.query
  degree : BinaryFn F.degree
  bound : BinaryFn F.bound

noncomputable def Family.reduction (F : Family) : PolynomialPseudoRemainderBits.Family where
  head := F.head
  input c := F.query c * (F.head c).derivative
  degree := F.degree
  bound := F.bound
  degree_pos := F.degree_pos
  degree_le := F.degree_le
  input_degree := F.input_degree

noncomputable def Family.seed (F : Family) (c : List Bool) : (ℤ[X])[X] :=
  PseudoRemainder.seed (F.head c) (F.query c) (F.degree c) (F.bound c)

noncomputable def reductionAccess {F : Family} (A : Access F) : PolynomialPseudoRemainderBits.Access F.reduction where
  head := A.head
  input := CertifiedPolynomial.BivariateProduct.reader A.query (CertifiedPolynomial.BivariateDerivative.reader A.head)
  degree := A.degree
  bound := A.bound

noncomputable def reader {F : Family} (A : Access F) : CertifiedPolynomial.BivariateReader F.seed :=
  PolynomialPseudoRemainderBits.reader (reductionAccess A)

theorem coefficient_evaluator {F : Family} (A : Access F) : SpaceFunction (reader A).coefficient :=
  (reader A).evaluator

theorem coefficient_packet {F : Family} (A : Access F) (q : List Bool) (u v : ℕ) :
    (reader A).coefficient (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      residueBits ((((F.seed (pairFst q)).coeff v).coeff u : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) :=
  (reader A).coefficient_eq q u v

end LeanCanny.Algebra.BivariateTarskiSeedBits
