/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SeparableIntegerPolynomialField
public import LeanCanny.Algebra.UnivariateRationalComposition

/-! # The explicit primitive-pair coordinates as composable polynomial ratios -/

@[expose] public section

namespace LeanCanny.Algebra.SeparableIntegerPolynomial
open Polynomial
open UnivariateRational

noncomputable def leftCoordinate (p q : SeparableIntegerPolynomial) : Coordinate :=
  ⟨PrimitivePair.leftNumerator p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial),
   PrimitivePair.denominator p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial)⟩

noncomputable def rightCoordinate (p q : SeparableIntegerPolynomial) : Coordinate :=
  ⟨PrimitivePair.rightNumerator p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial),
   PrimitivePair.denominator p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial)⟩

theorem leftCoordinate_degree (p q : SeparableIntegerPolynomial) :
    (leftCoordinate p q).degree ≤ p.polynomial.natDegree * q.polynomial.natDegree + 2 := by
  have hp : (q.polynomial.natDegree - 1) * p.polynomial.natDegree ≤ p.polynomial.natDegree * q.polynomial.natDegree :=
    (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans_eq (Nat.mul_comm _ _)
  have hn := PrimitivePair.leftNumerator_degree p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial)
  have hd := PrimitivePair.denominator_degree p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial)
  exact max_le (hn.trans (by omega)) (hd.trans (by omega))

theorem rightCoordinate_degree (p q : SeparableIntegerPolynomial) :
    (rightCoordinate p q).degree ≤ p.polynomial.natDegree * q.polynomial.natDegree + 2 := by
  have hp : (q.polynomial.natDegree - 1) * p.polynomial.natDegree ≤ p.polynomial.natDegree * q.polynomial.natDegree :=
    (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans_eq (Nat.mul_comm _ _)
  have hn := PrimitivePair.rightNumerator_degree p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial)
  have hd := PrimitivePair.denominator_degree p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial)
  exact max_le (hn.trans (by omega)) (hd.trans (by omega))

theorem leftCoordinate_eval {K : Type*} [Field K] (p q : SeparableIntegerPolynomial) (x : K) :
    (leftCoordinate p q).eval x = (decode p q x).1 := rfl

theorem rightCoordinate_eval {K : Type*} [Field K] (p q : SeparableIntegerPolynomial) (x : K) :
    (rightCoordinate p q).eval x = (decode p q x).2 := rfl

end LeanCanny.Algebra.SeparableIntegerPolynomial
