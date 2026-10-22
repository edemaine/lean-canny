/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicScaledSquarefreeSmall
public import LeanCanny.Algebra.PrimitivePairSeparation
public import LeanCanny.Algebra.CoordinateRecoveryMap

/-! # Constructed symbolic primitive pairs

All polynomials and recovery formulas remain in ℤ[alpha][X]. A bounded scan
for the first nonzero symbolic derivative resultant chooses the separating
integer. Arbitrary nonzero inputs enter through the proved symbolic squarefree
construction, rather than a supplied separability certificate.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicPrimitivePair
open Polynomial SymbolicScaledSquarefree
open scoped Classical
attribute [local irreducible] Matrix.det

structure SeparablePolynomial where
  polynomial : Polynomial Coefficient
  separable : (polynomial.map embedding).Separable

namespace SeparablePolynomial

theorem ne_zero (p : SeparablePolynomial) : p.polynomial ≠ 0 :=
  (Polynomial.map_ne_zero_iff embedding_injective).mp p.separable.ne_zero

noncomputable def of_nonzero (p : Polynomial Coefficient) (hp : p ≠ 0) : SeparablePolynomial :=
  ⟨SymbolicScaledSquarefree.polynomial p, SymbolicScaledSquarefree.separable p hp⟩

end SeparablePolynomial

noncomputable def discriminant (p : Polynomial Coefficient) : Coefficient := p.resultant p.derivative

theorem discriminant_map {R : Type*} [CommRing R] (φ : Coefficient →+* R)
    (p : Polynomial Coefficient) (hm : (p.map φ).natDegree = p.natDegree)
    (hd : (p.derivative.map φ).natDegree = p.derivative.natDegree) :
    φ (discriminant p) = (p.map φ).resultant (p.map φ).derivative := by
  rw [discriminant, derivative_map, hm, hd]
  exact (Polynomial.resultant_map_map p p.derivative p.natDegree p.derivative.natDegree φ).symm

theorem separable_iff_discriminant {K : Type*} [Field K] (p : K[X]) (hp : p ≠ 0) :
    p.Separable ↔ p.resultant p.derivative ≠ 0 := by
  have h : p.resultant p.derivative = 0 ↔ ¬ p.Separable := by
    rw [resultant_eq_zero_iff, separable_def]
    exact ⟨fun h => h.2, fun h => ⟨Or.inl hp, h⟩⟩
  tauto

def Candidate (p q : SeparablePolynomial) (c : ℕ) : Prop :=
  c ≤ (p.polynomial.natDegree * q.polynomial.natDegree) ^ 2 ∧
    discriminant (cannyResultant p.polynomial q.polynomial c) ≠ 0

theorem exists_candidate (p q : SeparablePolynomial) : ∃ c, Candidate p q c := by
  let P := p.polynomial.map embedding
  let Q := q.polynomial.map embedding
  obtain ⟨c, hc, hi⟩ := PrimitivePair.exists_bounded_direction
    (L := AlgebraicClosure CoefficientField) P Q p.separable q.separable
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)
  have hs := PrimitivePair.resultant_separable P Q c p.separable q.separable
    (IsAlgClosed.splits _) (IsAlgClosed.splits _) hi
  have hd := (separable_iff_discriminant _ hs.ne_zero).mp hs
  refine ⟨c, ?_, ?_⟩
  · simpa only [P, Q, natDegree_map_eq_of_injective embedding_injective] using hc
  · intro hz
    apply hd
    rw [← CoordinateRecoveryMap.resultant embedding embedding_injective,
      ← discriminant_map embedding _
        (natDegree_map_eq_of_injective embedding_injective _)
        (natDegree_map_eq_of_injective embedding_injective _), hz, map_zero]

noncomputable def direction (p q : SeparablePolynomial) : ℕ := Nat.find (exists_candidate p q)

theorem direction_spec (p q : SeparablePolynomial) : Candidate p q (direction p q) :=
  Nat.find_spec (exists_candidate p q)

noncomputable def parameter (p q : SeparablePolynomial) : Polynomial Coefficient :=
  cannyResultant p.polynomial q.polynomial (direction p q)

theorem parameter_separable (p q : SeparablePolynomial) : ((parameter p q).map embedding).Separable := by
  apply (separable_iff_discriminant _ ?_).mpr
  · rw [← discriminant_map embedding _
      (natDegree_map_eq_of_injective embedding_injective _)
      (natDegree_map_eq_of_injective embedding_injective _)]
    simpa only [parameter, map_zero] using embedding_injective.ne (direction_spec p q).2
  · rw [parameter, CoordinateRecoveryMap.resultant embedding embedding_injective]
    exact PrimitivePair.resultant_ne_zero (p.polynomial.map embedding) (q.polynomial.map embedding)
      (direction p q) p.separable q.separable
      (IsAlgClosed.splits (k := AlgebraicClosure CoefficientField) _)
      (IsAlgClosed.splits _)

noncomputable def combine (p q : SeparablePolynomial) : SeparablePolynomial :=
  ⟨parameter p q, parameter_separable p q⟩

noncomputable def denominator (p q : SeparablePolynomial) : Polynomial Coefficient :=
  PrimitivePair.denominator p.polynomial q.polynomial (direction p q)

noncomputable def leftNumerator (p q : SeparablePolynomial) : Polynomial Coefficient :=
  PrimitivePair.leftNumerator p.polynomial q.polynomial (direction p q)

noncomputable def rightNumerator (p q : SeparablePolynomial) : Polynomial Coefficient :=
  PrimitivePair.rightNumerator p.polynomial q.polynomial (direction p q)

theorem parameter_natDegree (p q : SeparablePolynomial) :
    (parameter p q).natDegree = p.polynomial.natDegree * q.polynomial.natDegree := by
  have h := cannyResultant_natDegree (L := AlgebraicClosure CoefficientField)
    (p.polynomial.map embedding) (q.polynomial.map embedding) (direction p q)
    p.separable q.separable (IsAlgClosed.splits _) (IsAlgClosed.splits _)
  rw [← CoordinateRecoveryMap.resultant embedding embedding_injective] at h
  simpa only [parameter, natDegree_map_eq_of_injective embedding_injective] using h

noncomputable def decode {L : Type*} [Field L] [Algebra CoefficientField L]
    (p q : SeparablePolynomial) (theta : L) : L × L :=
  ((leftNumerator p q).eval₂ ((algebraMap CoefficientField L).comp embedding) theta /
      (denominator p q).eval₂ ((algebraMap CoefficientField L).comp embedding) theta,
    (rightNumerator p q).eval₂ ((algebraMap CoefficientField L).comp embedding) theta /
      (denominator p q).eval₂ ((algebraMap CoefficientField L).comp embedding) theta)

theorem decode_eq {L : Type*} [Field L] [Algebra CoefficientField L]
    (p q : SeparablePolynomial) (theta : L) :
    decode p q theta = PrimitivePair.decode (p.polynomial.map embedding) (q.polynomial.map embedding)
      (direction p q) theta := by
  simp only [decode, PrimitivePair.decode, leftNumerator, rightNumerator, denominator,
    ← CoordinateRecoveryMap.leftNumerator embedding embedding_injective,
    ← CoordinateRecoveryMap.rightNumerator embedding embedding_injective,
    ← CoordinateRecoveryMap.denominator embedding embedding_injective,
    Polynomial.aeval_def, Polynomial.eval₂_map]

theorem separating (p q : SeparablePolynomial) :
    Set.InjOn (shear (direction p q))
      (rootPairs (L := AlgebraicClosure CoefficientField)
        (p.polynomial.map embedding) (q.polynomial.map embedding) :
          Set (AlgebraicClosure CoefficientField × AlgebraicClosure CoefficientField)) := by
  apply (PrimitivePair.resultant_separable_iff _ _ _ p.separable q.separable
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)).mp
  rw [← CoordinateRecoveryMap.resultant embedding embedding_injective]
  exact parameter_separable p q

/-- The actual polynomial and rational formulas give a bijective encoding of
the generic Cartesian root set, with a denominator nonzero at every root. -/
theorem decode_root (p q : SeparablePolynomial) (theta : AlgebraicClosure CoefficientField)
    (ht : (parameter p q).eval₂
      ((algebraMap CoefficientField (AlgebraicClosure CoefficientField)).comp embedding) theta = 0) :
    p.polynomial.eval₂ ((algebraMap CoefficientField (AlgebraicClosure CoefficientField)).comp embedding)
        (decode p q theta).1 = 0 ∧
      q.polynomial.eval₂ ((algebraMap CoefficientField (AlgebraicClosure CoefficientField)).comp embedding)
        (decode p q theta).2 = 0 ∧
      shear (direction p q) (decode p q theta) = theta ∧
      (denominator p q).eval₂
        ((algebraMap CoefficientField (AlgebraicClosure CoefficientField)).comp embedding) theta ≠ 0 := by
  have ht' : Polynomial.aeval theta
      (cannyResultant (p.polynomial.map embedding) (q.polynomial.map embedding) (direction p q)) = 0 := by
    rw [← CoordinateRecoveryMap.resultant embedding embedding_injective, Polynomial.aeval_def,
      Polynomial.eval₂_map]
    exact ht
  have h := PrimitivePair.decode_root (p.polynomial.map embedding) (q.polynomial.map embedding)
    (direction p q) theta p.separable.ne_zero q.separable (IsAlgClosed.splits _) (separating p q) ht'
  rw [← decode_eq] at h
  simpa only [Polynomial.aeval_def, Polynomial.eval₂_map, denominator,
    ← CoordinateRecoveryMap.denominator embedding embedding_injective] using h

end LeanCanny.Algebra.SymbolicPrimitivePair
