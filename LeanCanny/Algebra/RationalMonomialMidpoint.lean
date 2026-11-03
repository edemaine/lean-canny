/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthMonomialSpace
public import LeanCanny.Algebra.IntegerPolynomialRationalPointSource
public import LeanCanny.Algebra.MvCoefficientMass
/-! # Same-bank midpoint with two sparse monomials

The common denominator is twice the old common integer. Neither sign nor
unit status of that integer enters the coefficient representation.
-/
@[expose] public section
namespace LeanCanny.Algebra.RationalMonomialMidpoint
open scoped Classical

structure Family where
  arity : List Bool→ℕ
  leftIndex : List Bool→ℕ
  rightIndex : List Bool→ℕ
  leftWeight : List Bool→ℕ
  rightWeight : List Bool→ℕ
  left : IntegerPolynomialRationalPointSource.Scalars
  right : IntegerPolynomialRationalPointSource.Scalars
  sameDenominator : ∀ c,right.denominator c=left.denominator c

noncomputable def leftPolynomial (F : Family) :=
  FixedWidthMonomialBits.polynomial F.arity F.leftIndex F.leftWeight F.left.numerator
noncomputable def rightPolynomial (F : Family) :=
  FixedWidthMonomialBits.polynomial F.arity F.rightIndex F.rightWeight F.right.numerator
noncomputable def numerator (F : Family) (c : List Bool) :=leftPolynomial F c+rightPolynomial F c
noncomputable def denominator (F : Family) (c : List Bool) :=2*F.left.denominator c
noncomputable def degreeBound (F : Family) (c : List Bool) :=max (F.leftWeight c) (F.rightWeight c)
noncomputable def massBound (F : Family) (c : List Bool) :=max (F.left.mass c) (F.right.mass c)+1

private theorem monomial_degree (A i w : List Bool→ℕ) (a : List Bool→ℤ) (c : List Bool) :
    (FixedWidthMonomialBits.polynomial A i w a c).totalDegree≤w c :=by
  unfold FixedWidthMonomialBits.polynomial
  split_ifs
  · exact (MvPolynomial.totalDegree_monomial_le _ _).trans_eq (by simp)
  · simp

private theorem monomial_mass (A i w : List Bool→ℕ) (a : List Bool→ℤ) (c : List Bool) :
    MvMass.mass (FixedWidthMonomialBits.polynomial A i w a c)≤(a c).natAbs :=by
  unfold FixedWidthMonomialBits.polynomial
  split_ifs
  · rw [MvMass.monomial]
  · simp

theorem numerator_degree (F : Family) (c : List Bool) :
    (numerator F c).totalDegree≤degreeBound F c :=
  (MvPolynomial.totalDegree_add _ _).trans (max_le_max
    (monomial_degree _ _ _ _ _) (monomial_degree _ _ _ _ _))

theorem numerator_mass (F : Family) (c : List Bool) :
    MvMass.mass (numerator F c)≤2^massBound F c :=by
  have HL : MvMass.mass (leftPolynomial F c)≤2^(max (F.left.mass c) (F.right.mass c)) :=
    ((monomial_mass _ _ _ _ _).trans (F.left.numerator_bound c)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have HR : MvMass.mass (rightPolynomial F c)≤2^(max (F.left.mass c) (F.right.mass c)) :=
    ((monomial_mass _ _ _ _ _).trans (F.right.numerator_bound c)).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  exact ((MvMass.add_le _ _).trans (Nat.add_le_add HL HR)).trans_eq
    (by unfold massBound;rw [pow_succ];omega)

theorem denominator_bound (F : Family) (c : List Bool) :
    (denominator F c).natAbs≤2^massBound F c :=by
  unfold denominator
  rw [Int.natAbs_mul]
  have H:=(F.left.denominator_bound c).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_max_left (F.left.mass c) (F.right.mass c)))
  calc
    _≤2*2^(max (F.left.mass c) (F.right.mass c)):=Nat.mul_le_mul_left 2 H
    _=_:=by unfold massBound;rw [pow_succ];omega

theorem numerator_eval (F : Family) (c : List Bool) (z : Fin (F.arity c)→ℝ)
    (hl : F.leftIndex c<F.arity c) (hr : F.rightIndex c<F.arity c) :
    (numerator F c).eval₂ (Int.castRingHom ℝ) z=
      (F.left.numerator c:ℝ)*z ⟨F.leftIndex c,hl⟩^F.leftWeight c+
        (F.right.numerator c:ℝ)*z ⟨F.rightIndex c,hr⟩^F.rightWeight c :=by
  simp [numerator,leftPolynomial,rightPolynomial,FixedWidthMonomialBits.polynomial,
    hl,hr,MvPolynomial.eval₂_monomial]

theorem midpoint (F : Family) (c : List Bool) (z : Fin (F.arity c)→ℝ)
    (hl : F.leftIndex c<F.arity c) (hr : F.rightIndex c<F.arity c) :
    (numerator F c).eval₂ (Int.castRingHom ℝ) z/(denominator F c:ℝ)=
      ((F.left.numerator c:ℝ)*z ⟨F.leftIndex c,hl⟩^F.leftWeight c/(F.left.denominator c:ℝ)+
        (F.right.numerator c:ℝ)*z ⟨F.rightIndex c,hr⟩^F.rightWeight c/(F.right.denominator c:ℝ))/2 :=by
  rw [numerator_eval F c z hl hr,F.sameDenominator c]
  simp only [denominator,Int.cast_mul,Int.cast_ofNat]
  simp only [add_div,div_div]
  congr 1 <;> congr 1 <;> ring

end LeanCanny.Algebra.RationalMonomialMidpoint
