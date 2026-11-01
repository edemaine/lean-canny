/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralScalarSpaceDegree
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace
/-! # Scalar companions for actual integer-polynomial births -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralIntegerCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

theorem coefficient_eq (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ)
    (hp : ∀ q, letI := F.ring q; F.polynomial q = (p q).map (Int.castRingHom (F.carrier q))) (q : List Bool) (k : ℕ) :
    F.coefficient q k = ((p q).coeff k : ZMod (F.modulus q)) • 1 := by
  let := F.ring q
  ext r t
  change (((Algebra.leftMulMatrix (F.basis q).finBasis ((F.polynomial q).coeff k)) r t : ℤ) : ZMod (F.modulus q)) = _
  rw [hp q, Polynomial.coeff_map]
  change (((Algebra.leftMulMatrix (F.basis q).finBasis (((p q).coeff k : ℤ) : F.carrier q)) r t : ℤ) : ZMod (F.modulus q)) = _
  simp only [map_intCast, Matrix.intCast_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp only [Int.cast_zero, Int.cast_id, mul_zero, mul_one]

noncomputable def leading (_F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ) (q : List Bool) : ℤ := (p q).leadingCoeff

theorem leading_eq (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ)
    (hp : ∀ q, letI := F.ring q; F.polynomial q = (p q).map (Int.castRingHom (F.carrier q)))
    (hd : ∀ q, F.degree q = (p q).natDegree) (q : List Bool) :
    letI := F.ring q
    (F.polynomial q).coeff (F.degree q) = (leading F p q : F.carrier q) := by
  let := F.ring q
  rw [hp q, Polynomial.coeff_map, hd q, Polynomial.coeff_natDegree]
  rfl

noncomputable def scalarFamily (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ)
    (hp : ∀ q, letI := F.ring q; F.polynomial q = (p q).map (Int.castRingHom (F.carrier q)))
    (hd : ∀ q, F.degree q = (p q).natDegree) : IntegralScalarGeneratorBits.Family :=
  IntegralScalarGeneratorBits.finFamily F (leading F p) (leading_eq F p hp hd)

structure Controls (F : PaddedIntegralGeneratorFinBits.Family.{u}) : Prop where
  width : UnaryFn F.width
  modulus : BinaryFn F.modulus
  row : BinaryFn (fun q => (F.row q).val)
  col : BinaryFn (fun q => (F.col q).val)

theorem native (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ)
    (hp : ∀ q, letI := F.ring q; F.polynomial q = (p q).map (Int.castRingHom (F.carrier q)))
    (hd : ∀ q, F.degree q = (p q).natDegree) (a : Controls F) : IntegralScalarSpaceDegreeBits.Native (scalarFamily F p hp hd) where
  scalarDegree := (BinaryFn.const 2).powUnary a.width
  modulus := a.modulus
  row := a.row.mod ((BinaryFn.const 2).powUnary a.width)
  col := a.col.mod ((BinaryFn.const 2).powUnary a.width)
  oldRow := a.row.div ((BinaryFn.const 2).powUnary a.width)
  oldCol := a.col.div ((BinaryFn.const 2).powUnary a.width)
end LeanCanny.Algebra.IntegralIntegerCompanionBits
