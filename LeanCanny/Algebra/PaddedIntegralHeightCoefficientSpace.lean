/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralHeightSourceSpace
public import LeanCanny.Algebra.IntegralCoordinatePoweredSpace

/-! # Native canonical height coefficients from original scalar data

The actual numerator matrix is constructed internally. Reading its column
zero gives the canonical height representative, including for independent
query widths and coordinate-dependent powers. All calls are charged to
the original scalar-polynomial coefficient-matrix reader.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralHeightCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open PaddedIntegralGeneratorSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def family (S : Source) : IntegralCoordinateCoefficientBits.Family where
  arity c := S.arity c + 1
  width := S.width
  carrier c := by
    letI := S.ring c
    exact PaddedIntegralParameterExtension.Extension (S.polynomial c) (S.degree c) (2 ^ S.width c)
  ring c := by
    letI := S.ring c
    exact inferInstance
  basis c := by
    letI := S.ring c
    letI := S.nontrivial c
    exact PaddedIntegralParameterExtension.coordinateBasis (S.basis c) (S.polynomial c) (S.degree c)
  element c := by
    letI := S.ring c
    letI := S.nontrivial c
    exact PaddedIntegralParameterExtension.numerator (S.basis c) (S.polynomial c) (S.degree c)

theorem matrix_eq (S : Source) (c : List Bool) :
    (family S).matrix c = PaddedIntegralHeightSourceMatrix.matrix S c := rfl

theorem polynomial_eq (S : Source) (c : List Bool) :
    letI := S.ring c
    letI := S.nontrivial c
    (family S).polynomial c =
      PaddedIntegralParameterExtension.numeratorPolynomial (S.basis c) (S.polynomial c) (S.degree c) := rfl

theorem degree (S : Source) (c : List Bool) :
    ((family S).polynomial c).totalDegree ≤ (S.arity c + 1) * (2 ^ S.width c - 1) := by
  let := S.ring c
  let := S.nontrivial c
  exact PaddedIntegralParameterExtension.numeratorPolynomial_degree (S.basis c) (S.polynomial c) (S.degree c)

theorem entry_packet (S : Source) (c mw : List Bool)
    (i j : Fin (count ((family S).arity c) ((family S).width c))) :
    PaddedIntegralHeightSourceBits.value S
      (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (((family S).matrix c i j : ℤ) : ZMod (Nat.fromBitsLE mw + 1)) := by
  rw [matrix_eq]
  exact PaddedIntegralHeightSourceBits.value_packet S c mw i j

theorem evaluator (S : Source) (B : PaddedIntegralSelectedMatrixSource.Bounds S) (a : Access S)
    (hh : BinaryFn B.height) (E : SpaceFunction a.entry) (V : List Bool → ℕ)
    (target modulus : List Bool → List Bool) (hV : UnaryFn V) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (family S).arity V (family S).polynomial target modulus) :=
  IntegralCoordinateCoefficientBits.wide_evaluator (family S) V target modulus (PaddedIntegralHeightSourceBits.value S)
    (a.arity.add (UnaryFn.const 1)) a.width hV ht hm (PaddedIntegralHeightSourceBits.evaluator S B a hh E)
    (entry_packet S)

theorem powered_evaluator (S : Source) (B : PaddedIntegralSelectedMatrixSource.Bounds S) (a : Access S)
    (hh : BinaryFn B.height) (E : SpaceFunction a.entry) (G V : List Bool → ℕ)
    (target modulus : List Bool → List Bool) (hG : UnaryFn G) (hV : UnaryFn V) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (family S).arity V ((family S).poweredPolynomial G) target modulus) :=
  IntegralCoordinateCoefficientBits.powered_evaluator (family S) G V target modulus (PaddedIntegralHeightSourceBits.value S)
    hG (a.arity.add (UnaryFn.const 1)) a.width hV ht hm (PaddedIntegralHeightSourceBits.evaluator S B a hh E)
    (entry_packet S)

end LeanCanny.Algebra.PaddedIntegralHeightCoefficientBits
