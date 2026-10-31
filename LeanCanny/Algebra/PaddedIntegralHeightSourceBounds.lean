/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralHeightBounds
public import LeanCanny.Algebra.PaddedIntegralHeightCoefficientSpace

/-! # Original-source budgets for actual canonical height coefficients

All output budgets are derived from the original coefficient matrices.
The same original bound supplies the selected-matrix reader, so the native
coefficient program and its proved height bound refer to the same source.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralHeightSourceBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial PaddedIntegralGeneratorSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Bounds (S : Source) where
  height : List Bool → ℕ
  coefficient : ∀ c k i j, (S.coefficient c k i j).natAbs ≤ 2 ^ height c

def selected (S : Source) (B : Bounds S) : PaddedIntegralSelectedMatrixSource.Bounds S where
  height := B.height
  selected c := B.coefficient c (S.degree c)

def numeratorBudget (S : Source) (B : Bounds S) (c : List Bool) : ℕ :=
  PaddedIntegralParameterExtension.numeratorHeight (count (S.arity c) (S.width c)) (2 ^ S.width c) (B.height c)

def denominatorBudget (S : Source) (B : Bounds S) (c : List Bool) : ℕ :=
  CharacteristicIntegerBounds.budget (count (S.arity c) (S.width c)) (B.height c)

theorem oldRank_binary (S : Source) (a : Access S) : BinaryFn (fun c => count (S.arity c) (S.width c)) := by
  apply BinaryFn.of_bits
  exact mem_FP_of_eq (countCode_mem_FP a.arity a.width) (fun c => countCode_code _ _ c)

theorem numeratorBudget_binary (S : Source) (B : Bounds S) (a : Access S) (hH : BinaryFn B.height) :
    BinaryFn (numeratorBudget S B) :=
  PaddedIntegralParameterExtension.numeratorHeight_binary (oldRank_binary S a) ((BinaryFn.const 2).powUnary a.width) hH

theorem denominatorBudget_binary (S : Source) (B : Bounds S) (a : Access S) (hH : BinaryFn B.height) :
    BinaryFn (denominatorBudget S B) := CharacteristicIntegerBounds.budget_binary (oldRank_binary S a) hH

theorem coefficient_height (S : Source) (B : Bounds S) (c : List Bool)
    (r : Fin (count (S.arity c + 1) (S.width c))) :
    (((PaddedIntegralHeightCoefficientBits.family S).polynomial c).coeff (vector (S.arity c + 1) (S.width c) r)).natAbs ≤
      2 ^ numeratorBudget S B c := by
  let := S.ring c
  let := S.nontrivial c
  exact PaddedIntegralParameterExtension.numerator_coefficient_height (S.basis c) (S.polynomial c)
    (S.degree c) (B.height c) (B.coefficient c) r

theorem denominator_height (S : Source) (B : Bounds S) (c : List Bool) :
    (PaddedIntegralHeightSourceMatrix.denominator S c).natAbs ≤ 2 ^ denominatorBudget S B c :=
  IntegralInverseMatrixBounds.denominator_height (S.coefficient c (S.degree c)) (B.height c) (B.coefficient c (S.degree c))

theorem powered_evaluator (S : Source) (B : Bounds S) (a : Access S) (hH : BinaryFn B.height)
    (E : SpaceFunction a.entry) (G V : List Bool → ℕ) (target modulus : List Bool → List Bool)
    (hG : UnaryFn G) (hV : UnaryFn V) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (PaddedIntegralHeightCoefficientBits.family S).arity V
      ((PaddedIntegralHeightCoefficientBits.family S).poweredPolynomial G) target modulus) :=
  PaddedIntegralHeightCoefficientBits.powered_evaluator S (selected S B) a hH E G V target modulus hG hV ht hm

end LeanCanny.Algebra.PaddedIntegralHeightSourceBounds
