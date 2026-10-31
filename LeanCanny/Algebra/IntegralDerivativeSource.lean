/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCoefficientSource
public import LeanCanny.Algebra.AdditivePolynomialDerivative
public import LeanCanny.Algebra.FixedWidthDerivativeBinarySpace
public import LeanCanny.Algebra.IntegralPurePowerReductionCorrect

/-! # Native partial coefficients in the original parameter algebra

Derivative queries keep the original record, both old basis ranks, and a
spatial exponent word. The scalar coefficient program reads one bumped
original coefficient; old parameter monomials are never enumerated.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Source extends IntegralClearedCoefficientBits.Source where
  selected : ∀ c, Fin (arity c)
  degree : List Bool → ℕ
  degree_pos : ∀ c, 0 < degree c
  degree_le : ∀ c, letI := ring c
    (polynomial c).totalDegree ≤ degree c
  degree_lt : ∀ c, degree c < 2 ^ sourceWidth c

structure Access (S : Source) extends IntegralClearedCoefficientBits.Access S.toSource where
  selected : UnaryFn (fun c => (S.selected c).val)
  degree : BinaryFn S.degree

def original (z : List Bool) : List Bool := pairFst (pairFst z)
theorem original_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

def arity (S : Source) (z : List Bool) := S.arity (original z)
def width (S : Source) (z : List Bool) := S.sourceWidth (original z)
def degree (S : Source) (z : List Bool) := S.degree (original z)
def selected (S : Source) (z : List Bool) := (S.selected (original z)).val
def modulus (S : Source) (z : List Bool) := BinaryNatCode.encode (S.modulus (original z))

def coefficientQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)
theorem coefficientQuery_FP : coefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem coefficientQuery_packet (z : List Bool) (k : ℕ) :
    coefficientQuery (pair z (BinaryNatCode.encode k)) = pair (pairFst z) (BinaryNatCode.encode k) := by
  simp only [coefficientQuery, pairFst_pair, pairSnd_pair]

noncomputable def value (S : Source) (a : Access S) : List Bool → List Bool :=
  FixedWidthDerivativeBits.value (arity S) (width S) (width S) (degree S) (selected S) pairSnd (modulus S)
    (a.coefficient ∘ coefficientQuery)

theorem evaluator (S : Source) (a : Access S) (E : SpaceFunction a.coefficient) : SpaceFunction (value S a) := by
  have HM : BinaryFn (fun z => S.modulus (original z)) := a.modulus.comp original_FP
  exact FixedWidthDerivativeBits.evaluator_binary_degree (arity S) (width S) (width S) (degree S) (selected S)
    pairSnd (modulus S) (E.precompose coefficientQuery coefficientQuery_FP)
    (a.arity.comp original_FP) (a.sourceWidth.comp original_FP) (a.sourceWidth.comp original_FP)
    (a.degree.comp original_FP) (a.selected.comp original_FP) pairSnd_mem_FP HM.bits_mem_FP

end LeanCanny.Algebra.IntegralDerivativeBits
