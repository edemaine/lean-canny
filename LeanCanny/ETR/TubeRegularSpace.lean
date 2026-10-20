/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularDerivative
public import LeanCanny.Algebra.ModularNegFP

/-! # Complete coefficient readers for the regular tube projection system

Row zero is the reciprocal equation; row k+1 selects original row k. All other
row words inherit the original total decoder. One source or derivative child
suffices for each coefficient, with no modular inverses or uncharged work.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRegularBits
open Complexity LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Algebra LeanCanny.Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubePolynomial.integerProjection
  TubeIndexed.projectionResidue TubeRegularDerivative.derivativeResidue

def oldRow (row : List Bool → List Bool) (c : List Bool) : List Bool := BinaryNat.sub (pair (row c) [true])

theorem oldRow_mem_FP {row : List Bool → List Bool} (hr : row ∈ FP) : oldRow row ∈ FP := by
  have hq := mem_FP_pair hr (constFn_mem_FP [true])
  have h := mem_FP_comp hq BinaryNat.sub_mem_FP
  exact mem_FP_of_eq (g := oldRow row) h (fun _ => by simp only [oldRow, Function.comp_apply])

theorem oldRow_of_succ (row : List Bool → List Bool) (c : List Bool) (k : ℕ)
    (h : row c = BinaryNatCode.encode (k + 1)) : oldRow row c = BinaryNatCode.encode k := by
  rw [oldRow, h, BinaryNat.sub_pair]
  change (Nat.fromBitsLE (BinaryNatCode.encode (k + 1)) - 1).bits = _
  rw [MacaulayBits.fromBits_encode, Nat.add_sub_cancel]
  rfl

noncomputable def decodedIndex (source row : List Bool → List Bool) (c : List Bool) : TubeRegularSource.Index (source c) :=
  if BinaryNat.normalize (row c) = [] then none
  else some (TubeProjection.decodedRow (TubeIndexed.compiled source) (oldRow row) c)


theorem decodedIndex_reciprocal (source row : List Bool → List Bool) (c : List Bool)
    (h : BinaryNat.normalize (row c) = []) : decodedIndex source row c = none := by
  rw [decodedIndex, ite_eq_left h]

theorem decodedIndex_of_code (source row : List Bool → List Bool) (c : List Bool)
    (j : TubeSource.ProjectionIndex (source c))
    (h : row c = BinaryNatCode.encode (TubeProjectionRow.code (TubeIndexed.arity (source c)) j + 1)) :
    decodedIndex source row c = some j := by
  have hn : BinaryNat.normalize (row c) ≠ [] := by
    rw [h, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    intro hz
    have hh := (BinaryNat.bits_eq_nil_iff _).mp hz
    omega
  rw [decodedIndex, ite_eq_right hn]
  apply congrArg some
  apply TubeProjection.decodedRow_of_code
  exact oldRow_of_succ row c _ h

def negativeOne (modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (BinaryNat.succ (modulus c)) (ArithmeticBits.one (BinaryNat.succ (modulus c))))

theorem negativeOne_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : negativeOne modulus ∈ FP := by
  have hmod := mem_FP_comp hm BinaryNat.succ_mem_FP
  have hone := mem_FP_comp hmod ArithmeticBits.one_mem_FP
  have hq := mem_FP_pair hmod hone
  have h := mem_FP_comp hq ArithmeticBits.negate_mem_FP
  exact mem_FP_of_eq (g := negativeOne modulus) h (fun _ => by simp only [negativeOne, Function.comp_apply])

theorem negativeOne_correct (modulus : List Bool → List Bool) (c : List Bool) :
    negativeOne modulus c = residueBits (-1 : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let : NeZero (Nat.fromBitsLE (modulus c) + 1) := ⟨by omega⟩
  rw [negativeOne, BinaryNat.succ_eq_bits]
  change ArithmeticBits.negate (pair (BinaryNatCode.encode _) (ArithmeticBits.one (BinaryNatCode.encode _))) = _
  rw [ArithmeticBits.one_residueBits, ArithmeticBits.negate_residueBits]

noncomputable def value (source active row modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  if BinaryNat.normalize (row (pairFst q)) = [] then
    ReciprocalBits.inverseValue (TubeHomogenization.dimension source) (TubeHomogenization.width source)
      (TubeRegularDerivative.derivativeResidue source active modulus) (negativeOne modulus) q
  else ReciprocalBits.embeddedValue (TubeHomogenization.width source)
    (TubeIndexed.projectionResidue source active (oldRow row) modulus) q

noncomputable def evaluator (source active row modulus : List Bool → List Bool)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value source active row modulus) := by
  have hN : UnaryFn (TubeHomogenization.dimension source) := TubeIndexed.projectionDimension_unary.comp hs
  have hW : UnaryFn (TubeHomogenization.width source) := TubeIndexed.blockWidth_unary.comp hs
  have ED := TubeRegularDerivative.evaluator source active modulus hs ha hm
  have EI := ReciprocalBits.inverseEvaluator hN hW ED (negativeOne_mem_FP hm)
  have EO := TubeIndexed.projectionResidueEvaluator source active (oldRow row) modulus hs ha (oldRow_mem_FP hr) hm
  have EE := ReciprocalBits.embeddedEvaluator hW EO
  have htag := mem_FP_comp (mem_FP_comp pairFst_mem_FP hr) BinaryNat.normalize_mem_FP
  have ES := SpaceFunction.branch (fun q => decide (BinaryNat.normalize (row (pairFst q)) = []))
    (stringEq_fppred htag (constFn_mem_FP [])).flag_mem_FP EI EE
  exact ES.congr (funext fun q => by simp only [value, decide_eq_true_eq])

theorem value_packet (source active row modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    value source active row modulus (pair c (BinaryNatCode.encode r)) = residueBits
      (((TubeRegularSource.polynomial (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
        (decodedIndex source row c)).coeff
          (FixedWidthPolynomial.nativeExponent (TubeHomogenization.outputEquiv (source c))
            (TubeHomogenization.width source c) r) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  dsimp +instances only [TubeIndexed.arity]
  rw [value, pairFst_pair]
  by_cases h : BinaryNat.normalize (row c) = []
  · rw [ite_eq_left h, decodedIndex, ite_eq_left h]
    simp only [TubeRegularSource.polynomial.eq_def]
    apply ReciprocalBits.inverse_packet (TubeHomogenization.dimension source) (TubeHomogenization.width source)
      (TubeRegularDerivative.derivativeResidue source active modulus) (negativeOne modulus) c
      (variableEquiv (TubeIndexed.arity (source c))) _ _
      (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus c) + 1)))
    · simp [residueBits, BinaryNatCode.encode]
    · simpa only [Int.cast_neg, Int.cast_one] using negativeOne_correct modulus c
    · intro k
      change TubeRegularDerivative.derivativeResidue source active modulus (pair c (BinaryNatCode.encode k)) =
        TubeRegularDerivative.derivativeAt source active modulus c k
      exact TubeRegularDerivative.derivative_packet source active modulus c k
  · rw [ite_eq_right h, decodedIndex, ite_eq_right h]
    simp only [TubeRegularSource.polynomial.eq_def]
    apply ReciprocalBits.embedded_packet (TubeHomogenization.dimension source) (TubeHomogenization.width source)
      (TubeIndexed.projectionResidue source active (oldRow row) modulus) c
      (variableEquiv (TubeIndexed.arity (source c))) _
      (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (modulus c) + 1)))
    · simp [residueBits, BinaryNatCode.encode]
    · intro k
      change TubeIndexed.projectionResidue source active (oldRow row) modulus (pair c (BinaryNatCode.encode k)) =
        TubeIndexed.projectionAt source active (oldRow row) modulus c k
      exact TubeIndexed.projectionResidue_packet source active (oldRow row) modulus c k

end LeanCanny.ETR.TubeRegularBits
