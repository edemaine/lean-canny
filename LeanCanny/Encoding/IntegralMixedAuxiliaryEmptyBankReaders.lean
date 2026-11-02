/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankCoordinateBounds
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyCompanionSpace
/-! # Original-only actual denominator and cleared-coordinate readers

The original dimension, term word and arity scope derive every leading,
retained denominator, common-Q, cofactor and coordinate coefficient reader.
All caller moduli and terminal prefixes are retained literally.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryParameters
open scoped Classical

variable {n : List Bool → ℕ} {t : List Bool → Term}

private noncomputable def originalSyntax
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :
    IntegralMixedFramedNativeBits.Syntax (parameters n t) (plan hn ht ha) (data hn ht ha) :=
  IntegralMixedEmptyTiltedNative.inputSyntax (parameters n t) (access hn ht) (description hn ht ha)
    (ambient_positive n t) (auxiliary_cap n t) (room n t) (source_width n t)

theorem bank_leading_space
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :
    SpaceFunction (IntegralMixedFramedLeadingBits.value (parameters n t) (plan hn ht ha) (data hn ht ha)) :=
  IntegralMixedFramedLeadingBits.evaluator (parameters n t) (access hn ht) _ _ (originalSyntax hn ht ha)
    (familyInputs hn ht ha) (description hn ht ha).factor_positive (fun _ => Nat.le_refl 1)

theorem bank_denominator_space
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :
    SpaceFunction (IntegralMixedFramedBankDenominatorBits.value (parameters n t) (plan hn ht ha) (data hn ht ha)) :=
  IntegralMixedFramedBankDenominatorBits.evaluator (parameters n t) (access hn ht) _ _ (originalSyntax hn ht ha)
    (familyInputs hn ht ha) (description hn ht ha).factor_positive (fun _ => Nat.le_refl 1)

theorem bank_common_space
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :
    SpaceFunction (fun q => MatrixPower.residueBits
      (IntegralMixedHistory.commonDenominator (IntegralMixedFramedBankDenominatorBits.state (parameters n t) (plan hn ht ha) (data hn ht ha) q) :
        ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
  IntegralMixedFramedBankProductBits.common_evaluator (parameters n t) (access hn ht) _ _ (originalSyntax hn ht ha)
    (familyInputs hn ht ha) (description hn ht ha).factor_positive (fun _ => Nat.le_refl 1)

theorem bank_cofactor_space
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root)
    (skip : List Bool → ℕ) (hs : BinaryFn skip) :
    SpaceFunction (IntegralMixedFramedBankProductBits.value (parameters n t) (plan hn ht ha) (data hn ht ha) skip) :=
  IntegralMixedFramedBankProductBits.evaluator (parameters n t) (access hn ht) _ _ (originalSyntax hn ht ha)
    (familyInputs hn ht ha) (description hn ht ha).factor_positive (fun _ => Nat.le_refl 1) skip hs

noncomputable def bankCoordinateWidth
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) (q : List Bool) : ℕ :=
  (IntegralMixedFramedBankCoordinateBits.weight (parameters n t) (plan hn ht ha) (data hn ht ha) q).size

theorem bankCoordinateWidth_unary
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :
    UnaryFn (bankCoordinateWidth hn ht ha) :=
  (UnaryFn.length (IntegralMixedFramedBankCoordinateBits.weight_binary (parameters n t) (access hn ht)
    (plan hn ht ha) (data hn ht ha)).bits_mem_FP).of_eq
      (fun _ => BinaryNatCode.length_encode _)

theorem bank_coordinate_coefficient_space
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root) :
    SpaceFunction (IntegralMixedFramedBankCoordinateBits.coefficient (parameters n t) (plan hn ht ha) (data hn ht ha)
      (bankCoordinateWidth hn ht ha)) :=
  IntegralMixedFramedBankCoordinateBits.coefficient_evaluator (parameters n t) (access hn ht) _ _ (originalSyntax hn ht ha)
    (familyInputs hn ht ha) (description hn ht ha).factor_positive (fun _ => Nat.le_refl 1)
    _ (bankCoordinateWidth_unary hn ht ha)

theorem bank_coordinate_fit
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) (ha : ∀ root,(t root).arity≤n root)
    (q : List Bool) (i : Fin (IntegralMixedFramedBankDenominatorBits.count (parameters n t) (plan hn ht ha) (data hn ht ha) q)) :
    (IntegralMixedFramedBankCoordinateBits.polynomial (parameters n t) (plan hn ht ha) (data hn ht ha) q).degreeOf i<
      2^bankCoordinateWidth hn ht ha q :=
  (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((IntegralMixedFramedBankCoordinateBits.polynomial_degree _ _ _ q).trans_lt (Nat.lt_size_self _))

end LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyPlan
