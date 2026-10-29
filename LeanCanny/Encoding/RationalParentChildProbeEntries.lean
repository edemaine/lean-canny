/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildPencilBounds
public import LeanCanny.Algebra.SignedIntegerArithmeticFP

/-! # Native constant entries of regular-child point probes

The entry hG-H uses the queried integer descriptor, selected Gram matrix,
and hash-weighted moments. Contexts retain a spare binary feature field for
indexed queries; the constant entry is independent of that field.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildProbeEntries
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open RationalParentChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildRecords.length RationalParentChildThom.labelWidth
  RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight
  RationalParentChildQueries.roots RationalParentChildRegularCount.count

def hashContext (z : List Bool) : List Bool := pairFst z
def pointCode (z : List Bool) : List Bool := pairFst (pairSnd z)
def featureCode (z : List Bool) : List Bool := pairSnd (pairSnd z)
theorem hashContext_FP : hashContext ∈ FP := pairFst_mem_FP
theorem pointCode_FP : pointCode ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem featureCode_FP : featureCode ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
def pointValue (z : List Bool) : ℤ := SignedIntegerArithmetic.value (pointCode z)

def context (b : List Bool) (h : ℤ) (d : ℕ) : List Bool :=
  pair b (pair (SignStatisticBits.integerCode h) (BinaryNatCode.encode d))
theorem pointValue_packet (b : List Bool) (h : ℤ) (d : ℕ) : pointValue (context b h d) = h := by
  simp only [pointValue, pointCode, context, pairFst_pair, pairSnd_pair, SignedIntegerArithmetic.value_packet]

def entryQuery (e : List Bool) : List Bool := pair (hashContext (pairFst e)) (pairSnd e)
theorem entryQuery_FP : entryQuery ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP hashContext_FP) pairSnd_mem_FP

noncomputable def gram (P : Inputs) (e : List Bool) : ℤ := RationalParentChildPencilEntries.gram P (entryQuery e)
noncomputable def weighted (P : Inputs) (e : List Bool) : ℤ := RationalParentChildWeightedMoments.entry P (entryQuery e)
noncomputable def constant (P : Inputs) (e : List Bool) : ℤ := pointValue (pairFst e) * gram P e - weighted P e
theorem gram_evaluator {P : Inputs} (h : P.Access) :
    SpaceFunction (fun e => SignStatisticBits.integerCode (gram P e)) := by
  have E := (RationalParentChildBasisGram.entry_evaluator h).precompose
    (RationalParentChildPencilEntries.gramQuery ∘ entryQuery) (mem_FP_comp entryQuery_FP RationalParentChildPencilEntries.gramQuery_FP)
  exact E.congr (funext fun _ => by simp only [gram, RationalParentChildPencilEntries.gram, Function.comp_apply])

theorem constant_evaluator {P : Inputs} (h : P.Access) :
    SpaceFunction (fun e => SignStatisticBits.integerCode (constant P e)) := by
  have hp := mem_FP_comp pairFst_mem_FP pointCode_FP
  have R := SpaceFunction.ofFP (SignedIntegerArithmetic.canonical ∘ pointCode ∘ pairFst)
    (mem_FP_comp hp SignedIntegerArithmetic.canonical_FP)
  have X : SpaceFunction (fun e => SignStatisticBits.integerCode (pointValue (pairFst e))) :=
    R.congr (funext fun _ => by simp only [Function.comp_apply, SignedIntegerArithmetic.canonical_eq, pointValue])
  have W0 := (RationalParentChildWeightedMoments.evaluator h).precompose entryQuery entryQuery_FP
  have W : SpaceFunction (fun e => SignStatisticBits.integerCode (weighted P e)) := W0
  have M0 := (X.pairOutputs (gram_evaluator h)).postcompose IntegerSumBits.multiply IntegerSumBits.multiply_mem_FP
  have M : SpaceFunction (fun e => SignStatisticBits.integerCode (pointValue (pairFst e) * gram P e)) :=
    M0.congr (funext fun _ => by simp only [Function.comp_apply, IntegerSumBits.multiply_codes])
  have H := (M.pairOutputs W).postcompose SignedIntegerArithmetic.subtract SignedIntegerArithmetic.subtract_FP
  exact H.congr (funext fun _ => by simp only [Function.comp_apply, SignedIntegerArithmetic.subtract_packet, constant])

abbrev dimension (z : List Bool) : ℕ := RationalParentChildPencilEntries.dimension (hashContext z)
theorem dimension_binary : BinaryFn dimension := RationalParentChildPencilEntries.dimension_binary.comp hashContext_FP

end LeanCanny.Encoding.RationalParentChildProbeEntries
