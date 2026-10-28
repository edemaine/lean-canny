/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildProbeEntries

/-! # Uniform coefficient budgets for regular-child point probes -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildProbeBounds
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleChildProbeEntries
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildRecords.length BoundedCriticalSampleChildThom.labelWidth
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight
  BoundedCriticalSampleChildQueries.roots BoundedCriticalSampleChildRegularCount.count

noncomputable def bits (P : Inputs) (z : List Bool) : ℕ :=
  BoundedCriticalSampleChildPencilBounds.bits P (hashContext z) + (pointCode z).length + 1
theorem bits_unary {P : Inputs} (h : P.PolyTime) : UnaryFn (bits P) :=
  (((BoundedCriticalSampleChildPencilBounds.bits_unary h).comp hashContext_FP).add (UnaryFn.length pointCode_FP)).add (UnaryFn.const 1)

noncomputable def budget (P : Inputs) (z : List Bool) : ℕ := CharacteristicIntegerBounds.budget (dimension z) (bits P z)
theorem budget_binary {P : Inputs} (h : P.PolyTime) : BinaryFn (budget P) :=
  CharacteristicIntegerBounds.budget_binary dimension_binary (BinaryFn.ofUnary (bits_unary h))

theorem gram_bound (P : Inputs) (e : List Bool) : (gram P e).natAbs ≤
    2 ^ BoundedCriticalSampleChildPencilBounds.bits P (hashContext (pairFst e)) := by
  have H := BoundedCriticalSampleChildBasisGram.entry_bounds P (BoundedCriticalSampleChildPencilEntries.gramQuery (entryQuery e))
  have hc : pairFst (BoundedCriticalSampleChildPencilEntries.gramQuery (entryQuery e)) =
      BoundedCriticalSampleChildWeightedMoments.original (hashContext (pairFst e)) := by
    simp only [BoundedCriticalSampleChildPencilEntries.gramQuery, entryQuery, pairFst_pair]
  rw [hc] at H
  have hb : (gram P e).natAbs ≤ 2 ^ BoundedCriticalSampleChildThom.labelWidth P
      (BoundedCriticalSampleChildWeightedMoments.original (hashContext (pairFst e))) := by
    change (BoundedCriticalSampleChildBasisGram.entry P (BoundedCriticalSampleChildPencilEntries.gramQuery (entryQuery e))).natAbs ≤ _
    omega
  exact hb.trans (Nat.pow_le_pow_right (by decide) (by unfold BoundedCriticalSampleChildPencilBounds.bits; omega))

theorem weighted_bound (P : Inputs) (e : List Bool) : (weighted P e).natAbs ≤
    2 ^ BoundedCriticalSampleChildPencilBounds.bits P (hashContext (pairFst e)) := by
  have H := BoundedCriticalSampleChildWeightedMoments.entry_bits P (entryQuery e)
  have hb : BoundedCriticalSampleChildWeightedMoments.entryBits P (entryQuery e) =
      BoundedCriticalSampleChildPencilBounds.bits P (hashContext (pairFst e)) := by
    simp only [BoundedCriticalSampleChildWeightedMoments.entryBits, entryQuery, pairFst_pair, BoundedCriticalSampleChildPencilBounds.bits]
  rw [hb] at H
  exact (Nat.size_le.mp H).le

theorem constant_bound (P : Inputs) (e : List Bool) : (constant P e).natAbs ≤ 2 ^ bits P (pairFst e) := by
  have hp := (SignedIntegerArithmetic.value_bound (pointCode (pairFst e))).le
  have hg := gram_bound P e
  have hw := weighted_bound P e
  have H := Int.natAbs_sub_le (pointValue (pairFst e) * gram P e) (weighted P e)
  rw [Int.natAbs_mul] at H
  apply H.trans
  calc
    (pointValue (pairFst e)).natAbs * (gram P e).natAbs + (weighted P e).natAbs ≤
        2 ^ (pointCode (pairFst e)).length * 2 ^ BoundedCriticalSampleChildPencilBounds.bits P (hashContext (pairFst e)) +
          2 ^ BoundedCriticalSampleChildPencilBounds.bits P (hashContext (pairFst e)) :=
      Nat.add_le_add (Nat.mul_le_mul hp hg) hw
    _ = 2 ^ (BoundedCriticalSampleChildPencilBounds.bits P (hashContext (pairFst e)) + (pointCode (pairFst e)).length) +
        2 ^ BoundedCriticalSampleChildPencilBounds.bits P (hashContext (pairFst e)) := by rw [pow_add]; ring
    _ ≤ 2 ^ (BoundedCriticalSampleChildPencilBounds.bits P (hashContext (pairFst e)) + (pointCode (pairFst e)).length) +
        2 ^ (BoundedCriticalSampleChildPencilBounds.bits P (hashContext (pairFst e)) + (pointCode (pairFst e)).length) :=
      Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)) _
    _ = 2 ^ bits P (pairFst e) := by rw [bits, pow_succ]; omega

end LeanCanny.Encoding.BoundedCriticalSampleChildProbeBounds
