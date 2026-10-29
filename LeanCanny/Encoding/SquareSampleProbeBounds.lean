/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleProbeEntries

/-! # Uniform coefficient budgets for regular square-system point probes -/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleProbeBounds
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open SquareSampleProbeEntries
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleRecords.length SquareSampleThom.labelWidth
  SquareSampleCoordinates.parameterDegree SquareSampleCoordinates.baseHeight
  SquareSampleQueries.roots SquareSampleRegularCount.count

noncomputable def bits (P : Inputs) (z : List Bool) : ℕ :=
  SquareSamplePencilBounds.bits P (hashContext z) + (pointCode z).length + 1
theorem bits_unary {P : Inputs} (h : P.Access) : UnaryFn (bits P) :=
  (((SquareSamplePencilBounds.bits_unary h).comp hashContext_FP).add (UnaryFn.length pointCode_FP)).add (UnaryFn.const 1)

noncomputable def budget (P : Inputs) (z : List Bool) : ℕ := CharacteristicIntegerBounds.budget (dimension z) (bits P z)
theorem budget_binary {P : Inputs} (h : P.Access) : BinaryFn (budget P) :=
  CharacteristicIntegerBounds.budget_binary dimension_binary (BinaryFn.ofUnary (bits_unary h))

theorem gram_bound (P : Inputs) (e : List Bool) : (gram P e).natAbs ≤
    2 ^ SquareSamplePencilBounds.bits P (hashContext (pairFst e)) := by
  have H := SquareSampleBasisGram.entry_bounds P (SquareSamplePencilEntries.gramQuery (entryQuery e))
  have hc : pairFst (SquareSamplePencilEntries.gramQuery (entryQuery e)) =
      SquareSampleWeightedMoments.original (hashContext (pairFst e)) := by
    simp only [SquareSamplePencilEntries.gramQuery, entryQuery, pairFst_pair]
  rw [hc] at H
  have hb : (gram P e).natAbs ≤ 2 ^ SquareSampleThom.labelWidth P
      (SquareSampleWeightedMoments.original (hashContext (pairFst e))) := by
    change (SquareSampleBasisGram.entry P (SquareSamplePencilEntries.gramQuery (entryQuery e))).natAbs ≤ _
    omega
  exact hb.trans (Nat.pow_le_pow_right (by decide) (by unfold SquareSamplePencilBounds.bits; omega))

theorem weighted_bound (P : Inputs) (e : List Bool) : (weighted P e).natAbs ≤
    2 ^ SquareSamplePencilBounds.bits P (hashContext (pairFst e)) := by
  have H := SquareSampleWeightedMoments.entry_bits P (entryQuery e)
  have hb : SquareSampleWeightedMoments.entryBits P (entryQuery e) =
      SquareSamplePencilBounds.bits P (hashContext (pairFst e)) := by
    simp only [SquareSampleWeightedMoments.entryBits, entryQuery, pairFst_pair, SquareSamplePencilBounds.bits]
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
        2 ^ (pointCode (pairFst e)).length * 2 ^ SquareSamplePencilBounds.bits P (hashContext (pairFst e)) +
          2 ^ SquareSamplePencilBounds.bits P (hashContext (pairFst e)) :=
      Nat.add_le_add (Nat.mul_le_mul hp hg) hw
    _ = 2 ^ (SquareSamplePencilBounds.bits P (hashContext (pairFst e)) + (pointCode (pairFst e)).length) +
        2 ^ SquareSamplePencilBounds.bits P (hashContext (pairFst e)) := by rw [pow_add]; ring
    _ ≤ 2 ^ (SquareSamplePencilBounds.bits P (hashContext (pairFst e)) + (pointCode (pairFst e)).length) +
        2 ^ (SquareSamplePencilBounds.bits P (hashContext (pairFst e)) + (pointCode (pairFst e)).length) :=
      Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)) _
    _ = 2 ^ bits P (pairFst e) := by rw [bits, pow_succ]; omega

end LeanCanny.Encoding.SquareSampleProbeBounds
