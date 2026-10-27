/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberProbeEntries

/-! # Uniform coefficient budgets for pointwise signature probes -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberProbeBounds
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleFiberProbeEntries
open scoped Classical

noncomputable def bits (F : BoundedAlgebraicSlice.Family) (z : List Bool) : ℕ :=
  BoundedCriticalSampleFiberPencilBounds.bits F (hashContext z) + (pointCode z).length + 1
theorem bits_unary {F : BoundedAlgebraicSlice.Family} (A : F.Access) : UnaryFn (bits F) :=
  (((BoundedCriticalSampleFiberPencilBounds.bits_unary A).comp hashContext_FP).add (UnaryFn.length pointCode_FP)).add (UnaryFn.const 1)

noncomputable def budget (F : BoundedAlgebraicSlice.Family) (z : List Bool) : ℕ := CharacteristicIntegerBounds.budget (dimension z) (bits F z)
theorem budget_binary {F : BoundedAlgebraicSlice.Family} (A : F.Access) : BinaryFn (budget F) :=
  CharacteristicIntegerBounds.budget_binary dimension_binary (BinaryFn.ofUnary (bits_unary A))

theorem gram_bound (P : Readers) (F : BoundedAlgebraicSlice.Family) (e : List Bool) : (gram P F e).natAbs ≤
    2 ^ BoundedCriticalSampleFiberPencilBounds.bits F (hashContext (pairFst e)) := by
  have H := BoundedCriticalSampleFiberBasisGram.entry_bound P F (BoundedCriticalSampleFiberPencilEntries.gramQuery (entryQuery e))
  have hc : BoundedCriticalSampleSlice.context (pairFst (BoundedCriticalSampleFiberPencilEntries.gramQuery (entryQuery e))) =
      BoundedCriticalSampleSlice.context (BoundedCriticalSampleFiberWeightedMoments.original (hashContext (pairFst e))) := by
    simp only [BoundedCriticalSampleFiberPencilEntries.gramQuery, entryQuery, pairFst_pair]
  rw [hc] at H
  have hb : (gram P F e).natAbs ≤ 2 ^ (F.degree (BoundedCriticalSampleSlice.context (BoundedCriticalSampleFiberWeightedMoments.original (hashContext (pairFst e))))).size := by
    change (BoundedCriticalSampleFiberBasisGram.entry P F (BoundedCriticalSampleFiberPencilEntries.gramQuery (entryQuery e))).natAbs ≤ _
    exact H.trans (Nat.lt_size_self _).le
  exact hb.trans (Nat.pow_le_pow_right (by decide) (by unfold BoundedCriticalSampleFiberPencilBounds.bits; omega))

theorem weighted_bound (P : Readers) (F : BoundedAlgebraicSlice.Family) (e : List Bool) : (weighted P F e).natAbs ≤
    2 ^ BoundedCriticalSampleFiberPencilBounds.bits F (hashContext (pairFst e)) := by
  have H := BoundedCriticalSampleFiberWeightedMoments.entry_bits P F (entryQuery e)
  have hb : BoundedCriticalSampleFiberWeightedMoments.entryBits F (entryQuery e) =
      BoundedCriticalSampleFiberPencilBounds.bits F (hashContext (pairFst e)) := by
    simp only [BoundedCriticalSampleFiberWeightedMoments.entryBits, entryQuery, pairFst_pair, BoundedCriticalSampleFiberPencilBounds.bits]
  rw [hb] at H
  exact (Nat.size_le.mp H).le

theorem constant_bound (P : Readers) (F : BoundedAlgebraicSlice.Family) (e : List Bool) : (constant P F e).natAbs ≤ 2 ^ bits F (pairFst e) := by
  have hp := (SignedIntegerArithmetic.value_bound (pointCode (pairFst e))).le
  have hg := gram_bound P F e
  have hw := weighted_bound P F e
  have H := Int.natAbs_sub_le (pointValue (pairFst e) * gram P F e) (weighted P F e)
  rw [Int.natAbs_mul] at H
  apply H.trans
  calc
    (pointValue (pairFst e)).natAbs * (gram P F e).natAbs + (weighted P F e).natAbs ≤
        2 ^ (pointCode (pairFst e)).length * 2 ^ BoundedCriticalSampleFiberPencilBounds.bits F (hashContext (pairFst e)) +
          2 ^ BoundedCriticalSampleFiberPencilBounds.bits F (hashContext (pairFst e)) :=
      Nat.add_le_add (Nat.mul_le_mul hp hg) hw
    _ = 2 ^ (BoundedCriticalSampleFiberPencilBounds.bits F (hashContext (pairFst e)) + (pointCode (pairFst e)).length) +
        2 ^ BoundedCriticalSampleFiberPencilBounds.bits F (hashContext (pairFst e)) := by rw [pow_add]; ring
    _ ≤ 2 ^ (BoundedCriticalSampleFiberPencilBounds.bits F (hashContext (pairFst e)) + (pointCode (pairFst e)).length) +
        2 ^ (BoundedCriticalSampleFiberPencilBounds.bits F (hashContext (pairFst e)) + (pointCode (pairFst e)).length) :=
      Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)) _
    _ = 2 ^ bits F (pairFst e) := by rw [bits, pow_succ]; omega

theorem linear_bound (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (e : List Bool) : (linear P F unit e).natAbs ≤ 2 ^ bits F (pairFst e) := by
  cases unit with
  | true =>
    exact (gram_bound P F e).trans (Nat.pow_le_pow_right (by decide) (by unfold bits; omega))
  | false =>
    have H := BoundedCriticalSampleFiberFeatureMoments.moment_bound P F (featureQuery e)
    have hc : BoundedCriticalSampleSlice.context (pairFst (featureQuery e)) =
        BoundedCriticalSampleSlice.context (BoundedCriticalSampleFiberWeightedMoments.original (hashContext (pairFst e))) := by
      simp only [featureQuery, pairFst_pair]
    rw [hc] at H
    exact (H.trans (Nat.lt_size_self _).le).trans (Nat.pow_le_pow_right (by decide) (by unfold bits BoundedCriticalSampleFiberPencilBounds.bits; omega))

theorem entry_mass (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (z : List Bool) (i j : Fin (dimension z)) :
    coefficientMass (matrix P F unit z i j) ≤ 2 ^ (bits F z + 1) := by
  let e := pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hc := constant_bound P F e
  have hl := linear_bound P F unit e
  have he : pairFst e = z := pairFst_pair _ _
  rw [he] at hc hl
  have hx : coefficientMass (X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
  change coefficientMass (C (constant P F e) + C (linear P F unit e) * X) ≤ _
  calc
    _ ≤ coefficientMass (C (constant P F e)) + coefficientMass (C (linear P F unit e) * X) := coefficientMass_add_le _ _
    _ ≤ coefficientMass (C (constant P F e)) + coefficientMass (C (linear P F unit e)) * coefficientMass X :=
      Nat.add_le_add_left (coefficientMass_mul_le _ _) _
    _ = (constant P F e).natAbs + (linear P F unit e).natAbs := by rw [coefficientMass_C, coefficientMass_C, hx, Nat.mul_one]
    _ ≤ 2 ^ bits F z + 2 ^ bits F z := Nat.add_le_add hc hl
    _ = 2 ^ (bits F z + 1) := by rw [pow_succ]; omega

theorem determinant_bits (P : Readers) (F : BoundedAlgebraicSlice.Family) (unit : Bool) (z : List Bool) (k : ℕ) :
    ((matrix P F unit z).det.coeff k).natAbs.size ≤ budget F z := by
  have hd := det_coefficientMass_le_pow (matrix P F unit z) (bits F z + 1) (entry_mass P F unit z)
  have hc := (coeff_natAbs_le_coefficientMass (matrix P F unit z).det k).trans hd
  have hs := Nat.size_le_size hc
  simpa only [Fintype.card_fin, Nat.size_pow, budget, CharacteristicIntegerBounds.budget] using hs

end LeanCanny.Encoding.BoundedCriticalSampleFiberProbeBounds
