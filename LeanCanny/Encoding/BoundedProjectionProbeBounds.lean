/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionProbeEntries

/-! # Uniform coefficient budgets for pointwise signature probes -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionProbeBounds
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedProjectionProbeEntries
open scoped Classical

noncomputable def bits (P : Readers) (z : List Bool) : ℕ :=
  BoundedProjectionPencilBounds.bits P (hashContext z) + (pointCode z).length + 1
theorem bits_unary {P : Readers} (h : P.PolyTime) : UnaryFn (bits P) :=
  (((BoundedProjectionPencilBounds.bits_unary h).comp hashContext_FP).add (UnaryFn.length pointCode_FP)).add (UnaryFn.const 1)

noncomputable def budget (P : Readers) (z : List Bool) : ℕ := CharacteristicIntegerBounds.budget (dimension z) (bits P z)
theorem budget_binary {P : Readers} (h : P.PolyTime) : BinaryFn (budget P) :=
  CharacteristicIntegerBounds.budget_binary dimension_binary (BinaryFn.ofUnary (bits_unary h))

theorem gram_bound (P : Readers) (e : List Bool) : (gram P e).natAbs ≤
    2 ^ BoundedProjectionPencilBounds.bits P (hashContext (pairFst e)) := by
  have H := BoundedProjectionBasisGram.entry_bounds P (BoundedProjectionPencilEntries.gramQuery (entryQuery e))
  have hc : pairFst (BoundedProjectionPencilEntries.gramQuery (entryQuery e)) =
      BoundedProjectionWeightedMoments.original (hashContext (pairFst e)) := by
    simp only [BoundedProjectionPencilEntries.gramQuery, entryQuery, pairFst_pair]
  rw [hc] at H
  have hb : (gram P e).natAbs ≤ 2 ^ BoundedCriticalProjection.labelWidth P
      (BoundedProjectionWeightedMoments.original (hashContext (pairFst e))) := by
    change (BoundedProjectionBasisGram.entry P (BoundedProjectionPencilEntries.gramQuery (entryQuery e))).natAbs ≤ _
    omega
  exact hb.trans (Nat.pow_le_pow_right (by decide) (by unfold BoundedProjectionPencilBounds.bits; omega))

theorem weighted_bound (P : Readers) (e : List Bool) : (weighted P e).natAbs ≤
    2 ^ BoundedProjectionPencilBounds.bits P (hashContext (pairFst e)) := by
  have H := BoundedProjectionWeightedMoments.entry_bits P (entryQuery e)
  have hb : BoundedProjectionWeightedMoments.entryBits P (entryQuery e) =
      BoundedProjectionPencilBounds.bits P (hashContext (pairFst e)) := by
    simp only [BoundedProjectionWeightedMoments.entryBits, entryQuery, pairFst_pair, BoundedProjectionPencilBounds.bits]
  rw [hb] at H
  exact (Nat.size_le.mp H).le

theorem constant_bound (P : Readers) (e : List Bool) : (constant P e).natAbs ≤ 2 ^ bits P (pairFst e) := by
  have hp := (SignedIntegerArithmetic.value_bound (pointCode (pairFst e))).le
  have hg := gram_bound P e
  have hw := weighted_bound P e
  have H := Int.natAbs_sub_le (pointValue (pairFst e) * gram P e) (weighted P e)
  rw [Int.natAbs_mul] at H
  apply H.trans
  calc
    (pointValue (pairFst e)).natAbs * (gram P e).natAbs + (weighted P e).natAbs ≤
        2 ^ (pointCode (pairFst e)).length * 2 ^ BoundedProjectionPencilBounds.bits P (hashContext (pairFst e)) +
          2 ^ BoundedProjectionPencilBounds.bits P (hashContext (pairFst e)) :=
      Nat.add_le_add (Nat.mul_le_mul hp hg) hw
    _ = 2 ^ (BoundedProjectionPencilBounds.bits P (hashContext (pairFst e)) + (pointCode (pairFst e)).length) +
        2 ^ BoundedProjectionPencilBounds.bits P (hashContext (pairFst e)) := by rw [pow_add]; ring
    _ ≤ 2 ^ (BoundedProjectionPencilBounds.bits P (hashContext (pairFst e)) + (pointCode (pairFst e)).length) +
        2 ^ (BoundedProjectionPencilBounds.bits P (hashContext (pairFst e)) + (pointCode (pairFst e)).length) :=
      Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)) _
    _ = 2 ^ bits P (pairFst e) := by rw [bits, pow_succ]; omega

theorem linear_bound (P : Readers) (unit : Bool) (e : List Bool) : (linear P unit e).natAbs ≤ 2 ^ bits P (pairFst e) := by
  cases unit with
  | true =>
    exact (gram_bound P e).trans (Nat.pow_le_pow_right (by decide) (by unfold bits; omega))
  | false =>
    have H := BoundedProjectionFeatureMoments.moment_bound P (featureQuery e)
    have hc : pairFst (featureQuery e) = BoundedProjectionWeightedMoments.original (hashContext (pairFst e)) := by
      simp only [featureQuery, pairFst_pair]
    rw [hc] at H
    exact H.trans (Nat.pow_le_pow_right (by decide) (by unfold bits BoundedProjectionPencilBounds.bits; omega))

theorem entry_mass (P : Readers) (unit : Bool) (z : List Bool) (i j : Fin (dimension z)) :
    coefficientMass (matrix P unit z i j) ≤ 2 ^ (bits P z + 1) := by
  let e := pair z (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hc := constant_bound P e
  have hl := linear_bound P unit e
  have he : pairFst e = z := pairFst_pair _ _
  rw [he] at hc hl
  have hx : coefficientMass (X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
  change coefficientMass (C (constant P e) + C (linear P unit e) * X) ≤ _
  calc
    _ ≤ coefficientMass (C (constant P e)) + coefficientMass (C (linear P unit e) * X) := coefficientMass_add_le _ _
    _ ≤ coefficientMass (C (constant P e)) + coefficientMass (C (linear P unit e)) * coefficientMass X :=
      Nat.add_le_add_left (coefficientMass_mul_le _ _) _
    _ = (constant P e).natAbs + (linear P unit e).natAbs := by rw [coefficientMass_C, coefficientMass_C, hx, Nat.mul_one]
    _ ≤ 2 ^ bits P z + 2 ^ bits P z := Nat.add_le_add hc hl
    _ = 2 ^ (bits P z + 1) := by rw [pow_succ]; omega

theorem determinant_bits (P : Readers) (unit : Bool) (z : List Bool) (k : ℕ) :
    ((matrix P unit z).det.coeff k).natAbs.size ≤ budget P z := by
  have hd := det_coefficientMass_le_pow (matrix P unit z) (bits P z + 1) (entry_mass P unit z)
  have hc := (coeff_natAbs_le_coefficientMass (matrix P unit z).det k).trans hd
  have hs := Nat.size_le_size hc
  simpa only [Fintype.card_fin, Nat.size_pow, budget, CharacteristicIntegerBounds.budget] using hs

end LeanCanny.Encoding.BoundedProjectionProbeBounds
