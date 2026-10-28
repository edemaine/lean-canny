/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildPencilCoefficient

/-! # Uniform degree and coefficient budgets for weighted Gram determinants

All bounds apply to arbitrary context words. The binary dimension comes
from the count field. Polynomial entry lengths follow from the source label
width and the lengths of the count and modulus fields.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildPencilBounds
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleChildWeightedMoments BoundedCriticalSampleChildPencilEntries
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildRecords.length BoundedCriticalSampleChildThom.labelWidth
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight
  BoundedCriticalSampleChildQueries.roots BoundedCriticalSampleChildRegularCount.count

noncomputable def bits (P : Inputs) (b : List Bool) : ℕ :=
  (count b).length + BoundedCriticalSampleChildThom.labelWidth P (original b) + (modulus b).length
theorem bits_unary {P : Inputs} (h : P.PolyTime) : UnaryFn (bits P) :=
  ((UnaryFn.length count_FP).add ((BoundedCriticalSampleChildThom.labelWidth_unary h).comp original_FP)).add
    (UnaryFn.length modulus_FP)

noncomputable def budget (P : Inputs) (b : List Bool) : ℕ := CharacteristicIntegerBounds.budget (dimension b) (bits P b)
theorem budget_binary {P : Inputs} (h : P.PolyTime) : BinaryFn (budget P) :=
  CharacteristicIntegerBounds.budget_binary dimension_binary (BinaryFn.ofUnary (bits_unary h))

theorem entry_mass (P : Inputs) (b : List Bool) (i j : Fin (dimension b)) :
    coefficientMass (matrix P b i j) ≤ 2 ^ (bits P b + 1) := by
  let q := pair b (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hg := BoundedCriticalSampleChildBasisGram.entry_bounds P (gramQuery q)
  have hc : pairFst (gramQuery q) = original b := by simp only [gramQuery, q, pairFst_pair]
  rw [hc] at hg
  have hg' : (gram P q).natAbs ≤ 2 ^ bits P b := by
    have hl : (gram P q).natAbs ≤ 2 ^ BoundedCriticalSampleChildThom.labelWidth P (original b) := by
      change (BoundedCriticalSampleChildBasisGram.entry P (gramQuery q)).natAbs ≤ _
      omega
    exact hl.trans (Nat.pow_le_pow_right (by decide) (by unfold bits; omega))
  have hh := BoundedCriticalSampleChildWeightedMoments.entry_bits P q
  have he : BoundedCriticalSampleChildWeightedMoments.entryBits P q = bits P b := by
    simp only [BoundedCriticalSampleChildWeightedMoments.entryBits, q, pairFst_pair, bits]
  rw [he] at hh
  have hh' := (Nat.size_le.mp hh).le
  have hx : coefficientMass (X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
  change coefficientMass (C (gram P q) * X - C (entry P q)) ≤ _
  calc
    _ ≤ coefficientMass (C (gram P q) * X) + coefficientMass (C (entry P q)) := coefficientMass_sub_le _ _
    _ ≤ coefficientMass (C (gram P q)) * coefficientMass X + coefficientMass (C (entry P q)) :=
      Nat.add_le_add_right (coefficientMass_mul_le _ _) _
    _ = (gram P q).natAbs + (entry P q).natAbs := by rw [coefficientMass_C, coefficientMass_C, hx, Nat.mul_one]
    _ ≤ 2 ^ bits P b + 2 ^ bits P b := Nat.add_le_add hg' hh'
    _ = 2 ^ (bits P b + 1) := by rw [pow_succ]; omega

theorem determinant_bits (P : Inputs) (b : List Bool) (k : ℕ) :
    ((matrix P b).det.coeff k).natAbs.size ≤ budget P b := by
  have hd := det_coefficientMass_le_pow (matrix P b) (bits P b + 1) (entry_mass P b)
  have hc := (coeff_natAbs_le_coefficientMass (matrix P b).det k).trans hd
  have hs := Nat.size_le_size hc
  simpa only [Fintype.card_fin, Nat.size_pow, budget, CharacteristicIntegerBounds.budget] using hs

theorem determinant_degree (P : Inputs) (b : List Bool) : (matrix P b).det.natDegree ≤ dimension b := by
  have H := det_natDegree_le (matrix P b) (fun _ => 1) (entry_degree P b)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] using H

end LeanCanny.Encoding.BoundedCriticalSampleChildPencilBounds
