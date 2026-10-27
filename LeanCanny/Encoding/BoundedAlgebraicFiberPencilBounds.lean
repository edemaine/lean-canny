/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberPencilCoefficient

/-! # Uniform degree and coefficient budgets for weighted Gram determinants

All bounds apply to arbitrary context words. The binary dimension comes
from the count field. Polynomial entry lengths follow from the source label
width and the lengths of the count and modulus fields.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberPencilBounds
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicFiberWeightedMoments BoundedAlgebraicFiberPencilEntries
open scoped Classical

noncomputable def bits (F : BoundedAlgebraicSlice.Family) (b : List Bool) : ℕ :=
  (count b).length + (F.degree (pairFst (original b))).size + (modulus b).length
theorem bits_unary {F : BoundedAlgebraicSlice.Family} (A : F.Access) : UnaryFn (bits F) := by
  have hs : (fun b => pairFst (original b)) ∈ FP := mem_FP_comp original_FP pairFst_mem_FP
  exact ((UnaryFn.length count_FP).add ((BoundedAlgebraicFiberRecords.size_unary A).comp hs)).add
    (UnaryFn.length modulus_FP)

noncomputable def budget (F : BoundedAlgebraicSlice.Family) (b : List Bool) : ℕ :=
  CharacteristicIntegerBounds.budget (dimension b) (bits F b)
theorem budget_binary {F : BoundedAlgebraicSlice.Family} (A : F.Access) : BinaryFn (budget F) :=
  CharacteristicIntegerBounds.budget_binary dimension_binary (BinaryFn.ofUnary (bits_unary A))

theorem entry_mass (P : Readers) (F : BoundedAlgebraicSlice.Family) (b : List Bool) (i j : Fin (dimension b)) :
    coefficientMass (matrix P F b i j) ≤ 2 ^ (bits F b + 1) := by
  let q := pair b (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hg := BoundedAlgebraicFiberBasisGram.entry_bound P F (gramQuery q)
  have hc : pairFst (pairFst (gramQuery q)) = pairFst (original b) := by simp only [gramQuery, q, pairFst_pair]
  rw [hc] at hg
  have hg' : (gram P F q).natAbs ≤ 2 ^ bits F b := by
    have hl : (gram P F q).natAbs ≤ 2 ^ (F.degree (pairFst (original b))).size := by
      change (BoundedAlgebraicFiberBasisGram.entry P F (gramQuery q)).natAbs ≤ _
      exact hg.trans (Nat.lt_size_self _).le
    exact hl.trans (Nat.pow_le_pow_right (by decide) (by unfold bits; omega))
  have hh := BoundedAlgebraicFiberWeightedMoments.entry_bits P F q
  have he : BoundedAlgebraicFiberWeightedMoments.entryBits F q = bits F b := by
    simp only [BoundedAlgebraicFiberWeightedMoments.entryBits, q, pairFst_pair, bits]
  rw [he] at hh
  have hh' := (Nat.size_le.mp hh).le
  have hx : coefficientMass (X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
  change coefficientMass (C (gram P F q) * X - C (entry P F q)) ≤ _
  calc
    _ ≤ coefficientMass (C (gram P F q) * X) + coefficientMass (C (entry P F q)) := coefficientMass_sub_le _ _
    _ ≤ coefficientMass (C (gram P F q)) * coefficientMass X + coefficientMass (C (entry P F q)) :=
      Nat.add_le_add_right (coefficientMass_mul_le _ _) _
    _ = (gram P F q).natAbs + (entry P F q).natAbs := by rw [coefficientMass_C, coefficientMass_C, hx, Nat.mul_one]
    _ ≤ 2 ^ bits F b + 2 ^ bits F b := Nat.add_le_add hg' hh'
    _ = 2 ^ (bits F b + 1) := by rw [pow_succ]; omega

theorem determinant_bits (P : Readers) (F : BoundedAlgebraicSlice.Family) (b : List Bool) (k : ℕ) :
    ((matrix P F b).det.coeff k).natAbs.size ≤ budget F b := by
  have hd := det_coefficientMass_le_pow (matrix P F b) (bits F b + 1) (entry_mass P F b)
  have hc := (coeff_natAbs_le_coefficientMass (matrix P F b).det k).trans hd
  have hs := Nat.size_le_size hc
  simpa only [Fintype.card_fin, Nat.size_pow, budget, CharacteristicIntegerBounds.budget] using hs

theorem determinant_degree (P : Readers) (F : BoundedAlgebraicSlice.Family) (b : List Bool) : (matrix P F b).det.natDegree ≤ dimension b := by
  have H := det_natDegree_le (matrix P F b) (fun _ => 1) (entry_degree P F b)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] using H

end LeanCanny.Encoding.BoundedAlgebraicFiberPencilBounds
