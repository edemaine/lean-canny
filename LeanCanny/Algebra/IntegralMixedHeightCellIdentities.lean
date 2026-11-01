/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightIntegerModel
public import LeanCanny.Algebra.IntegralMixedHeightNaturalEntries
/-! # Literal affine cell identities and the actual integer height factors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightCellIdentities
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedHeightCellsBits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem affine_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    affine P D q = (rule P D (IntegralMixedVirtualTaskBits.saved P q)).heights i := by
  have HB : get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1 := hi ▸ i.isLt
  rw [affine, dite_eq_left HB]
  apply congrArg (rule P D (IntegralMixedVirtualTaskBits.saved P q)).heights
  exact Fin.ext hi.symm

theorem constant_cell (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    cell P D q 0 0 = IntegralMixedAffineCoefficients.constantCoefficient ((rule P D (IntegralMixedVirtualTaskBits.saved P q)).heights i) := by
  rw [cell, ite_eq_left rfl, affine_eq P D q i hi]

theorem reference_cell (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) (j : ℕ) :
    cell P D q 1 j = IntegralMixedAffineCoefficients.referenceCoefficient ((rule P D (IntegralMixedVirtualTaskBits.saved P q)).heights i) j := by
  simp only [cell, Nat.reduceEqDiff, ite_false, ite_true]
  rw [affine_eq P D q i hi]

theorem scale_cell (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (j : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) :
    cell P D q 2 j.val = (rule P D (IntegralMixedVirtualTaskBits.saved P q)).scales j := by
  simp only [cell, Nat.reduceEqDiff, ite_false, ite_true, dite_eq_left j.isLt]

theorem scales_original (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    IntegralMixedHeightIntegerBits.scales P D q = IntegralMixedHeightCofactor.original (rule P D (IntegralMixedVirtualTaskBits.saved P q)) i := by
  have HN := congrArg (fun r => P.ambient r + 1) (IntegralMixedFullHistoryFamilyBits.saved_root P q).symm
  unfold IntegralMixedHeightIntegerBits.scales
  rw [HN, ← hi, CommonHeightBits.cofactor_eq_erase]
  unfold CommonIntegerDenominator.denominator IntegralMixedHeightCofactor.original
  apply Finset.prod_congr rfl
  intro j _
  exact scale_cell P D q j

theorem factor_cofactor (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    IntegralMixedHeightIntegerBits.factor P D q = IntegralMixedHeightCofactor.value (IntegralMixedOldHeightBits.state P D q)
      (rule P D (IntegralMixedVirtualTaskBits.saved P q)) i := by
  rw [IntegralMixedHeightIntegerBits.factor, scales_original P D q i hi]
  unfold IntegralMixedHeightCofactor.value IntegralMixedHeightIntegerBits.bank
  rw [← IntegralMixedFullHistoryFamilyBits.saved_root P q]
  rfl

theorem references_entry (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    IntegralMixedHeightIntegerBits.references P D q =
      ∑ j : Fin ((IntegralMixedOldHeightBits.bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q)),
        IntegralMixedAffineCoefficients.referenceCoefficient ((rule P D (IntegralMixedVirtualTaskBits.saved P q)).heights i) j.val *
          Algebra.leftMulMatrix (IntegralMixedOldHeightBits.state P D q).sampler.scalarPrefix.basis.finBasis
            (cleared (IntegralMixedOldHeightBits.state P D q) j) (IntegralMixedHeightTableMatrixBits.row P D q) (IntegralMixedHeightTableMatrixBits.col P D q) := by
  unfold IntegralMixedHeightIntegerBits.references
  rw [← IntegralMixedOldHeightBits.bank_birth P D q, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [reference_cell P D q i hi j.val, IntegralMixedHeightTableMatrixBits.matrix_entry P D q j]

theorem constant_entry (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    IntegralMixedHeightIntegerBits.constant P D q = IntegralMixedAffineCoefficients.constantCoefficient
      ((rule P D (IntegralMixedVirtualTaskBits.saved P q)).heights i) *
        (if IntegralMixedHeightTableMatrixBits.row P D q = IntegralMixedHeightTableMatrixBits.col P D q then 1 else 0) := by
  rw [IntegralMixedHeightIntegerBits.constant, constant_cell P D q i hi]
  by_cases HE : IntegralMixedHeightTableMatrixBits.row P D q = IntegralMixedHeightTableMatrixBits.col P D q
  · have HN : IntegralMixedHeightTableQueryBits.oldRow P q = IntegralMixedHeightTableQueryBits.oldCol P q := congrArg Fin.val HE
    rw [ite_eq_left HE, ite_eq_left HN, mul_one]
  · have HN : IntegralMixedHeightTableQueryBits.oldRow P q ≠ IntegralMixedHeightTableQueryBits.oldCol P q :=
      fun H => HE (Fin.ext H)
    rw [ite_eq_right HE, ite_eq_right HN, mul_zero]

theorem affine_entry (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    IntegralMixedHeightIntegerBits.affine P D q = IntegralMixedHeightMatrix.affineEntry (IntegralMixedOldHeightBits.state P D q)
      ((rule P D (IntegralMixedVirtualTaskBits.saved P q)).heights i)
      (IntegralMixedHeightTableMatrixBits.row P D q) (IntegralMixedHeightTableMatrixBits.col P D q) := by
  rw [IntegralMixedHeightIntegerBits.affine, references_entry P D q i hi, constant_entry P D q i hi]
  unfold IntegralMixedHeightMatrix.affineEntry IntegralMixedHeightIntegerBits.bank
  ring

theorem slope_cell (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    cell P D q 3 0 = if i = ((IntegralMixedFullHistoryFamilyBits.family P D).rule (IntegralMixedVirtualTaskBits.saved P q)).height then
      ((IntegralMixedFullHistoryFamilyBits.family P D).rule (IntegralMixedVirtualTaskBits.saved P q)).slope else 0 := by
  simp only [cell, Nat.reduceEqDiff, ite_false, ite_true]
  rw [← hi]
  simp only [Fin.ext_iff]

end LeanCanny.Algebra.IntegralMixedHeightCellIdentities
