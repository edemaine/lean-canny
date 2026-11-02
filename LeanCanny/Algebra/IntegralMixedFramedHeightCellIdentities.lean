/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightIntegerModel
public import LeanCanny.Algebra.IntegralMixedHeightNaturalEntries
/-! # Literal affine cell identities and the actual integer height factors -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightCellIdentities
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedScalarCellsBits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem affine_eq (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    affine P D J q = (rule P D J (IntegralMixedVirtualTaskBits.saved P q)).heights i := by
  have HB : get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1 := hi ▸ i.isLt
  rw [affine, dite_eq_left HB]
  apply congrArg (rule P D J (IntegralMixedVirtualTaskBits.saved P q)).heights
  exact Fin.ext hi.symm

theorem constant_cell (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    cell P D J q 0 0 = IntegralMixedAffineCoefficients.constantCoefficient ((rule P D J (IntegralMixedVirtualTaskBits.saved P q)).heights i) := by
  rw [cell, ite_eq_left rfl, affine_eq P D J q i hi]

theorem reference_cell (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) (j : ℕ) :
    cell P D J q 1 j = IntegralMixedAffineCoefficients.referenceCoefficient ((rule P D J (IntegralMixedVirtualTaskBits.saved P q)).heights i) j := by
  simp only [cell, Nat.reduceEqDiff, ite_false, ite_true]
  rw [affine_eq P D J q i hi]

theorem scale_cell (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (j : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) :
    cell P D J q 2 j.val = (rule P D J (IntegralMixedVirtualTaskBits.saved P q)).scales j := by
  simp only [cell, Nat.reduceEqDiff, ite_false, ite_true, dite_eq_left j.isLt]

theorem scales_original (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    IntegralMixedFramedHeightIntegerBits.scales P D J q = IntegralMixedHeightCofactor.original (rule P D J (IntegralMixedVirtualTaskBits.saved P q)) i := by
  have HN := congrArg (fun r => P.ambient r + 1) (IntegralMixedFullHistoryFamilyBits.saved_root P q).symm
  unfold IntegralMixedFramedHeightIntegerBits.scales
  rw [HN, ← hi, CommonHeightBits.cofactor_eq_erase]
  unfold CommonIntegerDenominator.denominator IntegralMixedHeightCofactor.original
  apply Finset.prod_congr rfl
  intro j _
  exact scale_cell P D J q j

theorem factor_cofactor (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    IntegralMixedFramedHeightIntegerBits.factor P D J q = IntegralMixedHeightCofactor.value (IntegralMixedFramedOldHeightBits.state P D J q)
      (rule P D J (IntegralMixedVirtualTaskBits.saved P q)) i := by
  rw [IntegralMixedFramedHeightIntegerBits.factor, scales_original P D J q i hi]
  unfold IntegralMixedHeightCofactor.value IntegralMixedFramedHeightIntegerBits.bank
  rw [← IntegralMixedFullHistoryFamilyBits.saved_root P q]
  rfl

theorem references_entry (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    IntegralMixedFramedHeightIntegerBits.references P D J q =
      ∑ j : Fin ((IntegralMixedFramedOldHeightBits.bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q)),
        IntegralMixedAffineCoefficients.referenceCoefficient ((rule P D J (IntegralMixedVirtualTaskBits.saved P q)).heights i) j.val *
          Algebra.leftMulMatrix (IntegralMixedFramedOldHeightBits.state P D J q).sampler.scalarPrefix.basis.finBasis
            (cleared (IntegralMixedFramedOldHeightBits.state P D J q) j) (IntegralMixedFramedHeightTableMatrixBits.row P D J q) (IntegralMixedFramedHeightTableMatrixBits.col P D J q) := by
  unfold IntegralMixedFramedHeightIntegerBits.references
  rw [← IntegralMixedFramedOldHeightBits.bank_birth P D J q, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [reference_cell P D J q i hi j.val, IntegralMixedFramedHeightTableMatrixBits.matrix_entry P D J q j]

theorem constant_entry (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    IntegralMixedFramedHeightIntegerBits.constant P D J q = IntegralMixedAffineCoefficients.constantCoefficient
      ((rule P D J (IntegralMixedVirtualTaskBits.saved P q)).heights i) *
        (if IntegralMixedFramedHeightTableMatrixBits.row P D J q = IntegralMixedFramedHeightTableMatrixBits.col P D J q then 1 else 0) := by
  rw [IntegralMixedFramedHeightIntegerBits.constant, constant_cell P D J q i hi]
  by_cases HE : IntegralMixedFramedHeightTableMatrixBits.row P D J q = IntegralMixedFramedHeightTableMatrixBits.col P D J q
  · have HN : IntegralMixedHeightTableQueryBits.oldRow P q = IntegralMixedHeightTableQueryBits.oldCol P q := congrArg Fin.val HE
    rw [ite_eq_left HE, ite_eq_left HN, mul_one]
  · have HN : IntegralMixedHeightTableQueryBits.oldRow P q ≠ IntegralMixedHeightTableQueryBits.oldCol P q :=
      fun H => HE (Fin.ext H)
    rw [ite_eq_right HE, ite_eq_right HN, mul_zero]

theorem affine_entry (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    IntegralMixedFramedHeightIntegerBits.affine P D J q = IntegralMixedHeightMatrix.affineEntry (IntegralMixedFramedOldHeightBits.state P D J q)
      ((rule P D J (IntegralMixedVirtualTaskBits.saved P q)).heights i)
      (IntegralMixedFramedHeightTableMatrixBits.row P D J q) (IntegralMixedFramedHeightTableMatrixBits.col P D J q) := by
  rw [IntegralMixedFramedHeightIntegerBits.affine, references_entry P D J q i hi, constant_entry P D J q i hi]
  unfold IntegralMixedHeightMatrix.affineEntry IntegralMixedFramedHeightIntegerBits.bank
  ring

theorem slope_cell (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q) :
    cell P D J q 3 0 = if i = ((IntegralMixedFramedHistoryFamilyBits.family P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).height then
      ((IntegralMixedFramedHistoryFamilyBits.family P D J).rule (IntegralMixedVirtualTaskBits.saved P q)).slope else 0 := by
  simp only [cell, Nat.reduceEqDiff, ite_false, ite_true]
  rw [← hi]
  simp only [Fin.ext_iff]

end LeanCanny.Algebra.IntegralMixedFramedHeightCellIdentities
