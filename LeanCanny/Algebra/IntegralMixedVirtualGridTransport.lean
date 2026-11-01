/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualGridModel
public import LeanCanny.Algebra.IntegralMixedVirtualCaps
public import LeanCanny.Algebra.IntegralCriticalActualMaskSnapshot
/-! # Actual virtual grid-index children and their finite exponent masks -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualGridBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualMonomialBits
set_option backward.isDefEq.respectTransparency false

noncomputable def maskAt (F : Family) (key : List Bool) (e k : ℕ) : Prop :=
  let S := (IntegralMixedVirtualSnapshotBits.sourceAt F key 0 0 0 0 0 1 (by decide)).toEuler
  ∀ i < S.free [], FixedWidthPolynomial.entry (S.sourceWidth []) k (S.offset [] + i) =
    FixedWidthPolynomial.entry (S.targetWidth []) e i

theorem mask_snapshot (P : Parameters) (F : Family) (q : List Bool) (k : ℕ) :
    ClearedCoordinateExponentBits.mask
      (IntegralClearedCoefficientBits.maskLayout
        (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)))
      (pair q (BinaryNatCode.encode k)) ↔ maskAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .target q) k := by
  rw [IntegralClearedCoefficientBits.mask_packet]
  rfl

theorem maskAt_congr (F : Family) (key key' : List Bool) (e k e' k' : ℕ)
    (hkey : key = key') (he : e = e') (hk : k = k') : maskAt F key e k ↔ maskAt F key' e' k' := by
  subst key'; subst e'; subst k'
  rfl

theorem saved_writer (P : Parameters) (p : Phase) (z : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (IntegralCriticalFlatGridBits.writer P p z) = IntegralMixedVirtualTaskBits.saved P (pairFst z) :=
  IntegralMixedVirtualTaskBits.saved_invariance P _ _ (IntegralCriticalFlatGridBits.writer_root P p z)
    (IntegralCriticalFlatGridBits.writer_birth P p z) (IntegralCriticalFlatGridBits.writer_other P p z .slot15 (by decide))

theorem index_writer (P : Parameters) (p : Phase) (z : List Bool)
    (hk : Nat.fromBitsLE (pairSnd z) ≤ numericCap P (RankedHistoryTask.root (pairFst z))) :
    get P .sourceIndex (IntegralCriticalFlatGridBits.writer P p z) = Nat.fromBitsLE (pairSnd z) := by
  rw [IntegralCriticalFlatGridBits.writer_get]
  simp only [ite_true]
  exact min_eq_left hk

theorem snapshot_writer (P : Parameters) (F : Family) (p : Phase) (z : List Bool)
    (hk : Nat.fromBitsLE (pairSnd z) ≤ numericCap P (RankedHistoryTask.root (pairFst z))) :
    snapshot P F (IntegralCriticalFlatGridBits.writer P p z) = packetSnapshot P F z := by
  apply monomialAt_congr
  · exact saved_writer P p z
  · exact IntegralCriticalFlatGridBits.writer_other P p z .expression (by decide)
  · exact IntegralCriticalFlatGridBits.writer_other P p z .derivative (by decide)
  · exact index_writer P p z hk
  · exact IntegralCriticalFlatGridBits.writer_other P p z .row (by decide)
  · exact IntegralCriticalFlatGridBits.writer_other P p z .col (by decide)
  · exact IntegralCriticalFlatGridBits.writer_modulus P p z

theorem product_child (P : Parameters) (F : Family) (p : Phase) (z : List Bool)
    (hk : Nat.fromBitsLE (pairSnd z) ≤ numericCap P (RankedHistoryTask.root (pairFst z))) :
    product P F (IntegralCriticalFlatGridBits.writer P p z) =
      (IntegralClearedCoefficientBits.termSource
        (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F))).value z := by
  unfold product
  rw [← IntegralMonomialTermBits.snapshot_value, source_snapshot, snapshot_writer P F p z hk]
  rw [← term_snapshot, IntegralMonomialTermBits.snapshot_value]
theorem term_product_child (P : Parameters) (F : Family) (q : List Bool) :
    product P F (IntegralCriticalFlatGridBits.writer P .productPower (IntegralCriticalFlatGridBits.termInput P q)) =
      (IntegralClearedCoefficientBits.termSource
        (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F))).value
        (IntegralCriticalFlatGridBits.termInput P q) := by
  apply product_child
  simp only [IntegralCriticalFlatGridBits.termInput, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact IntegralCriticalHistoryTask.get_le P .sourceIndex q

theorem term_value (P : Parameters) (F : Family) (q : List Bool) :
    (IntegralCriticalFlatGenericGridBits.termProgram P (IntegralMixedVirtualTaskBits.arithmetic P F)).value
      (product P F) (IntegralCriticalFlatGridBits.termInput P q) = term P F q := by
  exact IntegralCriticalFlatGenericGridBits.term_value_at P (IntegralMixedVirtualTaskBits.arithmetic P F)
    (product P F) q (fun _ => term_product_child P F q)


theorem mask_writer (P : Parameters) (F : Family) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) (k : ℕ)
    (hk : k ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root q)) :
    ClearedCoordinateExponentBits.mask
      (IntegralClearedCoefficientBits.maskLayout
        (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)))
      (IntegralCriticalFlatGridBits.termInput P
        (IntegralCriticalFlatGridBits.writer P phase (pair q (BinaryNatCode.encode k)))) ↔
    ClearedCoordinateExponentBits.mask
      (IntegralClearedCoefficientBits.maskLayout
        (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F)))
      (pair q (BinaryNatCode.encode k)) := by
  unfold IntegralCriticalFlatGridBits.termInput
  rw [mask_snapshot, mask_snapshot]
  apply maskAt_congr
  · simpa only [pairFst_pair] using saved_writer P phase (pair q (BinaryNatCode.encode k))
  · simpa only [pairFst_pair] using IntegralCriticalFlatGridBits.writer_other P phase
      (pair q (BinaryNatCode.encode k)) .target (by decide)
  · exact IntegralCriticalFlatGridBits.writer_index P phase q k hk

theorem term_child (P : Parameters) (F : Family) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) (k : ℕ)
    (hk : k ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root q)) :
    term P F (IntegralCriticalFlatGridBits.writer P phase (pair q (BinaryNatCode.encode k))) =
      IntegralClearedCoefficientBits.maskedProgram
        (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F))
        (pair q (BinaryNatCode.encode k)) := by
  rw [term_as_product]
  have HM := mask_writer P F phase q k hk
  have HC : Nat.fromBitsLE (pairSnd (pair q (BinaryNatCode.encode k))) ≤
      IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root (pairFst (pair q (BinaryNatCode.encode k)))) := by
    simpa only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hk
  rw [product_child P F phase _ HC]
  simp only [HM, IntegralClearedCoefficientBits.maskedProgram]

theorem grid_child (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) (_hv : IntegralMixedVirtualCaps.valid P q) (k : ℕ)
    (hk : k < IntegralCriticalFlatGenericGridBits.budget P (IntegralMixedVirtualTaskBits.arithmetic P F) q) :
    term P F (IntegralCriticalFlatGridBits.writer P .originalGridTerm (pair q (BinaryNatCode.encode k))) =
      IntegralClearedCoefficientBits.maskedProgram
        (IntegralCriticalFlatGenericGridBits.source P (IntegralMixedVirtualTaskBits.arithmetic P F))
        (pair q (BinaryNatCode.encode k)) :=
  term_child P F .originalGridTerm q k (hk.le.trans (IntegralMixedVirtualCaps.source_grid_cap P F g q))

theorem grid_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    (IntegralCriticalFlatGenericGridBits.program P (IntegralMixedVirtualTaskBits.arithmetic P F)).value
      (term P F) q = IntegralMixedVirtualSpatialBits.cleared P F q :=
  IntegralCriticalFlatGenericGridBits.value_at P (IntegralMixedVirtualTaskBits.arithmetic P F) (term P F) q
    (grid_child P F g q hv)

end LeanCanny.Algebra.IntegralMixedVirtualGridBits
