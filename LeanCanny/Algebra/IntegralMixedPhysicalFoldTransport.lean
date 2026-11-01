/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalSpatialModel
public import LeanCanny.Algebra.IntegralMixedPhysicalCaps
public import LeanCanny.Algebra.IntegralCriticalFlatFrozenSum
/-! # Actual frozen and Euler summands under finite physical queries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalFoldBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalSnapshotBits
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev source (P : Parameters) (F : Family) := IntegralMixedPhysicalTaskBits.arithmetic P F

theorem arity_cap (P : Parameters) (F : Family) (h : IntegralMixedPhysicalCaps.RootGeometry P F) (q : List Bool) :
    (source P F).arity q ≤ numericCap P (RankedHistoryTask.root q) :=
  (Nat.add_le_add_right (h.ambient q) 1).trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1

theorem free_cap (P : Parameters) (F : Family) (h : IntegralMixedPhysicalCaps.RootGeometry P F) (q : List Bool) :
    (source P F).free q ≤ numericCap P (RankedHistoryTask.root q) := by
  have HF : (source P F).free q ≤ (source P F).arity q := by have H := (source P F).fit q; omega
  exact HF.trans (arity_cap P F h q)

theorem target_grid_cap (P : Parameters) (F : Family) (h : IntegralMixedPhysicalCaps.RootGeometry P F) (q : List Bool) :
    FixedWidthPolynomial.count ((source P F).free q) ((source P F).targetWidth q) ≤ numericCap P (RankedHistoryTask.root q) :=
  (IntegralMixedPhysicalCaps.dimension_le P F h q).trans (IntegralCriticalQueryBounds.spatial_grid_le _ _ _ _ _ _ _ _)

theorem family_coordinate (P : Parameters) (F : Family) (p : Phase) (q : List Bool) (i : ℕ) :
    family P F (IntegralCriticalFlatCoordinateQuery.writer P p (pair q (BinaryNatCode.encode i))) = family P F q := by
  apply family_invariance
  · simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_root P p (pair q (BinaryNatCode.encode i))
  · simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_birth P p (pair q (BinaryNatCode.encode i))
  · simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_other P p (pair q (BinaryNatCode.encode i)) .slot15 (by decide)
  · simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_other P p (pair q (BinaryNatCode.encode i)) .slot13 (by decide)
  · simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_other P p (pair q (BinaryNatCode.encode i)) .coefficient (by decide)
  · simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_other P p (pair q (BinaryNatCode.encode i)) .target (by decide)
  · simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_other P p (pair q (BinaryNatCode.encode i)) .row (by decide)
  · simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_other P p (pair q (BinaryNatCode.encode i)) .col (by decide)
  · simpa only [pairFst_pair] using IntegralCriticalFlatCoordinateQuery.writer_modulus P p (pair q (BinaryNatCode.encode i))

theorem frozenTerm_packet_eq (P : Parameters) (F : Family) (q : List Bool) (i : ℕ) :
    IntegralFrozenPowerBits.termProgram (eulerAt P F q).toGradient.toFrozen (pair [] (BinaryNatCode.encode i)) =
      IntegralFrozenPowerBits.termProgram (source P F).toGradient.toFrozen (pair q (BinaryNatCode.encode i)) := by
  rw [IntegralFrozenPowerBits.term_packet, IntegralFrozenPowerBits.term_packet]
  rfl

theorem frozenSum_child (P : Parameters) (F : Family) (q : List Bool) (i : ℕ)
    (hi : i ≤ numericCap P (RankedHistoryTask.root q)) :
    frozenTerm P F (IntegralCriticalFlatCoordinateQuery.writer P .frozenPowerTerm (pair q (BinaryNatCode.encode i))) =
      IntegralFrozenPowerBits.termProgram (source P F).toGradient.toFrozen (pair q (BinaryNatCode.encode i)) := by
  unfold frozenTerm eulerAt
  rw [family_coordinate, IntegralCriticalFlatCoordinateQuery.writer_coordinate P _ q i hi]
  exact frozenTerm_packet_eq P F q i

noncomputable def termIndex (A : IntegralClearedCriticalBits.Source) (j : ℕ) : Fin (A.free []) :=
  ⟨j % A.free [], Nat.mod_lt _ (A.toEuler.free_pos [])⟩
noncomputable def productAt (A : IntegralClearedCriticalBits.Source) (j : ℕ) :=
  IntegralEulerBits.termProgram A.toEuler (pair [] (BinaryNatCode.encode (termIndex A j).val))
noncomputable def product (P : Parameters) (F : Family) (q : List Bool) := productAt (family P F q) (get P .derivative q)

theorem product_eq_term (P : Parameters) (F : Family) (q : List Bool) :
    product P F q = IntegralEulerBits.termProgram (source P F)
      (pair q (BinaryNatCode.encode (IntegralCriticalFlatEulerRowsBits.selected P (source P F) q).val)) := by
  unfold product productAt
  rw [IntegralEulerBits.term_packet, IntegralEulerBits.term_packet]
  rfl

theorem productAt_packet (P : Parameters) (F : Family) (q : List Bool) (j : Fin ((source P F).free q)) :
    productAt (family P F q) j.val = IntegralEulerBits.termProgram (source P F) (pair q (BinaryNatCode.encode j.val)) := by
  unfold productAt
  rw [IntegralEulerBits.term_packet, IntegralEulerBits.term_packet]
  change residueBits ((source P F).summand q (j.val % (source P F).free q) : ZMod ((source P F).modulus q)) = _
  rw [Nat.mod_eq_of_lt j.isLt]

theorem family_spatial (P : Parameters) (F : Family) (p : Phase) (q : List Bool) (j : ℕ)
    (hj : j ≤ numericCap P (RankedHistoryTask.root q)) :
    family P F (IntegralCriticalFlatEulerRowsBits.spatial P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (get P .target q))))) = family P F q := by
  apply family_invariance
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_root P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (get P .target q))))
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_birth P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (get P .target q))))
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (get P .target q)))) .slot15 (by decide) (by decide) (by decide)
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (get P .target q)))) .slot13 (by decide) (by decide) (by decide)
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (get P .target q)))) .coefficient (by decide) (by decide) (by decide)
  · exact (IntegralCriticalFlatEulerRowsBits.spatial_fields P p 0 q j _ hj (get_le P .target q) (Nat.zero_le _)).2.1
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (get P .target q)))) .row (by decide) (by decide) (by decide)
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (get P .target q)))) .col (by decide) (by decide) (by decide)
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_modulus P p 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (get P .target q))))

theorem sum_child (P : Parameters) (F : Family) (h : IntegralMixedPhysicalCaps.RootGeometry P F)
    (q : List Bool) (j : ℕ) (hj : j < (source P F).free q) :
    product P F (IntegralCriticalFlatEulerRowsBits.sumTask P (source P F) (pair q (BinaryNatCode.encode j))) =
      IntegralEulerBits.termProgram (source P F) (pair q (BinaryNatCode.encode j)) := by
  have HC := hj.le.trans (free_cap P F h q)
  have HF := IntegralCriticalFlatEulerRowsBits.spatial_fields P .coordinateGradientProduct 0 q j
    (get P .target q) HC (get_le P .target q) (Nat.zero_le _)
  unfold product
  simp only [IntegralCriticalFlatEulerRowsBits.sumTask, IntegralEulerBits.termQuery, pairFst_pair, pairSnd_pair]
  have HT : (source P F).target q = get P .target q := rfl
  simp only [HT]
  rw [family_spatial P F .coordinateGradientProduct q j HC, HF.1]
  exact productAt_packet P F q ⟨j, hj⟩
end LeanCanny.Algebra.IntegralMixedPhysicalFoldBits
