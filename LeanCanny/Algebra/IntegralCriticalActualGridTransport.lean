/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualMonomialSnapshot
public import LeanCanny.Algebra.IntegralCriticalActualMaskSnapshot
/-! # Actual original-grid and product replies under flat index writers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualGridTransport
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualMonomialSnapshot
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap
attribute [local irreducible] IntegralCriticalFlatGridBits.writer

noncomputable def product (F : Scripts) (q : List Bool) := (IntegralCriticalFlatActualLow.source F).value q
noncomputable def term (F : Scripts) (q : List Bool) :=
  IntegralClearedCoefficientBits.maskedProgram
    (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F))
    (IntegralCriticalFlatGridBits.termInput F.toParameters q)

theorem creator_writer (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool) :
    IntegralCriticalTotalCreatingBits.atFamily F (IntegralCriticalFlatGridBits.writer F.toParameters phase p) =
      IntegralCriticalTotalCreatingBits.atFamily F (pairFst p) := by
  apply IntegralCriticalTotalCreatingBits.atFamily_invariance
  · simpa only [root, IntegralCriticalFlatHeightBits.root] using
      IntegralCriticalFlatGridBits.writer_root F.toParameters phase p
  · exact IntegralCriticalFlatGridBits.writer_birth F.toParameters phase p

theorem index_writer (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool)
    (hk : Nat.fromBitsLE (pairSnd p) ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root (pairFst p))) :
    IntegralCriticalHistoryTask.get F.toParameters .sourceIndex (IntegralCriticalFlatGridBits.writer F.toParameters phase p) =
      Nat.fromBitsLE (pairSnd p) := by
  rw [IntegralCriticalFlatGridBits.writer_get]
  simp only [ite_true]
  exact min_eq_left hk

theorem snapshot_writer (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool)
    (hk : Nat.fromBitsLE (pairSnd p) ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root (pairFst p))) :
    snapshot F (IntegralCriticalFlatGridBits.writer F.toParameters phase p) = packetSnapshot F p := by
  apply monomialAt_congr
  · exact creator_writer F phase p
  · exact IntegralCriticalFlatGridBits.writer_other F.toParameters phase p .expression (by decide)
  · exact IntegralCriticalFlatGridBits.writer_other F.toParameters phase p .derivative (by decide)
  · exact index_writer F phase p hk
  · exact IntegralCriticalFlatGridBits.writer_other F.toParameters phase p .row (by decide)
  · exact IntegralCriticalFlatGridBits.writer_other F.toParameters phase p .col (by decide)
  · exact IntegralCriticalFlatGridBits.writer_modulus F.toParameters phase p

theorem product_child (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool)
    (hk : Nat.fromBitsLE (pairSnd p) ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root (pairFst p))) :
    product F (IntegralCriticalFlatGridBits.writer F.toParameters phase p) =
      (IntegralClearedCoefficientBits.termSource
        (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F))).value p := by
  unfold product
  rw [value_snapshot, snapshot_writer F phase p hk]
  exact (packet_value_snapshot F p).symm

theorem term_product_child (F : Scripts) (q : List Bool) :
    product F (IntegralCriticalFlatGridBits.writer F.toParameters .productPower (IntegralCriticalFlatGridBits.termInput F.toParameters q)) =
      (IntegralClearedCoefficientBits.termSource
        (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F))).value
        (IntegralCriticalFlatGridBits.termInput F.toParameters q) := by
  apply product_child
  simp only [IntegralCriticalFlatGridBits.termInput, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact IntegralCriticalHistoryTask.get_le F.toParameters .sourceIndex q

theorem term_value (F : Scripts) (q : List Bool) :
    (IntegralCriticalFlatGenericGridBits.termProgram F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).value
      (product F) (IntegralCriticalFlatGridBits.termInput F.toParameters q) = term F q := by
  exact IntegralCriticalFlatGenericGridBits.term_value_at F.toParameters (IntegralCriticalTotalCreatingBits.euler F)
    (product F) q (fun _ => term_product_child F q)


theorem term_as_product (F : Scripts) (q : List Bool) :
    term F q = if ClearedCoordinateExponentBits.mask
      (IntegralClearedCoefficientBits.maskLayout
        (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)))
      (IntegralCriticalFlatGridBits.termInput F.toParameters q) then product F q else [] := rfl

theorem mask_writer (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) (k : ℕ)
    (hk : k ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q)) :
    ClearedCoordinateExponentBits.mask
      (IntegralClearedCoefficientBits.maskLayout
        (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)))
      (IntegralCriticalFlatGridBits.termInput F.toParameters
        (IntegralCriticalFlatGridBits.writer F.toParameters phase (pair q (BinaryNatCode.encode k)))) ↔
    ClearedCoordinateExponentBits.mask
      (IntegralClearedCoefficientBits.maskLayout
        (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F)))
      (pair q (BinaryNatCode.encode k)) := by
  unfold IntegralCriticalFlatGridBits.termInput
  rw [IntegralCriticalActualMaskSnapshot.mask_snapshot, IntegralCriticalActualMaskSnapshot.mask_snapshot]
  apply IntegralCriticalActualMaskSnapshot.maskAt_congr
  · simpa only [pairFst_pair] using creator_writer F phase (pair q (BinaryNatCode.encode k))
  · simpa only [pairFst_pair] using IntegralCriticalFlatGridBits.writer_other F.toParameters phase
      (pair q (BinaryNatCode.encode k)) .target (by decide)
  · exact IntegralCriticalFlatGridBits.writer_index F.toParameters phase q k hk

theorem term_child (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) (k : ℕ)
    (hk : k ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q)) :
    term F (IntegralCriticalFlatGridBits.writer F.toParameters phase (pair q (BinaryNatCode.encode k))) =
      IntegralClearedCoefficientBits.maskedProgram
        (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F))
        (pair q (BinaryNatCode.encode k)) := by
  rw [term_as_product]
  have HM := mask_writer F phase q k hk
  have HC : Nat.fromBitsLE (pairSnd (pair q (BinaryNatCode.encode k))) ≤
      IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root (pairFst (pair q (BinaryNatCode.encode k)))) := by
    simpa only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hk
  rw [product_child F phase _ HC]
  simp only [HM, IntegralClearedCoefficientBits.maskedProgram]

theorem grid_child (F : Scripts) (q : List Bool) (hv : valid F q) (k : ℕ)
    (hk : k < IntegralCriticalFlatGenericGridBits.budget F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q) :
    term F (IntegralCriticalFlatGridBits.writer F.toParameters .originalGridTerm (pair q (BinaryNatCode.encode k))) =
      IntegralClearedCoefficientBits.maskedProgram
        (IntegralCriticalFlatGenericGridBits.source F.toParameters (IntegralCriticalTotalCreatingBits.euler F))
        (pair q (BinaryNatCode.encode k)) :=
  term_child F .originalGridTerm q k (hk.le.trans (IntegralCriticalActualCaps.original_grid_cap F q hv))

theorem grid_value (F : Scripts) (q : List Bool) (hv : valid F q) :
    (IntegralCriticalFlatGenericGridBits.program F.toParameters (IntegralCriticalTotalCreatingBits.euler F)).value
      (term F) q = IntegralCriticalActualSpatialTransport.cleared F q :=
  IntegralCriticalFlatGenericGridBits.value_at F.toParameters (IntegralCriticalTotalCreatingBits.euler F) (term F) q
    (grid_child F q hv)

end LeanCanny.Algebra.IntegralCriticalActualGridTransport
