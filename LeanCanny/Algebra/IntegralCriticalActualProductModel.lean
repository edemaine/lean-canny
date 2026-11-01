/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualSpatialTransport
/-! # Actual coordinate-gradient summands under flat row queries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualProductModel
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualScalarModels
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap
attribute [local irreducible] IntegralCriticalFlatEulerRowsBits.spatial

noncomputable def productAt (A : IntegralHistoryCriticalBits.Family) (j : ℕ) :=
  IntegralEulerBits.termProgram (eulerAt A) (pair [] (BinaryNatCode.encode (selectedAt A j []).val))
noncomputable def product (F : Scripts) (q : List Bool) :=
  productAt (IntegralCriticalTotalSnapshotBits.family F q) (IntegralCriticalHistoryTask.get F.toParameters .derivative q)

theorem product_eq_term (F : Scripts) (q : List Bool) :
    product F q = IntegralEulerBits.termProgram (IntegralCriticalTotalCreatingBits.euler F)
      (pair q (BinaryNatCode.encode
        (IntegralCriticalFlatEulerRowsBits.selected F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q).val)) := by
  unfold product productAt
  rw [IntegralEulerBits.term_packet, IntegralEulerBits.term_packet]
  rfl

theorem product_eq (F : Scripts) (q : List Bool) :
    product F q = if IntegralCriticalFlatEulerRowsBits.selected F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q =
        (IntegralCriticalTotalCreatingBits.euler F).objective q then [] else
      IntegralCriticalCoordinateProductBits.value (IntegralCriticalTotalCreatingBits.euler F).toGradient
        (IntegralCriticalFlatEulerRowsBits.packet F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q) := by
  rw [product_eq_term]
  have HX : IntegralEulerBits.excluded (IntegralCriticalTotalCreatingBits.euler F)
      (pair q (BinaryNatCode.encode
        (IntegralCriticalFlatEulerRowsBits.selected F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q).val)) ↔
      IntegralCriticalFlatEulerRowsBits.selected F.toParameters (IntegralCriticalTotalCreatingBits.euler F) q =
        (IntegralCriticalTotalCreatingBits.euler F).objective q := by
    unfold IntegralEulerBits.excluded IntegralEulerBits.objectiveRank
    rw [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact Fin.ext_iff.symm
  unfold IntegralEulerBits.termProgram
  simp only [HX]
  simp only [IntegralEulerBits.termQuery, pairFst_pair, pairSnd_pair]
  rfl

theorem productAt_packet (F : Scripts) (q : List Bool)
    (j : Fin ((IntegralCriticalTotalCreatingBits.euler F).free q)) :
    productAt (IntegralCriticalTotalSnapshotBits.family F q) j.val =
      IntegralEulerBits.termProgram (IntegralCriticalTotalCreatingBits.euler F) (pair q (BinaryNatCode.encode j.val)) := by
  unfold productAt
  rw [IntegralEulerBits.term_packet, IntegralEulerBits.term_packet]
  change residueBits ((IntegralCriticalTotalCreatingBits.euler F).summand q
    (j.val % (IntegralCriticalTotalCreatingBits.euler F).free q) : ZMod ((IntegralCriticalTotalCreatingBits.euler F).modulus q)) = _
  rw [Nat.mod_eq_of_lt j.isLt]

theorem family_spatial (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) (j : ℕ)
    (hj : j ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q)) :
    IntegralCriticalTotalSnapshotBits.family F
      (IntegralCriticalFlatEulerRowsBits.spatial F.toParameters phase 0
        (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (IntegralCriticalHistoryTask.get F.toParameters .target q))))) =
    IntegralCriticalTotalSnapshotBits.family F q := by
  apply IntegralCriticalTotalSnapshotBits.family_invariance
  · simpa only [root, IntegralCriticalFlatHeightBits.root, pairFst_pair] using
      IntegralCriticalFlatEulerRowsBits.spatial_root F.toParameters phase 0
        (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (IntegralCriticalHistoryTask.get F.toParameters .target q))))
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_birth F.toParameters phase 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (IntegralCriticalHistoryTask.get F.toParameters .target q))))
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_modulus F.toParameters phase 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (IntegralCriticalHistoryTask.get F.toParameters .target q))))
  · simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other F.toParameters phase 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (IntegralCriticalHistoryTask.get F.toParameters .target q))))
      .coefficient (by decide) (by decide) (by decide)
  · exact (IntegralCriticalFlatEulerRowsBits.spatial_fields F.toParameters phase 0 q j _ hj
      (IntegralCriticalHistoryTask.get_le F.toParameters .target q) (Nat.zero_le _)).2.1
  all_goals
    simpa only [pairFst_pair] using IntegralCriticalFlatEulerRowsBits.spatial_other F.toParameters phase 0
      (pair q (pair (BinaryNatCode.encode j) (BinaryNatCode.encode (IntegralCriticalHistoryTask.get F.toParameters .target q))))
      _ (by decide) (by decide) (by decide)

theorem sum_child (F : Scripts) (q : List Bool) (j : ℕ)
    (hj : j < (IntegralCriticalTotalCreatingBits.euler F).free q) :
    product F (IntegralCriticalFlatEulerRowsBits.sumTask F.toParameters (IntegralCriticalTotalCreatingBits.euler F)
      (pair q (BinaryNatCode.encode j))) =
    IntegralEulerBits.termProgram (IntegralCriticalTotalCreatingBits.euler F) (pair q (BinaryNatCode.encode j)) := by
  have HC := IntegralCriticalActualSpatialTransport.selected_cap F q (⟨j, hj⟩ : Fin ((IntegralCriticalTotalCreatingBits.euler F).free q))
  have HF := IntegralCriticalFlatEulerRowsBits.spatial_fields F.toParameters .coordinateGradientProduct 0 q j
    (IntegralCriticalHistoryTask.get F.toParameters .target q) HC
    (IntegralCriticalHistoryTask.get_le F.toParameters .target q) (Nat.zero_le _)
  unfold product
  simp only [IntegralCriticalFlatEulerRowsBits.sumTask, IntegralEulerBits.termQuery, pairFst_pair, pairSnd_pair]
  have HT : (IntegralCriticalTotalCreatingBits.euler F).target q = IntegralCriticalHistoryTask.get F.toParameters .target q := rfl
  simp only [HT]
  rw [family_spatial F .coordinateGradientProduct q j HC, HF.1]
  exact productAt_packet F q ⟨j, hj⟩

end LeanCanny.Algebra.IntegralCriticalActualProductModel
