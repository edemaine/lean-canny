/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualMomentMatrix
public import LeanCanny.Algebra.IntegralMixedNativeMomentPower
/-! # Actual virtual augmented-entry models and finite power replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev moment (P : Parameters) (F : Family) := IntegralCriticalFlatMomentBits.source P (characteristic P F)
noncomputable def momentEntry (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  IntegralMixedVirtualMomentMatrixBits.modularEntry P F q
    (get P .row q % IntegralMixedVirtualMomentMatrixBits.size P F q)
    (get P .col q % IntegralMixedVirtualMomentMatrixBits.size P F q)

theorem moment_rank (P : Parameters) (F : Family) (q : List Bool) : (moment P F).rank q = (characteristic P F).rank q := by
  change (characteristic P F).rank (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatMomentBits.packet P q)) = _
  rw [IntegralCriticalFlatMomentBits.packet_parent]

theorem moment_size_pos (P : Parameters) (F : Family) (q : List Bool) : 0 < IntegralMixedVirtualMomentMatrixBits.size P F q := by
  have HR : 0 < (moment P F).rank q := (moment_rank P F q).symm ▸ (characteristic P F).rank_pos q
  change 0 < ((moment P F).dimension q + 2) * (moment P F).rank q
  exact Nat.mul_pos (by omega) HR

theorem moment_modulus (P : Parameters) (F : Family) (q : List Bool) : (moment P F).modulus q = modulus P q := by
  change (characteristic P F).modulus (IntegralBerkowitzBlockBits.original (IntegralCriticalFlatMomentBits.packet P q)) = _
  rw [IntegralCriticalFlatMomentBits.packet_parent]
  rfl

theorem moment_dimension_le (P : Parameters) (F : Family) (q : List Bool) : (moment P F).dimension q ≤ (characteristic P F).dimension q := by
  change IntegralBerkowitzBlockBits.remaining (characteristic P F) (IntegralCriticalFlatMomentBits.packet P q) ≤ _
  unfold IntegralBerkowitzBlockBits.remaining
  rw [IntegralCriticalFlatMomentBits.packet_parent]
  exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)

theorem moment_size_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedVirtualMomentMatrixBits.size P F q ≤ numericCap P (RankedHistoryTask.root q) := by
  have HD := (moment_dimension_le P F q).trans (IntegralMixedVirtualCaps.dimension_le P F g q)
  have HR : (moment P F).rank q ≤ rankCap P (RankedHistoryTask.root q) := by
    rw [moment_rank]
    exact IntegralMixedVirtualCaps.rank_le P F g q hv
  have HC : (PurePowerReductionBounds.dimension (P.ambient (RankedHistoryTask.root q) + 1)
      (P.degree (RankedHistoryTask.root q)) + 2) * rankCap P (RankedHistoryTask.root q) ≤ numericCap P (RankedHistoryTask.root q) := by
    unfold numericCap
    exact IntegralCriticalQueryBounds.moment_block_le _ _ _ _ _ _ _ _
  exact (Nat.mul_le_mul (Nat.add_le_add_right HD 2) HR).trans HC

attribute [local irreducible] characteristic characteristicAccess IntegralMixedVirtualMomentMatrixBits.modularEntry
  IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

theorem value21 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (answer : List Bool → List Bool) (q : List Bool)
    (he : IntegralCriticalFlatMomentEntryBits.RepliesAt P a (characteristic P F) (characteristicAccess P a F h) answer q) :
    (IntegralCriticalFlatMomentEntryBits.program P a (characteristic P F) (characteristicAccess P a F h)).value answer q = momentEntry P F q := by
  rw [IntegralCriticalFlatMomentEntryBits.value P a (characteristic P F) (characteristicAccess P a F h) answer q he]
  let r : Fin (IntegralMixedVirtualMomentMatrixBits.size P F q) :=
    ⟨get P .row q % IntegralMixedVirtualMomentMatrixBits.size P F q, Nat.mod_lt _ (moment_size_pos P F q)⟩
  let t : Fin (IntegralMixedVirtualMomentMatrixBits.size P F q) :=
    ⟨get P .col q % IntegralMixedVirtualMomentMatrixBits.size P F q, Nat.mod_lt _ (moment_size_pos P F q)⟩
  have HE := IntegralBlockMomentBits.entry_correct (moment P F)
    (IntegralCriticalFlatMomentBits.access P a (characteristic P F) (characteristicAccess P a F h)) q r t
  have HM := congrArg (fun m => residueBits (((moment P F).powerMatrix q r t : ℤ) : ZMod m)) (moment_modulus P F q)
  exact HE.trans (HM.trans (IntegralMixedVirtualMomentMatrixBits.modularEntry_fin P F q r t).symm)

theorem moment_entry_child (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (i j : Fin (IntegralMixedVirtualMomentMatrixBits.size P F q)) :
    momentEntry P F (IntegralCriticalFlatMatrixQuery.writer P .momentEntry
      (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((moment P F).powerMatrix q i j : ℤ) : ZMod ((moment P F).modulus q)) := by
  let c := IntegralCriticalFlatMatrixQuery.writer P .momentEntry
    (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  have HR : RankedHistoryTask.root c = RankedHistoryTask.root q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_root, pairFst_pair]
  have HB : birth P c = birth P q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_birth, pairFst_pair]
  have HM : modulus P c = modulus P q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_modulus, pairFst_pair]
  have HX : get P .slot15 c = get P .slot15 q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, reduceCtorEq, ite_false]
  have HJ : get P .slot13 c = get P .slot13 q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, reduceCtorEq, ite_false]
  have HS : get P .slot11 c = get P .slot11 q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, reduceCtorEq, ite_false]
  have HT : get P .slot12 c = get P .slot12 q := by simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, reduceCtorEq, ite_false]
  have HD := IntegralMixedVirtualMomentMatrixBits.size_transport P F q c HR HB HX HJ HS HT
  have HI : get P .row c = i.val := by
    simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]
    exact min_eq_left (i.isLt.le.trans (moment_size_cap P F g q hv))
  have HK : get P .col c = j.val := by
    simp only [c, IntegralCriticalFlatMatrixQuery.writer_get, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, reduceCtorEq, ite_true, ite_false]
    exact min_eq_left (j.isLt.le.trans (moment_size_cap P F g q hv))
  change momentEntry P F c = _
  unfold momentEntry
  rw [HI, HK, HD, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]
  have HE := (IntegralMixedVirtualMomentMatrixBits.modularEntry_transport P F q c HR HB HX HJ HS HT HM i.val j.val).trans
    (IntegralMixedVirtualMomentMatrixBits.modularEntry_fin P F q i j)
  exact HE.trans (congrArg (fun m => residueBits (((moment P F).powerMatrix q i j : ℤ) : ZMod m)) (moment_modulus P F q).symm)

end LeanCanny.Algebra.IntegralMixedVirtualUpperBits
