/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualMonomialHeightTransport
public import LeanCanny.Algebra.IntegralMixedVirtualNativeFolds
/-! # Actual virtual frozen powers request the selected height matrix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
theorem power_height_child (P : Parameters) (_a : Access P) (F : Family) (_h : InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (r t : Fin ((source P F).toGradient.toFrozen.rank q)) :
    height P F
      (IntegralCriticalFlatMatrixQuery.writer P .clearedHeight
        (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      residueBits ((IntegralCriticalFlatFrozenTermBits.family P (source P F).toGradient.toFrozen).matrix q r t) := by
  let child := IntegralCriticalFlatMatrixQuery.writer P .clearedHeight
    (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HR : RankedHistoryTask.root child = RankedHistoryTask.root q := by
    simpa only [child, pairFst_pair] using
      IntegralCriticalFlatMatrixQuery.writer_root P .clearedHeight
        (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HB : IntegralCriticalHistoryTask.birth P child = IntegralCriticalHistoryTask.birth P q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_birth P .clearedHeight
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HM : IntegralCriticalHistoryTask.modulus P child = IntegralCriticalHistoryTask.modulus P q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_modulus P .clearedHeight
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HI : IntegralCriticalHistoryTask.get P .slot8 child = IntegralCriticalHistoryTask.get P .slot8 q := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, pairFst_pair]
  have HROW : IntegralCriticalHistoryTask.get P .row child = r.val := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (r.isLt.le.trans (IntegralMixedVirtualCaps.rank_cap P F g q hv))
  have HCOL : IntegralCriticalHistoryTask.get P .col child = t.val := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (t.isLt.le.trans (IntegralMixedVirtualCaps.rank_cap P F g q hv))
  have HX : get P .slot15 child = get P .slot15 q := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, pairFst_pair]
  change height P F child = _
  rw [IntegralMixedVirtualMonomialHeightBits.height_snapshot, HI, HROW, HCOL]
  refine (IntegralMixedVirtualMonomialHeightBits.heightAt_congr F (IntegralMixedVirtualTaskBits.saved P child) (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot8 q) r.val t.val (modulus P child) (get P .slot8 q) r.val t.val (modulus P q)
    (modulus_ne_zero P child) (modulus_ne_zero P q)
    (IntegralMixedVirtualTaskBits.saved_invariance P q child HR HB HX) rfl rfl rfl HM).trans ?_
  let := (source P F).ring q
  have HRI : (⟨r.val % (source P F).rank q, Nat.mod_lt _ ((Nat.zero_le _).trans_lt r.isLt)⟩ : Fin ((source P F).rank q)) = r :=
    Fin.ext (Nat.mod_eq_of_lt r.isLt)
  have HTI : (⟨t.val % (source P F).rank q, Nat.mod_lt _ ((Nat.zero_le _).trans_lt t.isLt)⟩ : Fin ((source P F).rank q)) = t :=
    Fin.ext (Nat.mod_eq_of_lt t.isLt)
  change residueBits ((Algebra.leftMulMatrix ((source P F).basis q) ((source P F).height q (get P .slot8 q))
    ⟨r.val % (source P F).rank q, _⟩ ⟨t.val % (source P F).rank q, _⟩ : ℤ) : ZMod (modulus P q)) = _
  rw [HRI, HTI]
  rfl
end LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
