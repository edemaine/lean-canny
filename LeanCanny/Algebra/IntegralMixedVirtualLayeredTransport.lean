/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualLayeredModel
/-! # Finite layered-product children preserve virtual source data -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualLayeredBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualMonomialBits IntegralCriticalActualLowMatrixModel
set_option backward.isDefEq.respectTransparency false

theorem productEntry_child (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (p : Phase) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (r t : ℕ)
    (hr : r < dimension P F q) (ht : t < dimension P F q) :
    productEntry P F (IntegralCriticalFlatMatrixQuery.writer P p (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))) =
      layeredEntry P F q r t := by
  let child := IntegralCriticalFlatMatrixQuery.writer P p (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))
  have HR : RankedHistoryTask.root child = RankedHistoryTask.root q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_root P p (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))
  have HB : birth P child = birth P q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_birth P p (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))
  have HM : modulus P child = modulus P q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_modulus P p (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))
  have HF (f : Field) (hf : f ≠ .row) (hg : f ≠ .col) : get P f child = get P f q := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [hf, hg, ite_false, pairFst_pair]
  have HROW : get P .row child = r := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (hr.le.trans (dimension_cap P F g q hv))
  have HCOL : get P .col child = t := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (ht.le.trans (dimension_cap P F g q hv))
  change productEntry P F child = _
  unfold productEntry
  rw [HROW, HCOL, dimension_invariance P F q child HR HB (HF .slot15 (by decide) (by decide)), Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt ht]
  exact layered_invariance P F q child HR HB (HF .slot15 (by decide) (by decide)) HM
    (HF .expression (by decide) (by decide)) (HF .derivative (by decide) (by decide)) (HF .sourceIndex (by decide) (by decide)) r t

theorem product_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralCriticalFlatGenericPowerBits.RepliesAt P (IntegralCriticalFlatGenericPowerBits.productFamily (source P F))
      .productEntry (productEntry P F) q := by
  intro r t
  exact (productEntry_child P F g .productEntry q hv r.val t.val r.isLt t.isLt).trans (entryBits_fin _ r t)
end LeanCanny.Algebra.IntegralMixedVirtualLayeredBits
