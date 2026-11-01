/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualMonomialLeaves
public import LeanCanny.Algebra.IntegralMixedVirtualFactorTransport
public import LeanCanny.Algebra.IntegralMixedVirtualNativeDerivative
/-! # Concrete coefficient children of the charged virtual monomial controller -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualMonomialLeafBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualMonomialBits IntegralMixedVirtualFactorBits
set_option backward.isDefEq.respectTransparency false

noncomputable def coefficient (P : Parameters) (F : Family) (q : List Bool) :=
  if get P .expression q = 1 then IntegralMixedVirtualCoefficientBits.derivative P F q else IntegralMixedVirtualNativeLowerBits.original P F q

theorem monomial_eq_coefficient (P : Parameters) (F : Family) (q : List Bool)
    (hs : get P .slot8 q = 0) (hr : get P .row q < rank P F q) (ht : get P .col q < rank P F q) :
    monomial P F q = coefficient P F q := by
  have HR := hr
  have HT := ht
  rw [rank_snapshot] at HR HT
  unfold monomial
  rw [hs, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt ht, factor_snapshot,
    factorAt_cases F _ _ _ _ _ _ _ _ HR HT]
  unfold coefficient IntegralMixedVirtualCoefficientBits.derivative
  rw [IntegralMixedVirtualCoefficientBits.original_snapshot]

theorem coefficient_matrix_child (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (p : Phase) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (r t : Fin ((source P F).rank q)) (hs : get P .slot8 q = 0) :
    coefficient P F (IntegralCriticalFlatMatrixQuery.writer P p (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      factorEntry P F q 0 r.val t.val := by
  let child := IntegralCriticalFlatMatrixQuery.writer P p (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HR : RankedHistoryTask.root child = RankedHistoryTask.root q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_root P p (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HB : birth P child = birth P q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_birth P p (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HF (f : Field) (hf : f ≠ .row) (hg : f ≠ .col) : get P f child = get P f q := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [hf, hg, ite_false, pairFst_pair]
  have HS : get P .slot8 child = 0 := (HF .slot8 (by decide) (by decide)).trans hs
  have Hrank := rank_invariance P F q child HR HB (HF .slot15 (by decide) (by decide))
  have HROW : get P .row child = r.val := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (r.isLt.le.trans (rank_cap P F g q hv))
  have HCOL : get P .col child = t.val := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (t.isLt.le.trans (rank_cap P F g q hv))
  change coefficient P F child = _
  rw [← monomial_eq_coefficient P F child HS (by rw [HROW, Hrank]; exact r.isLt) (by rw [HCOL, Hrank]; exact t.isLt)]
  rw [monomial_child P F g p q hv r.val t.val r.isLt t.isLt, hs]

theorem coefficient_child (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q)
    (r t : Fin ((source P F).rank q)) (hs : get P .slot8 q = 0) :
    coefficient P F (IntegralCriticalFlatGenericMonomialBits.coefficientTask P
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      (access P a F h).coefficient (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) := by
  rw [coefficient_leaf]
  unfold IntegralCriticalFlatGenericMonomialBits.coefficientTask
  simp only [pairFst_pair]
  split_ifs
  all_goals exact coefficient_matrix_child P F g _ q hv r t hs
end LeanCanny.Algebra.IntegralMixedVirtualMonomialLeafBits
