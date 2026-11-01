/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualFactorModel
/-! # Finite factor matrix children preserve the actual virtual generating data -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualMonomialBits IntegralCriticalActualLowMatrixModel
set_option backward.isDefEq.respectTransparency false

theorem factor_invariance (P : Parameters) (F : Family) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hc : get P .slot15 c = get P .slot15 q) (hm : modulus P c = modulus P q)
    (hx : get P .expression c = get P .expression q) (hj : get P .derivative c = get P .derivative q)
    (hk : get P .sourceIndex c = get P .sourceIndex q) (s r t : ℕ) : factorEntry P F c s r t = factorEntry P F q s r t := by
  rw [factor_snapshot, factor_snapshot]
  exact factorAt_congr F _ _ _ _ _ _ _ _ _ _ s r t _ _
    (IntegralMixedVirtualTaskBits.saved_invariance P q c hr hb hc) hx hj hk hm

theorem power_invariance (P : Parameters) (F : Family) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hc : get P .slot15 c = get P .slot15 q) (hm : modulus P c = modulus P q)
    (hx : get P .expression c = get P .expression q) (hj : get P .derivative c = get P .derivative q)
    (hk : get P .sourceIndex c = get P .sourceIndex q) (s r t : ℕ) : powerEntry P F c s r t = powerEntry P F q s r t := by
  rw [power_snapshot, power_snapshot]
  exact powerAt_congr F _ _ _ _ _ _ _ _ _ _ s r t _ _
    (IntegralMixedVirtualTaskBits.saved_invariance P q c hr hb hc) hx hj hk hm

theorem factor_dimension (P : Parameters) (F : Family) (q : List Bool) :
    (IntegralCriticalFlatGenericPowerBits.factorFamily P (source P F)).dimension q = rank P F q := by
  change (source P F).rank (pairFst (IntegralCriticalFlatFactorQuery.input P q)) = _
  rw [IntegralCriticalFlatFactorQuery.input_parent]
  rfl

theorem factor_matrix_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    entryBits ((IntegralCriticalFlatGenericPowerBits.factorFamily P (source P F)).matrix q) r t = factorEntry P F q (get P .slot8 q) r t := by
  change entryBits ((IntegralPowerProductBits.powerFamily (IntegralMonomialTermBits.family (source P F))).matrix (IntegralCriticalFlatFactorQuery.input P q)) r t = _
  generalize hp : IntegralCriticalFlatFactorQuery.input P q = p
  have HC : pairFst p = q := by rw [← hp, IntegralCriticalFlatFactorQuery.input_parent]
  have HS : Nat.fromBitsLE (IntegralPowerProductBits.factorWord p) = get P .slot8 q := by
    rw [← hp, IntegralCriticalFlatFactorQuery.input, IntegralPowerProductBits.factorWord]
    simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst q
  let := (source P F).ring (pairFst p)
  change entryBits ((Algebra.leftMulMatrix ((source P F).basis (pairFst p))
    (IntegralMonomialTermBits.factor (source P F) (pairFst p) (Nat.fromBitsLE (IntegralPowerProductBits.factorWord p)))).map
      (Int.castRingHom (ZMod ((source P F).modulus (pairFst p))))) r t = _
  rw [HS]
  rfl

theorem monomial_child (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (p : Phase) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (r t : ℕ)
    (hr : r < rank P F q) (ht : t < rank P F q) :
    monomial P F (IntegralCriticalFlatMatrixQuery.writer P p (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))) =
      factorEntry P F q (get P .slot8 q) r t := by
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
    exact min_eq_left (hr.le.trans (rank_cap P F g q hv))
  have HCOL : get P .col child = t := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (ht.le.trans (rank_cap P F g q hv))
  change monomial P F child = _
  unfold monomial
  rw [HROW, HCOL, rank_invariance P F q child HR HB (HF .slot15 (by decide) (by decide)), Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt ht,
    HF .slot8 (by decide) (by decide)]
  exact factor_invariance P F q child HR HB (HF .slot15 (by decide) (by decide)) HM
    (HF .expression (by decide) (by decide)) (HF .derivative (by decide) (by decide)) (HF .sourceIndex (by decide) (by decide)) _ r t

theorem factor_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralCriticalFlatGenericPowerBits.RepliesAt P (IntegralCriticalFlatGenericPowerBits.factorFamily P (source P F))
      .monomialFactor (monomial P F) q := by
  intro r t
  have HR : r.val < rank P F q := by rw [← factor_dimension P F q]; exact r.isLt
  have HT : t.val < rank P F q := by rw [← factor_dimension P F q]; exact t.isLt
  exact (monomial_child P F g .monomialFactor q hv r.val t.val HR HT).trans
    ((factor_matrix_snapshot P F q r.val t.val).symm.trans (entryBits_fin _ r t))

theorem power_value (P : Parameters) (F : Family) (q : List Bool) :
    (IntegralPowerProductBits.powerFamily (IntegralMonomialTermBits.family (source P F))).value
      (IntegralCriticalFlatFactorQuery.input P q) = power P F q :=
  IntegralCriticalActualFactorModel.power_packet_natural (source P F) q _ _ _
end LeanCanny.Algebra.IntegralMixedVirtualFactorBits
