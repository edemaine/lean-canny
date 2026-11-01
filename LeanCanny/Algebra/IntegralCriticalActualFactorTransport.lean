/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualFactorModel
/-! # Actual typed factor-power requests under fresh matrix writers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualFactorTransport
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualMonomialSnapshot IntegralCriticalActualLowMatrixModel
open IntegralCriticalActualFactorModel
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily IntegralCriticalFlatActualLow.source
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap
attribute [local irreducible] IntegralCriticalFlatMatrixQuery.writer

theorem factor_invariance (F : Scripts) (child q : List Bool)
    (hr : root child = root q)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q)
    (hx : IntegralCriticalHistoryTask.get F.toParameters .expression child = IntegralCriticalHistoryTask.get F.toParameters .expression q)
    (hj : IntegralCriticalHistoryTask.get F.toParameters .derivative child = IntegralCriticalHistoryTask.get F.toParameters .derivative q)
    (hk : IntegralCriticalHistoryTask.get F.toParameters .sourceIndex child = IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
    (s r t : ℕ) : factorEntry F child s r t = factorEntry F q s r t := by
  rw [factor_snapshot, factor_snapshot]
  exact factorAt_congr _ _ _ _ _ _ _ _ _ _ s r t _ _
    (IntegralCriticalTotalCreatingBits.atFamily_invariance F child q hr hb) hx hj hk hm

theorem power_invariance (F : Scripts) (child q : List Bool)
    (hr : root child = root q)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q)
    (hx : IntegralCriticalHistoryTask.get F.toParameters .expression child = IntegralCriticalHistoryTask.get F.toParameters .expression q)
    (hj : IntegralCriticalHistoryTask.get F.toParameters .derivative child = IntegralCriticalHistoryTask.get F.toParameters .derivative q)
    (hk : IntegralCriticalHistoryTask.get F.toParameters .sourceIndex child = IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
    (s r t : ℕ) : powerEntry F child s r t = powerEntry F q s r t := by
  rw [power_snapshot, power_snapshot]
  exact powerAt_congr _ _ _ _ _ _ _ _ _ _ s r t _ _
    (IntegralCriticalTotalCreatingBits.atFamily_invariance F child q hr hb) hx hj hk hm

theorem factor_dimension (F : Scripts) (q : List Bool) :
    (IntegralCriticalFlatGenericPowerBits.factorFamily F.toParameters (IntegralCriticalFlatActualLow.source F)).dimension q = rank F q := by
  change (IntegralCriticalFlatActualLow.source F).rank (pairFst (IntegralCriticalFlatFactorQuery.input F.toParameters q)) = _
  rw [IntegralCriticalFlatFactorQuery.input_parent]
  rfl

theorem factor_matrix_snapshot (F : Scripts) (q : List Bool) (r t : ℕ) :
    entryBits ((IntegralCriticalFlatGenericPowerBits.factorFamily F.toParameters (IntegralCriticalFlatActualLow.source F)).matrix q) r t =
      factorEntry F q (IntegralCriticalHistoryTask.get F.toParameters .slot8 q) r t := by
  change entryBits ((IntegralPowerProductBits.powerFamily (IntegralMonomialTermBits.family (IntegralCriticalFlatActualLow.source F))).matrix
    (IntegralCriticalFlatFactorQuery.input F.toParameters q)) r t = _
  generalize hp : IntegralCriticalFlatFactorQuery.input F.toParameters q = p
  have HC : pairFst p = q := by rw [← hp, IntegralCriticalFlatFactorQuery.input_parent]
  have HS : Nat.fromBitsLE (IntegralPowerProductBits.factorWord p) = IntegralCriticalHistoryTask.get F.toParameters .slot8 q := by
    rw [← hp, IntegralCriticalFlatFactorQuery.input, IntegralPowerProductBits.factorWord]
    simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst q
  let := (IntegralCriticalFlatActualLow.source F).ring (pairFst p)
  change entryBits ((Algebra.leftMulMatrix ((IntegralCriticalFlatActualLow.source F).basis (pairFst p))
    (IntegralMonomialTermBits.factor (IntegralCriticalFlatActualLow.source F) (pairFst p)
      (Nat.fromBitsLE (IntegralPowerProductBits.factorWord p)))).map
        (Int.castRingHom (ZMod ((IntegralCriticalFlatActualLow.source F).modulus (pairFst p))))) r t = _
  rw [HS]
  rfl

theorem monomial_child (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) (r t : ℕ)
    (hr : r < rank F q) (ht : t < rank F q) :
    monomial F (IntegralCriticalFlatMatrixQuery.writer F.toParameters phase
      (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))) =
      factorEntry F q (IntegralCriticalHistoryTask.get F.toParameters .slot8 q) r t := by
  let child := IntegralCriticalFlatMatrixQuery.writer F.toParameters phase
    (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))
  have HR : root child = root q := by
    simpa only [child, root, IntegralCriticalFlatHeightBits.root, pairFst_pair] using
      IntegralCriticalFlatMatrixQuery.writer_root F.toParameters phase (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))
  have HB : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_birth F.toParameters phase
      (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))
  have HM : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_modulus F.toParameters phase
      (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))
  have HF (f : IntegralCriticalHistoryTask.Field) (hf : f ≠ .row) (hg : f ≠ .col) :
      IntegralCriticalHistoryTask.get F.toParameters f child = IntegralCriticalHistoryTask.get F.toParameters f q := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [hf, hg, ite_false, pairFst_pair]
  have HROW : IntegralCriticalHistoryTask.get F.toParameters .row child = r := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (hr.le.trans (rank_cap F q))
  have HCOL : IntegralCriticalHistoryTask.get F.toParameters .col child = t := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (ht.le.trans (rank_cap F q))
  change monomial F child = _
  unfold monomial
  rw [HROW, HCOL, rank_invariance F child q HR HB, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt ht,
    HF .slot8 (by decide) (by decide)]
  exact factor_invariance F child q HR HB HM (HF .expression (by decide) (by decide))
    (HF .derivative (by decide) (by decide)) (HF .sourceIndex (by decide) (by decide)) _ r t

theorem factor_replies (F : Scripts) (q : List Bool) :
    IntegralCriticalFlatGenericPowerBits.RepliesAt F.toParameters
      (IntegralCriticalFlatGenericPowerBits.factorFamily F.toParameters (IntegralCriticalFlatActualLow.source F))
      .monomialFactor (monomial F) q := by
  intro r t
  have HR : r.val < rank F q := by rw [← factor_dimension F q]; exact r.isLt
  have HT : t.val < rank F q := by rw [← factor_dimension F q]; exact t.isLt
  exact (monomial_child F .monomialFactor q r.val t.val HR HT).trans
    ((factor_matrix_snapshot F q r.val t.val).symm.trans (entryBits_fin _ r t))

end LeanCanny.Algebra.IntegralCriticalActualFactorTransport
