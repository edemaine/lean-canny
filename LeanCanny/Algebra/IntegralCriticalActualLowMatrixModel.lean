/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualMonomialSnapshot
public import LeanCanny.Algebra.IntegralCriticalActualFrozenTransport
/-! # Natural entries of actual monomial product matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualLowMatrixModel
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualMonomialSnapshot
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap
attribute [local irreducible] IntegralCriticalFlatMatrixQuery.writer

noncomputable def entryBits {m n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod m)) (r t : ℕ) : List Bool :=
  if hr : r < n then if ht : t < n then residueBits (M ⟨r, hr⟩ ⟨t, ht⟩) else [] else []
theorem entryBits_fin {m n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod m)) (r t : Fin n) :
    entryBits M r.val t.val = residueBits (M r t) := by
  unfold entryBits
  rw [dite_eq_left r.isLt, dite_eq_left t.isLt]

noncomputable def dimensionAt (A : IntegralHistoryCriticalBits.Family) :=
  ((IntegralCriticalActualScalarModels.eulerAt A).arity [] + 3) * (IntegralCriticalActualScalarModels.eulerAt A).rank []
noncomputable def dimension (F : Scripts) (q : List Bool) :=
  (IntegralCriticalFlatGenericPowerBits.productFamily (IntegralCriticalFlatActualLow.source F)).dimension q

noncomputable def layeredAt (A : IntegralHistoryCriticalBits.Family) (x j k m : ℕ) (hm : m ≠ 0) (r t : ℕ) :=
  entryBits ((IntegralCriticalFlatGenericPowerBits.productFamily (monomialAt A x j k 0 0 m hm)).matrix []) r t
noncomputable def layeredEntry (F : Scripts) (q : List Bool) (r t : ℕ) :=
  entryBits ((IntegralCriticalFlatGenericPowerBits.productFamily (IntegralCriticalFlatActualLow.source F)).matrix q) r t
noncomputable def productEntry (F : Scripts) (q : List Bool) :=
  layeredEntry F q (IntegralCriticalHistoryTask.get F.toParameters .row q % dimension F q)
    (IntegralCriticalHistoryTask.get F.toParameters .col q % dimension F q)

theorem dimension_snapshot (F : Scripts) (q : List Bool) : dimension F q = dimensionAt (IntegralCriticalTotalCreatingBits.atFamily F q) := by
  change (IntegralCriticalFlatGenericPowerBits.productFamily ((IntegralCriticalFlatActualLow.source F).snapshot q)).dimension [] = _
  rw [source_snapshot]
  rfl

theorem layered_snapshot (F : Scripts) (q : List Bool) (r t : ℕ) :
    layeredEntry F q r t = layeredAt (IntegralCriticalTotalCreatingBits.atFamily F q)
      (IntegralCriticalHistoryTask.get F.toParameters .expression q)
      (IntegralCriticalHistoryTask.get F.toParameters .derivative q)
      (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
      (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) r t := by
  change entryBits ((IntegralCriticalFlatGenericPowerBits.productFamily ((IntegralCriticalFlatActualLow.source F).snapshot q)).matrix []) r t = _
  rw [source_snapshot]
  rfl

theorem dimension_invariance (F : Scripts) (child q : List Bool)
    (hr : root child = root q)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q) :
    dimension F child = dimension F q := by
  rw [dimension_snapshot, dimension_snapshot]
  exact congrArg dimensionAt (IntegralCriticalTotalCreatingBits.atFamily_invariance F child q hr hb)

theorem layeredAt_congr (A B : IntegralHistoryCriticalBits.Family) (x j k m x' j' k' m' r t : ℕ)
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hA : A = B) (hx : x = x') (hj : j = j') (hk : k = k') (hmod : m = m') :
    layeredAt A x j k m hm r t = layeredAt B x' j' k' m' hm' r t := by
  subst B; subst x'; subst j'; subst k'; subst m'
  rfl

theorem layered_invariance (F : Scripts) (child q : List Bool)
    (hr : root child = root q)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q)
    (hx : IntegralCriticalHistoryTask.get F.toParameters .expression child = IntegralCriticalHistoryTask.get F.toParameters .expression q)
    (hj : IntegralCriticalHistoryTask.get F.toParameters .derivative child = IntegralCriticalHistoryTask.get F.toParameters .derivative q)
    (hk : IntegralCriticalHistoryTask.get F.toParameters .sourceIndex child = IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
    (r t : ℕ) : layeredEntry F child r t = layeredEntry F q r t := by
  rw [layered_snapshot, layered_snapshot]
  exact layeredAt_congr _ _ _ _ _ _ _ _ _ _ r t _ _
    (IntegralCriticalTotalCreatingBits.atFamily_invariance F child q hr hb) hx hj hk hm

theorem dimension_cap (F : Scripts) (q : List Bool) (hv : valid F q) :
    dimension F q ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q) := by
  have HA : (IntegralCriticalFlatActualLow.source F).arity q ≤ F.ambient (root q) + 1 := by
    change (IntegralCriticalTotalCreatingBits.euler F).arity (pairFst (IntegralCriticalFlatGridBits.termInput F.toParameters q)) ≤ _
    rw [IntegralCriticalFlatGridBits.termInput_parent]
    change (IntegralCriticalTotalCreatingBits.atFamily F q).ambient [] + 1 ≤ _
    rw [IntegralCriticalTotalCreatingBits.at_ambient, ite_eq_left hv]
  have HR : (IntegralCriticalFlatActualLow.source F).rank q ≤ IntegralCriticalHistoryTask.rankCap F.toParameters (root q) := by
    change (IntegralCriticalTotalCreatingBits.euler F).rank (pairFst (IntegralCriticalFlatGridBits.termInput F.toParameters q)) ≤ _
    rw [IntegralCriticalFlatGridBits.termInput_parent]
    exact IntegralCriticalActualCaps.rank_le F q hv
  change (((IntegralCriticalFlatActualLow.source F).arity q + 2) + 1) * (IntegralCriticalFlatActualLow.source F).rank q ≤ _
  unfold IntegralCriticalHistoryTask.numericCap
  exact IntegralCriticalQueryBounds.product_block_le_of_le
    (IntegralCriticalHistoryTask.birthCap F.toParameters (root q)) (F.ambient (root q) + 1)
    (IntegralCriticalHistoryTask.rankCap F.toParameters (root q)) (F.sourceWidth (root q)) (F.degree (root q))
    (2 ^ F.width (root q)) (IntegralCriticalHistoryTask.heightBudget F.toParameters (root q))
    (F.modulusBound (root q)) (Nat.add_le_add_right HA 2) HR


theorem product_power_child (F : Scripts) (q : List Bool) (hv : valid F q)
    (r t : Fin ((IntegralCriticalFlatGenericPowerBits.productFamily (IntegralCriticalFlatActualLow.source F)).dimension q)) :
    productEntry F (IntegralCriticalFlatMatrixQuery.writer F.toParameters .productEntry
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
    residueBits ((IntegralCriticalFlatGenericPowerBits.productFamily (IntegralCriticalFlatActualLow.source F)).matrix q r t) := by
  let child := IntegralCriticalFlatMatrixQuery.writer F.toParameters .productEntry
    (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HR : root child = root q := by
    simpa only [child, root, IntegralCriticalFlatHeightBits.root, pairFst_pair] using
      IntegralCriticalFlatMatrixQuery.writer_root F.toParameters .productEntry
        (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HB : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_birth F.toParameters .productEntry
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HM : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q := by
    simpa only [child, pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_modulus F.toParameters .productEntry
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
  have HD := dimension_invariance F child q HR HB
  have HROW : IntegralCriticalHistoryTask.get F.toParameters .row child = r.val := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (r.isLt.le.trans (dimension_cap F q hv))
  have HCOL : IntegralCriticalHistoryTask.get F.toParameters .col child = t.val := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact min_eq_left (t.isLt.le.trans (dimension_cap F q hv))
  have HX : IntegralCriticalHistoryTask.get F.toParameters .expression child = IntegralCriticalHistoryTask.get F.toParameters .expression q := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, pairFst_pair]
  have HJ : IntegralCriticalHistoryTask.get F.toParameters .derivative child = IntegralCriticalHistoryTask.get F.toParameters .derivative q := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, pairFst_pair]
  have HK : IntegralCriticalHistoryTask.get F.toParameters .sourceIndex child = IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q := by
    dsimp only [child]
    rw [IntegralCriticalFlatMatrixQuery.writer_get]
    simp only [reduceCtorEq, ite_false, pairFst_pair]
  have HRmod : r.val % dimension F q = r.val := Nat.mod_eq_of_lt r.isLt
  have HTmod : t.val % dimension F q = t.val := Nat.mod_eq_of_lt t.isLt
  change productEntry F child = _
  unfold productEntry
  rw [HROW, HCOL, HD, HRmod, HTmod,
    layered_invariance F child q HR HB HM HX HJ HK]
  exact entryBits_fin _ r t

theorem power_replies (F : Scripts) (q : List Bool) (hv : valid F q) :
    IntegralCriticalFlatGenericPowerBits.RepliesAt F.toParameters
      (IntegralCriticalFlatGenericPowerBits.productFamily (IntegralCriticalFlatActualLow.source F))
      .productEntry (productEntry F) q := product_power_child F q hv

end LeanCanny.Algebra.IntegralCriticalActualLowMatrixModel
