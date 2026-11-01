/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualFactorTransport
public import LeanCanny.Algebra.IntegralCriticalActualNaturalPower
/-! # Actual product-entry requests of monomial factor powers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualProductEntryTransport
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualFactorModel IntegralCriticalActualFactorTransport
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily IntegralCriticalFlatActualLow.source
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap
attribute [local irreducible] IntegralCriticalFlatFactorQuery.writer

theorem power_value (F : Scripts) (q : List Bool) :
    (IntegralPowerProductBits.powerFamily (IntegralMonomialTermBits.family (IntegralCriticalFlatActualLow.source F))).value
      (IntegralCriticalFlatFactorQuery.input F.toParameters q) = power F q :=
  power_packet_natural (IntegralCriticalFlatActualLow.source F) q _ _ _

theorem power_child (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) (s r t : ℕ)
    (hs : s ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q))
    (hr : r < rank F q) (ht : t < rank F q) :
    power F (IntegralCriticalFlatFactorQuery.writer F.toParameters phase (IntegralMonomialTermBits.packet q s r t)) =
      powerEntry F q s r t := by
  let child := IntegralCriticalFlatFactorQuery.writer F.toParameters phase (IntegralMonomialTermBits.packet q s r t)
  have HR : root child = root q := by
    simpa only [child, root, IntegralCriticalFlatHeightBits.root, IntegralMonomialTermBits.packet, pairFst_pair] using
      IntegralCriticalFlatFactorQuery.writer_root F.toParameters phase (IntegralMonomialTermBits.packet q s r t)
  have HB : IntegralCriticalHistoryTask.birth F.toParameters child = IntegralCriticalHistoryTask.birth F.toParameters q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using IntegralCriticalFlatFactorQuery.writer_birth
      F.toParameters phase (IntegralMonomialTermBits.packet q s r t)
  have HM : IntegralCriticalHistoryTask.modulus F.toParameters child = IntegralCriticalHistoryTask.modulus F.toParameters q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using IntegralCriticalFlatFactorQuery.writer_modulus
      F.toParameters phase (IntegralMonomialTermBits.packet q s r t)
  have HF (f : IntegralCriticalHistoryTask.Field) (hrow : f ≠ .row) (hcol : f ≠ .col) (hslot : f ≠ .slot8) :
      IntegralCriticalHistoryTask.get F.toParameters f child = IntegralCriticalHistoryTask.get F.toParameters f q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using IntegralCriticalFlatFactorQuery.writer_other
      F.toParameters phase (IntegralMonomialTermBits.packet q s r t) f hrow hcol hslot
  have HQ := IntegralCriticalFlatFactorQuery.writer_packet_fields F.toParameters phase q s r t hs
    (hr.le.trans (rank_cap F q)) (ht.le.trans (rank_cap F q))
  change power F child = _
  unfold power
  rw [HQ.1, HQ.2.1, HQ.2.2, rank_invariance F child q HR HB, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt ht]
  exact power_invariance F child q HR HB HM (HF .expression (by decide) (by decide) (by decide))
    (HF .derivative (by decide) (by decide) (by decide)) (HF .sourceIndex (by decide) (by decide) (by decide)) s r t

theorem power_child_packet (F : Scripts) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) (s r t : ℕ)
    (hs : s ≤ IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q))
    (hr : r < rank F q) (ht : t < rank F q) :
    power F (IntegralCriticalFlatFactorQuery.writer F.toParameters phase (IntegralMonomialTermBits.packet q s r t)) =
      (IntegralPowerProductBits.powerFamily (IntegralMonomialTermBits.family (IntegralCriticalFlatActualLow.source F))).value
        (IntegralMonomialTermBits.packet q s r t) := by
  rw [power_child F phase q s r t hs hr ht]
  unfold IntegralMonomialTermBits.packet
  rw [power_packet_natural]
  have HRmod : r % (IntegralCriticalFlatActualLow.source F).rank q = r := Nat.mod_eq_of_lt hr
  have HTmod : t % (IntegralCriticalFlatActualLow.source F).rank q = t := Nat.mod_eq_of_lt ht
  rw [HRmod, HTmod]
  rfl

theorem count_cap (F : Scripts) (q : List Bool) (hv : valid F q) :
    (IntegralMonomialTermBits.family (IntegralCriticalFlatActualLow.source F)).count q ≤
      IntegralCriticalHistoryTask.numericCap F.toParameters (RankedHistoryTask.root q) := by
  have HP : 0 < (IntegralCriticalFlatActualLow.source F).rank q :=
    (Nat.zero_le _).trans_lt ((IntegralCriticalFlatActualLow.source F).row q).isLt
  exact (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ HP).trans
    (IntegralCriticalActualLowMatrixModel.dimension_cap F q hv))


theorem entry_replies (F : Scripts) (q : List Bool) (hv : valid F q) :
    IntegralCriticalFlatGenericProductEntryBits.RepliesAt F.toParameters
      (IntegralCriticalFlatActualLow.source F) (power F) q := by
  intro ha
  let S := IntegralCriticalFlatActualLow.source F
  let M := IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family S)
  let i := IntegralCriticalFlatGenericProductEntryBits.index F.toParameters S .row q
  let j := IntegralCriticalFlatGenericProductEntryBits.index F.toParameters S .col q
  have HA : i.divNat.val + 1 = j.divNat.val :=
    (MatrixProductBits.RecursiveStage.adjacent_packet M q i j).mp ha
  have HS : i.divNat.val < M.count q := by
    have HJ : j.divNat.val < (IntegralMonomialTermBits.family S).count q + 1 := j.divNat.isLt
    change i.divNat.val < (IntegralMonomialTermBits.family S).count q
    omega
  have HC : MatrixProductBits.factorQuery M
      (IntegralCriticalFlatGenericProductEntryBits.input F.toParameters S q) =
      IntegralMonomialTermBits.packet q i.divNat.val i.modNat.val j.modNat.val :=
    MatrixProductBits.RecursiveStage.factorQuery_packet M q i j
  change power F (IntegralCriticalFlatFactorQuery.writer F.toParameters .factorPower
      (MatrixProductBits.factorQuery M (IntegralCriticalFlatGenericProductEntryBits.input F.toParameters S q))) = _
  rw [HC]
  exact power_child_packet F .factorPower q i.divNat.val i.modNat.val j.modNat.val
    (HS.le.trans (count_cap F q hv)) i.modNat.isLt j.modNat.isLt

theorem entry_value (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F) (q : List Bool) (hv : valid F q) :
    (IntegralCriticalFlatGenericProductEntryBits.program F.toParameters (IntegralCriticalFlatActualLow.source F)).value
      (power F) (IntegralCriticalFlatGenericProductEntryBits.input F.toParameters (IntegralCriticalFlatActualLow.source F) q) =
      IntegralCriticalActualLowMatrixModel.productEntry F q := by
  have H := IntegralCriticalFlatGenericProductEntryBits.value_at F.toParameters (IntegralCriticalFlatActualLow.source F)
    (IntegralCriticalFlatActualLow.access F h) (power F) q (entry_replies F q hv)
  have HM : IntegralCriticalActualLowMatrixModel.productEntry F q =
      residueBits ((IntegralCriticalFlatGenericPowerBits.productFamily (IntegralCriticalFlatActualLow.source F)).matrix q
        (IntegralCriticalFlatGenericProductEntryBits.index F.toParameters (IntegralCriticalFlatActualLow.source F) .row q)
        (IntegralCriticalFlatGenericProductEntryBits.index F.toParameters (IntegralCriticalFlatActualLow.source F) .col q)) :=
    by
      unfold IntegralCriticalActualLowMatrixModel.productEntry IntegralCriticalActualLowMatrixModel.layeredEntry
        IntegralCriticalActualLowMatrixModel.dimension
      exact IntegralCriticalActualLowMatrixModel.entryBits_fin
        ((IntegralCriticalFlatGenericPowerBits.productFamily (IntegralCriticalFlatActualLow.source F)).matrix q)
        (IntegralCriticalFlatGenericProductEntryBits.index F.toParameters (IntegralCriticalFlatActualLow.source F) .row q)
        (IntegralCriticalFlatGenericProductEntryBits.index F.toParameters (IntegralCriticalFlatActualLow.source F) .col q)
  exact H.trans HM.symm

end LeanCanny.Algebra.IntegralCriticalActualProductEntryTransport
