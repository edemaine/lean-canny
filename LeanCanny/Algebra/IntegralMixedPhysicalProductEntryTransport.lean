/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalFactorTransport
public import LeanCanny.Algebra.IntegralMixedPhysicalLayeredTransport
public import LeanCanny.Algebra.IntegralCriticalFlatGenericProductEntry
/-! # Adjacent layered-product entries call actual physical factor powers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalProductEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalMonomialBits IntegralMixedPhysicalFactorBits
open IntegralCriticalActualFactorModel (power_packet_natural)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalFlatFactorQuery.writer
theorem power_child (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) (s r t : ℕ)
    (hs : s ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root q))
    (hr : r < rank P F q) (ht : t < rank P F q) :
    power P F (IntegralCriticalFlatFactorQuery.writer P phase (IntegralMonomialTermBits.packet q s r t)) =
      powerEntry P F q s r t := by
  let child := IntegralCriticalFlatFactorQuery.writer P phase (IntegralMonomialTermBits.packet q s r t)
  have HR : RankedHistoryTask.root child = RankedHistoryTask.root q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using
      IntegralCriticalFlatFactorQuery.writer_root P phase (IntegralMonomialTermBits.packet q s r t)
  have HB : IntegralCriticalHistoryTask.birth P child = IntegralCriticalHistoryTask.birth P q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using IntegralCriticalFlatFactorQuery.writer_birth
      P phase (IntegralMonomialTermBits.packet q s r t)
  have HM : IntegralCriticalHistoryTask.modulus P child = IntegralCriticalHistoryTask.modulus P q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using IntegralCriticalFlatFactorQuery.writer_modulus
      P phase (IntegralMonomialTermBits.packet q s r t)
  have HF (f : IntegralCriticalHistoryTask.Field) (hrow : f ≠ .row) (hcol : f ≠ .col) (hslot : f ≠ .slot8) :
      IntegralCriticalHistoryTask.get P f child = IntegralCriticalHistoryTask.get P f q := by
    simpa only [child, IntegralMonomialTermBits.packet, pairFst_pair] using IntegralCriticalFlatFactorQuery.writer_other
      P phase (IntegralMonomialTermBits.packet q s r t) f hrow hcol hslot
  have HQ := IntegralCriticalFlatFactorQuery.writer_packet_fields P phase q s r t hs
    (hr.le.trans (rank_cap P F g q)) (ht.le.trans (rank_cap P F g q))
  change power P F child = _
  unfold power
  rw [HQ.1, HQ.2.1, HQ.2.2, rank_invariance P F q child HR HB (HF .slot15 (by decide) (by decide) (by decide)), Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt ht]
  exact power_invariance P F q child HR HB (HF .slot15 (by decide) (by decide) (by decide)) HM (HF .expression (by decide) (by decide) (by decide))
    (HF .derivative (by decide) (by decide) (by decide)) (HF .sourceIndex (by decide) (by decide) (by decide)) s r t

theorem power_child_packet (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F) (phase : IntegralCriticalHistoryTask.Phase) (q : List Bool) (s r t : ℕ)
    (hs : s ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root q))
    (hr : r < rank P F q) (ht : t < rank P F q) :
    power P F (IntegralCriticalFlatFactorQuery.writer P phase (IntegralMonomialTermBits.packet q s r t)) =
      (IntegralPowerProductBits.powerFamily (IntegralMonomialTermBits.family (source P F))).value
        (IntegralMonomialTermBits.packet q s r t) := by
  rw [power_child P F g phase q s r t hs hr ht]
  unfold IntegralMonomialTermBits.packet
  rw [power_packet_natural]
  have HRmod : r % (source P F).rank q = r := Nat.mod_eq_of_lt hr
  have HTmod : t % (source P F).rank q = t := Nat.mod_eq_of_lt ht
  rw [HRmod, HTmod]
  rfl

theorem count_cap (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F) (q : List Bool) :
    (IntegralMonomialTermBits.family (source P F)).count q ≤
      IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root q) := by
  have HP : 0 < (source P F).rank q :=
    (Nat.zero_le _).trans_lt ((source P F).row q).isLt
  exact (Nat.le_succ _).trans ((Nat.le_mul_of_pos_right _ HP).trans
    (IntegralMixedPhysicalLayeredBits.dimension_cap P F g q))


theorem entry_replies (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F) (q : List Bool) :
    IntegralCriticalFlatGenericProductEntryBits.RepliesAt P
      (source P F) (power P F) q := by
  intro ha
  let S := source P F
  let M := IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family S)
  let i := IntegralCriticalFlatGenericProductEntryBits.index P S .row q
  let j := IntegralCriticalFlatGenericProductEntryBits.index P S .col q
  have HA : i.divNat.val + 1 = j.divNat.val :=
    (MatrixProductBits.RecursiveStage.adjacent_packet M q i j).mp ha
  have HS : i.divNat.val < M.count q := by
    have HJ : j.divNat.val < (IntegralMonomialTermBits.family S).count q + 1 := j.divNat.isLt
    change i.divNat.val < (IntegralMonomialTermBits.family S).count q
    omega
  have HC : MatrixProductBits.factorQuery M
      (IntegralCriticalFlatGenericProductEntryBits.input P S q) =
      IntegralMonomialTermBits.packet q i.divNat.val i.modNat.val j.modNat.val :=
    MatrixProductBits.RecursiveStage.factorQuery_packet M q i j
  change power P F (IntegralCriticalFlatFactorQuery.writer P .factorPower
      (MatrixProductBits.factorQuery M (IntegralCriticalFlatGenericProductEntryBits.input P S q))) = _
  rw [HC]
  exact power_child_packet P F g .factorPower q i.divNat.val i.modNat.val j.modNat.val
    (HS.le.trans (count_cap P F g q)) i.modNat.isLt j.modNat.isLt

end LeanCanny.Algebra.IntegralMixedPhysicalProductEntryBits
