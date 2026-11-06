/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPoint
public import LeanCanny.Encoding.IntegralFramedPhysicalBankChronologicalPoint
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarPoint
/-! # Provider interval order reads the actual own-word endpoint quotients -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem newest_env (b : IntegralFramedBankQuery.Bank) (tab : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents b.parameters b.plan b.data tab) (q w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input b) q w)
    (i : Fin ((IntegralMixedFramedBankSnapshotBits.atKey b.parameters b.plan b.data (b.key q)).count)) :
    IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state b.parameters b.plan b.data (b.key q))
      (IntegralFramedPhysicalSquare.scalarTuple b.parameters b.plan b.data b.nodes b.factor b.seed b.bounds
        b.key b.positive q w hw) i=
      IntegralFramedPhysicalBankTerm.env b tab hr q w hw
        ((IntegralMixedFramedBankSnapshotBits.atKey b.parameters b.plan b.data (b.key q)).count-1-i.val) := by
  have HC : (IntegralMixedFramedBankSnapshotBits.atKey b.parameters b.plan b.data (b.key q)).count=
      (family b.parameters b.plan b.data).birth (b.key q) := rfl
  rw [IntegralFramedPhysicalBankTerm.env_chronological b tab hr q w hw _ (by
    have HI := i.isLt
    omega),IntegralFramedPhysicalSquare.scalarTuple_point]
  apply congrArg (IntegralFramedPhysicalSquare.point b.parameters b.plan b.data b.nodes b.factor b.seed b.bounds b.key b.positive q w hw)
  apply Fin.ext
  have HI := i.isLt
  change i.val=(family b.parameters b.plan b.data).birth (b.key q)-1-
    ((IntegralMixedFramedBankSnapshotBits.atKey b.parameters b.plan b.data (b.key q)).count-1-i.val)
  omega

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank

noncomputable def endpoint (side : Bool) (q w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input q w)
    (hi : selected side q<count q) : ℝ :=
  IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state (B).parameters (B).plan (B).data ((B).key q))
    (IntegralFramedPhysicalSquare.scalarTuple (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive q w hw) ⟨selected side q,hi⟩

theorem endpoint_env (side : Bool) (q w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input q w)
    (hi : selected side q<count q) :
    endpoint side q w hw hi=FormulaSignSlotRadialProviderAtomic.bankField q w hw (count q-1-selected side q) :=
  newest_env B T FormulaSignSlotRadialProviderAtomic.bank_represents q w hw ⟨selected side q,hi⟩

theorem order_iff (q w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input q w)
    (hl : selected false q<count q) (hr : selected true q<count q) :
    order (pair q w)=InfinitesimalSign.encode 1 ↔ endpoint false q w hw hl<endpoint true q w hw hr := by
  unfold order
  rw [IntegralFramedPhysicalBankOrderSource.packet B (selected false) (selected true) T
    FormulaSignSlotRadialProviderAtomic.bank_represents q w [] hw hl hr]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans (sign_eq_one_iff.trans sub_pos)

theorem language_iff_comparison (q w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input q w)
    (hb : Bounds (pair q w)) (hg : Guards (pair q w)) :
    pair q w∈language ↔ pair q w∈comparison ∧
      endpoint false q w hw (by simpa only [pairFst_pair] using hb.1)<
      endpoint true q w hw (by simpa only [pairFst_pair] using hb.2.1) := by
  have HL : selected false q<count q := by simpa only [pairFst_pair] using hb.1
  have HR : selected true q<count q := by simpa only [pairFst_pair] using hb.2.1
  have HO := order_iff q w hw HL HR
  constructor
  · intro h
    exact ⟨h.1,HO.mp h.2.2.2.2⟩
  · rintro ⟨h,ho⟩
    refine ⟨h,?_,hb,hg,HO.mpr ho⟩
    simpa only [pairFst_pair,pairSnd_pair] using hw

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
