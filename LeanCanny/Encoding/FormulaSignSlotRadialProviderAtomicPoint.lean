/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicValid
public import LeanCanny.Encoding.IntegralFramedPhysicalCompanionFields
/-! # The accepted provider atomic point and its actual captured coordinates -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank

theorem full_valid (q : List Bool) (hv : Valid q) : SquareSampleCompleteVertices.Valid input (context q) (word q) :=
  valid_full q hv
theorem context_root (q : List Bool) : pairFst ((B).key (context q))=root q := by
  unfold FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.bankKey context
  simp only [IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair]
theorem native_dimension (q : List Bool) : (P).ambient (pairFst ((B).key (context q)))=dimension q := by
  rw [context_root]
  rfl

noncomputable abbrev Active := IntegralFramedPhysicalCompanionPoint.Active B T
noncomputable abbrev selected := IntegralFramedPhysicalCompanionPoint.selected B T
noncomputable abbrev geometricPoint := IntegralFramedPhysicalCompanionPoint.geometricPoint B T
noncomputable abbrev bankField := IntegralFramedPhysicalBankTerm.env B T bank_represents
theorem selected_lt (c : List Bool) (b : ℕ) (hb : Active c b) : selected c b<(P).ambient (pairFst ((B).key c))+1 :=
  IntegralFramedPhysicalCompanionPoint.selected_lt B T bank_represents c b hb
noncomputable def field (q : List Bool) (hv : Valid q) (label : ℕ) :=
  bankField (context q) (word q) (full_valid q hv) label
noncomputable def point (q : List Bool) (hv : Valid q) :=
  geometricPoint (context q) (word q) (full_valid q hv) (anchor (dimension q) (initial q) q)

theorem anchor_active_packet (c w : List Bool) (a f k : ℕ)
    (h : pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k)∈Companions.language) : Active c a := by
  have H := h.2.1.2.1
  simpa only [Active,IntegralFramedPhysicalCompanionPoint.Active,
    IntegralMixedPhysicalPointCompanionScan.anchorQuery,IntegralMixedPhysicalPointCompanionScan.anchor,
    IntegralMixedPhysicalPointCompanionScan.descriptor,pairFst_pair,pairSnd_pair,List.length_replicate] using H
theorem anchor_active (q : List Bool) (hv : Valid q) : Active (context q) (anchor (dimension q) (initial q) q) :=
  anchor_active_packet (context q) (word q) _ _ _ (valid_companions q hv)

private theorem correlation_packet (c w : List Bool) (a f k j : ℕ) :
    Companions.correlation (pair (pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k))
      (List.replicate j true))=IntegralFramedPhysicalCompanionPoint.scalarValue B T bank_represents c w (f+j) := by
  simp only [Companions.correlation,Function.comp_apply,IntegralMixedPhysicalPointCompanionScan.correlationQuery,
    IntegralMixedPhysicalPointCompanionScan.first,IntegralMixedPhysicalPointCompanionScan.descriptor,
    IntegralFramedPhysicalCompanionPoint.scalarValue,pairFst_pair,pairSnd_pair,List.length_replicate]

private theorem equality_zero_iff (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid input c w) (a b i : ℕ)
    (h : Companions.PointAdmissible (pair (pair c w) (IntegralMixedPhysicalPointEquality.datum a b i))) :
    Companions.pointValue (pair (pair c w) (IntegralMixedPhysicalPointEquality.datum a b i))=InfinitesimalSign.encode 0 ↔
      IntegralFramedPhysicalCompanionPoint.block B T c w hv a i=
        IntegralFramedPhysicalCompanionPoint.block B T c w hv b i :=
  IntegralFramedPhysicalCompanionPoint.pointValue_zero_iff_block B T bank_represents c w hv a b i h

private theorem admissible_iff (c w : List Bool) (a b i : ℕ) :
    Companions.PointAdmissible (pair (pair c w) (IntegralMixedPhysicalPointEquality.datum a b i)) ↔
      Active c a ∧ Active c b ∧ i<(P).ambient (pairFst ((B).key c))+1 :=
  IntegralFramedPhysicalCompanionPoint.admissible_packet_iff B T c w a b i

private theorem scalar_zero_iff (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid input c w)
    (b : ℕ) (hb : Active c b) :
    IntegralFramedPhysicalCompanionPoint.scalarValue B T bank_represents c w b=InfinitesimalSign.encode 0 ↔
      bankField c w hv b=geometricPoint c w hv b ⟨selected c b,selected_lt c b hb⟩ := by
  have H := IntegralFramedPhysicalCompanionPoint.scalarValue_zero_iff B T bank_represents c w hv b hb
  rw [IntegralFramedPhysicalCompanionPoint.retained_env] at H
  exact H

theorem holds_iff_points (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid input c w)
    (a f k : ℕ) (hAnchor : Active c a) :
    Companions.holds (pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k)) ↔
      ∀j<k, ∃hb : Active c (f+j), geometricPoint c w hv (f+j)=geometricPoint c w hv a ∧
        bankField c w hv (f+j)=geometricPoint c w hv a ⟨selected c (f+j),selected_lt c (f+j) hb⟩ := by
  have HH : Companions.holds (pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k)) ↔
      ∀j<k, (∀i<(P).ambient (pairFst ((B).key c))+1, Companions.PointAccepted
        (pair (pair c w) (IntegralMixedPhysicalPointEquality.datum a (f+j) i))) ∧
        IntegralFramedPhysicalCompanionPoint.scalarValue B T bank_represents c w (f+j)=InfinitesimalSign.encode 0 := by
    simp only [Companions.holds]
    simp_rw [correlation_packet]
    simp only [IntegralMixedPhysicalPointCompanionScan.number,IntegralMixedPhysicalPointCompanionScan.descriptor,
      Companions.dimension,IntegralMixedPhysicalPointCompanionScan.coordinateQuery_packet,
      IntegralMixedPhysicalPointCompanionScan.anchor,IntegralMixedPhysicalPointCompanionScan.first,
      pairFst_pair,pairSnd_pair,List.length_replicate]
  rw [HH]
  constructor
  · intro H j hj
    have HJ := H j hj
    have H0 := HJ.1 0 (Nat.zero_lt_succ _)
    have HB := ((admissible_iff c w a (f+j) 0).mp H0.2.1).2.1
    have HE : geometricPoint c w hv (f+j)=geometricPoint c w hv a := by
      funext i
      have HI := HJ.1 i.val i.isLt
      exact ((equality_zero_iff c w hv a (f+j) i.val HI.2.1).mp HI.2.2).symm
    exact ⟨HB,HE,((scalar_zero_iff c w hv (f+j) HB).mp HJ.2).trans
      (congrFun HE ⟨selected c (f+j),selected_lt c (f+j) HB⟩)⟩
  · intro H j hj
    obtain ⟨HB,HE,HR⟩ := H j hj
    refine ⟨fun i hi => ?_,?_⟩
    · have HA := (admissible_iff c w a (f+j) i).mpr ⟨hAnchor,HB,hi⟩
      refine ⟨IntegralMixedPhysicalPointEquality.wellformed_packet c w a (f+j) i,HA,?_⟩
      exact (equality_zero_iff c w hv a (f+j) i HA).mpr (congrFun HE ⟨i,hi⟩).symm
    · exact (scalar_zero_iff c w hv (f+j) HB).mpr
        (HR.trans (congrFun HE ⟨selected c (f+j),selected_lt c (f+j) HB⟩).symm)

theorem companions (q : List Bool) (hv : Valid q) : ∀j<free (dimension q) q,
    ∃hb : Active (context q) (first (dimension q) (initial q) q+j),
      geometricPoint (context q) (word q) (full_valid q hv) (first (dimension q) (initial q) q+j)=point q hv ∧
      field q hv (first (dimension q) (initial q) q+j)=
        point q hv ⟨selected (context q) (first (dimension q) (initial q) q+j),
          selected_lt _ _ hb⟩ :=
  (holds_iff_points (context q) (word q) (full_valid q hv) _ _ _ (anchor_active q hv)).mp
    (valid_companions q hv).2.2

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
