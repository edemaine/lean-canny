/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPoint
/-! # Concrete bidirectional provider critical and companion guard receipts -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank

theorem scalarValue_zero_iff_field (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid input c w)
    (b : ℕ) (hb : Active c b) :
    IntegralFramedPhysicalCompanionPoint.scalarValue B T bank_represents c w b=InfinitesimalSign.encode 0 ↔
      bankField c w hv b=geometricPoint c w hv b ⟨selected c b,selected_lt c b hb⟩ := by
  have H := IntegralFramedPhysicalCompanionPoint.scalarValue_zero_iff B T bank_represents c w hv b hb
  rw [IntegralFramedPhysicalCompanionPoint.retained_env] at H
  exact H

theorem companion_language_packet_iff (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid input c w)
    (a f k : ℕ) (hAnchor : Active c a)
    (hfit : f+k≤IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key c)) :
    pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k)∈Companions.language ↔
      ∀j<k, ∃hb : Active c (f+j), geometricPoint c w hv (f+j)=geometricPoint c w hv a ∧
        bankField c w hv (f+j)=geometricPoint c w hv a ⟨selected c (f+j),selected_lt c (f+j) hb⟩ := by
  have HG : Companions.Grammar (pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k)) := by
    refine ⟨IntegralMixedPhysicalPointCompanionScan.descriptor_packet c w a f k,?_,?_⟩
    · simpa only [Active,IntegralFramedPhysicalCompanionPoint.Active,IntegralMixedPhysicalPointCompanionScan.anchorQuery,
        IntegralMixedPhysicalPointCompanionScan.anchor,IntegralMixedPhysicalPointCompanionScan.descriptor,
        pairFst_pair,pairSnd_pair,List.length_replicate] using hAnchor
    · simpa only [IntegralMixedPhysicalPointCompanionScan.first,IntegralMixedPhysicalPointCompanionScan.number,
        IntegralMixedPhysicalPointCompanionScan.descriptor,pairFst_pair,pairSnd_pair,List.length_replicate] using hfit
  have HM : pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k)∈Companions.language ↔
      Companions.holds (pair (pair c w) (IntegralMixedPhysicalPointCompanionScan.descriptor a f k)) := by
    constructor
    · exact fun h => h.2.2
    · intro h
      refine ⟨?_,HG,h⟩
      simpa only [pairFst_pair,pairSnd_pair] using hv
  exact HM.trans (holds_iff_points c w hv a f k hAnchor)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
