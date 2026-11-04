/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionSemantics
public import LeanCanny.Encoding.IntegralMixedPhysicalGuardScan
/-! # Exact completeness criterion for the all-critical native correlation scan

All values are read from one context and one complete full word. Inactive
integer/cut births contribute zero. Each actual critical birth compares its
own retained quotient and powered selected physical coordinate.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open IntegralFramedPhysicalCriticalGuardTest (keyDatum)
open IntegralFramedPhysicalCriticalGuardScan (stage)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term}
  (hn :UnaryFn n) (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R :List Bool→ℕ} (hR :BinaryFn R) (outer :Bool)
local notation "B"=>bank hn ht ha hR outer
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "T"=>tables hn ht ha hR outer
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer
local notation "HC"=>IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR outer
attribute [local irreducible] bank tables IntegralMixedFramedHistoryFamilyBits.family

theorem scalarValue_zero_inactive (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w)
    (b :ℕ) (hb :¬Active hn ht ha hR outer c b) :
    scalarValue hn ht ha hR outer c w b=InfinitesimalSign.encode 0:=by
  have HP:=IntegralFramedPhysicalCriticalGuardTest.packet S P (B).plan (B).data T
    (B).nodes (B).factor (B).seed (B).bounds (B).key stage HC c w (List.replicate b true) hv
  change scalarValue hn ht ha hR outer c w b=InfinitesimalSign.encode (SignType.sign
    ((IntegralMixedFramedCriticalGuardBits.polynomial P (B).plan (B).data T (keyDatum (B).key) stage
      (pair c (List.replicate b true))).eval₂ (Int.castRingHom ℝ)
        (fullTuple hn ht ha hR outer c w hv b))) at HP
  have HN :¬IntegralMixedFramedCriticalGuardBits.Active P T (keyDatum (B).key) stage
      (pair c (List.replicate b true)):=hb
  rw [IntegralMixedFramedCriticalGuardBits.polynomial,ite_eq_right HN,MvPolynomial.eval₂_zero,
    sign_zero] at HP
  exact HP

theorem critical_holds_iff (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w) :
    IntegralFramedPhysicalCriticalGuardScan.holds S P (B).plan (B).data T (B).nodes (B).factor (B).seed
      (B).bounds (B).key HC (pair c w) ↔
    ∀b, b<IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key c)→
      ∀hb :Active hn ht ha hR outer c b,
        retained hn ht ha hR outer c w hv b hb=
          geometricPoint hn ht ha hR outer c w hv b
            ⟨selected hn ht ha hR outer c b,selected_lt hn ht ha hR outer c b hb⟩:=by
  simp only [IntegralFramedPhysicalCriticalGuardScan.holds,pairFst_pair]
  change (∀b,b<IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key c)→
    scalarValue hn ht ha hR outer c w b=InfinitesimalSign.encode 0) ↔ _
  constructor
  · intro HH b hbound hb
    exact (scalarValue_zero_iff hn ht ha hR outer c w hv b hb).mp (HH b hbound)
  · intro HH b hbound
    by_cases hb :Active hn ht ha hR outer c b
    · exact (scalarValue_zero_iff hn ht ha hR outer c w hv b hb).mpr (HH b hbound hb)
    · exact scalarValue_zero_inactive hn ht ha hR outer c w hv b hb

theorem all_critical_packet_iff (ctx w :List Bool) :
    pair ctx w∈IntegralMixedPhysicalGuardScan.language hn ht ha hR outer ↔
      ∃hv :SquareSampleCompleteVertices.Valid S (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w,
        ∀b,b<IntegralMixedFramedHistoryFamilyBits.prefixLength P
          ((B).key (IntegralMixedPhysicalMarkedTest.sampleContext ctx))→
          ∀hb :Active hn ht ha hR outer (IntegralMixedPhysicalMarkedTest.sampleContext ctx) b,
            retained hn ht ha hR outer (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hv b hb=
              geometricPoint hn ht ha hR outer (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hv b
                ⟨selected hn ht ha hR outer (IntegralMixedPhysicalMarkedTest.sampleContext ctx) b,
                  selected_lt hn ht ha hR outer (IntegralMixedPhysicalMarkedTest.sampleContext ctx) b hb⟩:=by
  rw [IntegralMixedPhysicalGuardScan.packet hn ht ha hR outer ctx w]
  constructor
  · rintro ⟨hv,HH⟩
    exact ⟨hv,(critical_holds_iff hn ht ha hR outer _ w hv).mp HH⟩
  · rintro ⟨hv,HH⟩
    exact ⟨hv,(critical_holds_iff hn ht ha hR outer _ w hv).mpr HH⟩

end LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan
