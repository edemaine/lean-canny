/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionSemantics
/-! # The whole critical scan supplies every companion correlation -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCompanionScan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalPointCompanionScan
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool)

/-- The creating correlations are already part of the whole native critical
scan on this same word. Only the coordinate equalities remain to be checked. -/
theorem holds_iff_coordinates (ctx w : List Bool) (a f k : ℕ)
    (hscan : pair ctx w ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hR outer)
    (hfit : f + k ≤ IntegralMixedFramedHistoryFamilyBits.prefixLength
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer).parameters
      ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer).key
        (IntegralMixedPhysicalMarkedTest.sampleContext ctx))) :
    holds hn ht ha hR outer
      (pair (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) (descriptor a f k)) ↔
      ∀ j < k, ∀ i < dimension hn ht ha hR outer
        (pair (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w) (descriptor a f k)),
        IntegralMixedPhysicalPointEquality.Accepted hn ht ha hR outer
          (pair (pair (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w)
            (IntegralMixedPhysicalPointEquality.datum a (f + j) i)) := by
  have hs := (IntegralMixedPhysicalGuardScan.packet hn ht ha hR outer ctx w).mp hscan
  constructor
  · intro h j hj i hi
    have hji := (h j (by simpa only [number, descriptor, pairSnd_pair, List.length_replicate] using hj)).1 i hi
    simpa only [coordinateQuery_packet, anchor, first, descriptor, pairFst_pair,
      pairSnd_pair, List.length_replicate] using hji
  · intro h j hj
    have hjk : j < k := by
      simpa only [number, descriptor, pairSnd_pair, List.length_replicate] using hj
    refine ⟨?_, ?_⟩
    · intro i hi
      simpa only [coordinateQuery_packet, anchor, first, descriptor, pairFst_pair,
        pairSnd_pair, List.length_replicate] using h j hjk i hi
    · rw [correlation_packet]
      have hp : f + j < IntegralMixedFramedHistoryFamilyBits.prefixLength
          (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer).parameters
          ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer).key
            (IntegralMixedPhysicalMarkedTest.sampleContext ctx)) := by omega
      exact hs.2 (f + j) (by simpa only [pairFst_pair] using hp)

end LeanCanny.Encoding.CoefficientMarkedRecordCompanionScan
