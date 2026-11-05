/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalGuardScan
public import LeanCanny.Encoding.IntegralFramedPhysicalSquarePoint
/-! # Actual tuple incidence for the complete critical-correlation scan

The tuple predicate uses the installed guard polynomials and their literal
dimension casts. Complete sampling constructs its own word at the current
radius; no word from another sampler or radius is reused.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalIncidence
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank tables)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool)

noncomputable def source :=
  IntegralFramedPhysicalCriticalGuardTest.source (input hn ht ha hR outer)
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (tables hn ht ha hR outer) (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
    (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds (bank hn ht ha hR outer).key
    IntegralFramedPhysicalCriticalGuardScan.stage (IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR outer)

/-- Every creating stage is tested on the same full physical tuple. -/
noncomputable def CriticalZeros (ctx : List Bool)
    (z : Fin ((input hn ht ha hR outer).count (sampleContext ctx)) → ℝ) : Prop :=
  ∀ i < IntegralMixedFramedHistoryFamilyBits.prefixLength (bank hn ht ha hR outer).parameters
      ((bank hn ht ha hR outer).key (sampleContext ctx)),
    ((source hn ht ha hR outer).polynomial (sampleContext ctx) (List.replicate i true)).eval₂
      (Int.castRingHom ℝ) (fun j => z (Fin.cast
        ((source hn ht ha hR outer).dimension (sampleContext ctx) (List.replicate i true))
        (FixedWidthSuffixLiftBits.shift 0 j))) = 0

attribute [local irreducible] bank tables source IntegralMixedFramedHistoryFamilyBits.family

/-- The whole native scan is exactly the installed polynomial tests on its own decoded tuple. -/
theorem packet_iff (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w) :
    pair ctx w ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hR outer ↔
      CriticalZeros hn ht ha hR outer ctx
        (SquareSampleCompleteVertices.candidate (input hn ht ha hR outer) (sampleContext ctx) w hv).val := by
  rw [IntegralMixedPhysicalGuardScan.packet hn ht ha hR outer ctx w, and_iff_right hv]
  unfold CriticalZeros source
  exact IntegralFramedPhysicalCriticalGuardScan.holds_iff (input hn ht ha hR outer)
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (tables hn ht ha hR outer) (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
    (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds (bank hn ht ha hR outer).key
    (IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR outer) (sampleContext ctx) w hv

/-- Actual row roots and critical correlations admit one fresh, exact-width native word. -/
theorem exists_word_iff (ctx : List Bool)
    (z : Fin ((input hn ht ha hR outer).count (sampleContext ctx)) → ℝ) :
    ((∀ i, ((input hn ht ha hR outer).system (sampleContext ctx) i).eval₂ (Int.castRingHom ℝ) z = 0) ∧
      CriticalZeros hn ht ha hR outer ctx z) ↔
    ∃ w, ∃ hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w,
      w.length = SquareSampleCompleteVertices.width (input hn ht ha hR outer) (sampleContext ctx) ∧
      (SquareSampleCompleteVertices.candidate (input hn ht ha hR outer) (sampleContext ctx) w hv).val = z ∧
      pair ctx w ∈ IntegralMixedPhysicalGuardScan.language hn ht ha hR outer := by
  constructor
  · rintro ⟨hz, hc⟩
    let B := bank hn ht ha hR outer
    have hcomplete : SquareSampleComplete.Complete (input hn ht ha hR outer) :=
      IntegralFramedPhysicalSquare.complete B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive
    let root : SquareSampleComplete.Roots (input hn ht ha hR outer) (sampleContext ctx) := ⟨z, hz⟩
    let w := SquareSampleCompleteVertices.word (input hn ht ha hR outer) hcomplete (sampleContext ctx) root
    have hv := SquareSampleCompleteVertices.word_valid (input hn ht ha hR outer) hcomplete (sampleContext ctx) root
    have he := congrArg (fun r : SquareSampleComplete.Roots (input hn ht ha hR outer) (sampleContext ctx) => r.val)
      (SquareSampleCompleteVertices.candidate_word (input hn ht ha hR outer) hcomplete (sampleContext ctx) root)
    refine ⟨w, hv, (Classical.choose hv).1, he, ?_⟩
    apply (packet_iff hn ht ha hR outer ctx w hv).mpr
    exact he.symm ▸ hc
  · rintro ⟨w, hv, _, he, hc⟩
    refine ⟨?_, ?_⟩
    · exact he ▸ (SquareSampleCompleteVertices.candidate (input hn ht ha hR outer) (sampleContext ctx) w hv).property
    · exact he ▸ (packet_iff hn ht ha hR outer ctx w hv).mp hc

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalIncidence
