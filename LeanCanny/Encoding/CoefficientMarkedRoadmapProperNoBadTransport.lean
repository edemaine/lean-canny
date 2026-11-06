/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRoadmapProperNoBadLayout
public import LeanCanny.Encoding.CoefficientMarkedRoadmapAtomicCutoff
/-! # The actual proper NoBad guard on one shared atomic row curve -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRoadmapProperNoBadTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open CoefficientMarkedRoadmapProperNoBadLayout
open CoefficientMarkedRoadmapAtomicMetadata (reword)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def cutoff (q : List Bool) := CoefficientMarkedRoadmapBadProbeTransport.searchCutoff hn ht ha (request q)
theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  (CoefficientMarkedRoadmapBadProbeTransport.searchCutoff_binary hn ht ha).comp request_FP
theorem cutoff_reword (q w : List Bool) : cutoff hn ht ha (reword q w) = cutoff hn ht ha q :=
  congrArg (CoefficientMarkedRoadmapBadProbeTransport.searchCutoff hn ht ha) (request_reword q w)

theorem exists_envelope : ∃ g : List Bool → ℕ, BinaryFn g ∧ ∀ u q,
    q.length ≤ CoefficientMarkedRoadmapAtomicCutoff.allowance hn ht ha u → cutoff hn ht ha q ≤ g u :=
  (cutoff_binary hn ht ha).wordEnvelope (CoefficientMarkedRoadmapAtomicCutoff.allowance_unary hn ht ha)
noncomputable def envelope : List Bool → ℕ := Classical.choose (exists_envelope hn ht ha)
theorem envelope_binary : BinaryFn (envelope hn ht ha) := (Classical.choose_spec (exists_envelope hn ht ha)).1

theorem cutoff_le_envelope {R : List Bool → ℕ} (hR : BinaryFn R) (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR q) : cutoff hn ht ha q ≤ envelope hn ht ha (IntegralMixedRoadmapAtomic.original q) := by
  rw [← cutoff_reword hn ht ha q []]
  exact (Classical.choose_spec (exists_envelope hn ht ha)).2 _ _
    (CoefficientMarkedRoadmapAtomicCutoff.canonical_length hn ht ha hR q hv)

private theorem at_context (q c : List Bool)
    (hc : CoefficientMarkedRoadmapBadProbeTransport.leftContext q = c)
    {R0 S0 : List Bool → ℕ} (hR0 : BinaryFn R0) (hS0 : BinaryFn S0)
    (hRlarge : CoefficientMarkedRoadmapBadProbeTransport.searchCutoff hn ht ha q ≤ IntegralMixedOriginalRegularSource.radius R0 (pairFst c))
    (hSlarge : CoefficientMarkedRoadmapBadProbeTransport.searchCutoff hn ht ha q ≤ IntegralMixedOriginalRegularSource.radius S0 (pairFst c))
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRoadmapBadProbeTransport.searchCutoff hn ht ha q ≤ a)
    (s : Ioo a b) (x : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha c))
    (hx : ∀ y : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (pairFst c)
      (IntegralMixedCausalRecordPlanBits.count (pairFst c)) le_rfl y.val (x y))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (pairFst c))
    (hv : v.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius S0 (pairFst c))
    (w w' : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false) c w)
    (hw' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false) c w')
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false) c w hw).val (x u))
    (hz' : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false) c w' hw').val (x v)) :
    IntegralMixedRoadmapBadProbeSearch.NoBadProbe hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0)
      (CoefficientMarkedRoadmapBadProbeTransport.base q w) ↔
    IntegralMixedRoadmapBadProbeSearch.NoBadProbe hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0)
      (CoefficientMarkedRoadmapBadProbeTransport.base q w') := by
  cases hc
  exact CoefficientMarkedRoadmapBadProbeTransport.noBadProbe_on_curve hn ht ha hR0 hS0 q
    hRlarge hSlarge ha0 s x hx u v hu hv w w' hw hw' hz hz'

/-- The whole original proper NoBad predicate, with its actual sampled
word slot, transports on the SAME complete atomic row curve. -/
theorem noBad_on_curve (q : List Bool) {R0 S0 : List Bool → ℕ} (hR0 : BinaryFn R0) (hS0 : BinaryFn S0)
    (hRlarge : cutoff hn ht ha q ≤ IntegralMixedOriginalRegularSource.radius R0 (IntegralMixedRoadmapAtomic.root q))
    (hSlarge : cutoff hn ht ha q ≤ IntegralMixedOriginalRegularSource.radius S0 (IntegralMixedRoadmapAtomic.root q))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a) (s : Ioo a b)
    (x : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (IntegralMixedRoadmapAtomic.context q)))
    (hx : ∀ y : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedRoadmapAtomic.root q)
      (IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q)) le_rfl y.val (x y))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (IntegralMixedRoadmapAtomic.root q))
    (hv : v.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius S0 (IntegralMixedRoadmapAtomic.root q))
    (w' : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q))
    (hw' : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false)
      (IntegralMixedRoadmapAtomic.context q) w')
    (hz : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) hw).val (x u))
    (hz' : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false)
      (IntegralMixedRoadmapAtomic.context q) w' hw').val (x v)) :
    IntegralMixedRoadmapProper.NoBad hn ht ha hR0 q ↔ IntegralMixedRoadmapProper.NoBad hn ht ha hS0 (reword q w') := by
  have h := at_context hn ht ha (request q) (IntegralMixedRoadmapAtomic.context q) (leftContext_request q)
    hR0 hS0 hRlarge hSlarge ha0 s x hx u v hu hv (IntegralMixedRoadmapAtomic.word q) w' hw hw' hz hz'
  rw [base_source, base_reword] at h
  exact h

end LeanCanny.Encoding.CoefficientMarkedRoadmapProperNoBadTransport
