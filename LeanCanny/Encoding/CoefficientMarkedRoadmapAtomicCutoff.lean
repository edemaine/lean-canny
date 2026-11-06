/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRoadmapAtomicMetadata
public import LeanCanny.Encoding.CoefficientMarkedRecordMarkedWordTransport
public import LeanCanny.Encoding.CoefficientMarkedProperCriticalRadiusTransport
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicSize
public import LeanCanny.Computation.WordResourceEnvelope
/-! # An original ceiling for every checked Atomic marked and NoCritical cutoff -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRoadmapAtomicCutoff
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedRoadmapAtomic
open CoefficientMarkedRoadmapAtomicMetadata (reword)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def canonical (q : List Bool) := reword q []
theorem canonical_FP : canonical ∈ FP := mem_FP_pair candidate_FP (mem_FP_pair payload_FP (constFn_mem_FP []))

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def cutoff (q : List Bool) :=
  CoefficientMarkedRecordMarkedWordTransport.cutoff hn ht ha (root q) +
    CoefficientMarkedProperCriticalRadiusTransport.cutoff hn ht ha q

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  BinaryFn.add ((CoefficientMarkedRecordMarkedWordTransport.cutoff_binary hn ht ha).comp root_FP)
    (CoefficientMarkedProperCriticalRadiusTransport.cutoff_binary hn ht ha)

private theorem noCritical_readers (q r : List Bool)
    (hc : candidate q = candidate r) (hp : payload q = payload r) :
    CoefficientMarkedProperCriticalRadiusTransport.cutoff hn ht ha q =
      CoefficientMarkedProperCriticalRadiusTransport.cutoff hn ht ha r := by
  have hq := CoefficientMarkedProperCriticalWordErasure.query_readers n q r hc hp
  have hctx := CoefficientMarkedProperCriticalWordErasure.context_readers n q r hc hp
  have hat := CoefficientMarkedProperCriticalWordErasure.atomic_context_readers q r hc hp
  unfold CoefficientMarkedProperCriticalRadiusTransport.cutoff
    CoefficientMarkedProperCriticalBranchTransport.cutoff CoefficientMarkedProperCriticalRadiusTransport.contextRoot
  rw [hq, hctx, hat]

/-- The numeric thresholds themselves erase the old sampled word; the
original resource envelope therefore has no circular dependence on it. -/
theorem cutoff_canonical (q : List Bool) : cutoff hn ht ha (canonical q) = cutoff hn ht ha q := by
  unfold cutoff canonical
  rw [CoefficientMarkedRoadmapAtomicMetadata.root_reword]
  rw [noCritical_readers hn ht ha (reword q []) q
    (CoefficientMarkedRoadmapAtomicMetadata.candidate_reword q [])
    (CoefficientMarkedRoadmapAtomicMetadata.payload_reword q [])]

noncomputable def allowance (u : List Bool) := 2 * IntegralMixedRoadmapWidth.candidateBudget hn ht ha u +
  2 * IntegralMixedRoadmapChain.payloadBudget (n u + 3) (n u + 8)
    (IntegralMixedRoadmapWidth.scalarBudget hn ht ha u) + 4

theorem allowance_unary : UnaryFn (allowance hn ht ha) :=
  (((UnaryFn.const 2).mul (IntegralMixedRoadmapWidth.candidateBudget_unary hn ht ha)).add
    ((UnaryFn.const 2).mul (IntegralMixedRoadmapChain.payloadBudget_unary
      (hn.add (UnaryFn.const 3)) (hn.add (UnaryFn.const 8))
      (IntegralMixedRoadmapWidth.scalarBudget_unary hn ht ha)))).add (UnaryFn.const 4)

theorem canonical_length {R : List Bool → ℕ} (hR : BinaryFn R) (q : List Bool)
    (hv : Valid hn ht ha hR q) : (canonical q).length ≤ allowance hn ht ha (original q) := by
  have hc := candidate_byte_bound hn ht ha hR q hv
  have hp := payload_byte_bound hn ht ha hR q hv
  simp only [canonical, reword, packet, pair_length, List.length_nil]
  unfold allowance
  omega

/-- This bounds the already proved marked/NoCritical sign cutoffs, uniformly
over every accepted checked table with this original input. -/
theorem exists_envelope : ∃ g : List Bool → ℕ, BinaryFn g ∧
    ∀ u q, q.length ≤ allowance hn ht ha u → cutoff hn ht ha q ≤ g u :=
  (cutoff_binary hn ht ha).wordEnvelope (allowance_unary hn ht ha)

noncomputable def envelope : List Bool → ℕ := Classical.choose (exists_envelope hn ht ha)
theorem envelope_binary : BinaryFn (envelope hn ht ha) := (Classical.choose_spec (exists_envelope hn ht ha)).1

theorem cutoff_le_envelope {R : List Bool → ℕ} (hR : BinaryFn R) (q : List Bool)
    (hv : Valid hn ht ha hR q) : cutoff hn ht ha q ≤ envelope hn ht ha (original q) := by
  rw [← cutoff_canonical hn ht ha q]
  exact (Classical.choose_spec (exists_envelope hn ht ha)).2 _ _ (canonical_length hn ht ha hR q hv)

end LeanCanny.Encoding.CoefficientMarkedRoadmapAtomicCutoff
