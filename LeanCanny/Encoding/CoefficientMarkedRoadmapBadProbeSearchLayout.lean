/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeSearchBudget
public import LeanCanny.Encoding.IntegralMixedOriginalRegularSource
/-! # Actual bounded hint bytes are independent of the radius and OWN word -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeTransport
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def hint (q bits : List Bool) := IntegralMixedRoadmapBadProbeSearch.hintPacket hn ht ha (BinaryFn.const 0) (pair (canonical q) bits)

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapBadProbeTest.dimension IntegralMixedRoadmapBadProbeTest.width

variable {R : List Bool → ℕ} (hR : BinaryFn R)

theorem blockWidth_base (q word : List Bool) :
    IntegralMixedRoadmapBadProbeSearch.blockWidth hn ht ha hR (base q word) =
      IntegralMixedRoadmapBadProbeSearch.blockWidth hn ht ha (BinaryFn.const 0) (canonical q) := by
  have HW := CoefficientMarkedRoadmapBadProbeMetadata.width_request hn ht ha hR (BinaryFn.const 0)
    (IntegralMixedRoadmapBadProbePacket.candidate (pairFst q)) (IntegralMixedRoadmapBadProbePacket.raw (pairFst q))
    (IntegralMixedRoadmapBadProbePacket.labels (pairFst q))
    (pairFst (IntegralMixedRoadmapBadProbePacket.endpoints (pairFst q)))
    (pairSnd (IntegralMixedRoadmapBadProbePacket.endpoints (pairFst q))) [] word []
  have HD := CoefficientMarkedRoadmapBadProbeMetadata.dimension_request hn ht ha hR (BinaryFn.const 0)
    (IntegralMixedRoadmapBadProbePacket.candidate (pairFst q)) (IntegralMixedRoadmapBadProbePacket.raw (pairFst q))
    (IntegralMixedRoadmapBadProbePacket.labels (pairFst q))
    (pairFst (IntegralMixedRoadmapBadProbePacket.endpoints (pairFst q)))
    (pairSnd (IntegralMixedRoadmapBadProbePacket.endpoints (pairFst q))) [] word []
  exact congrArg₂ (fun B d : ℕ => B+d+2) HW HD

theorem hintWidth_base (q word : List Bool) :
    IntegralMixedRoadmapBadProbeSearch.hintWidth hn ht ha hR (base q word) =
      IntegralMixedRoadmapBadProbeSearch.hintWidth hn ht ha (BinaryFn.const 0) (canonical q) :=
  congrArg (fun k : ℕ => 4*k) (blockWidth_base hn ht ha hR q word)

/-- The same bits produce exactly the same four-number hint, while the OWN
sampled base word remains in its actual native slot. -/
theorem hintPacket_base (q word bits : List Bool) :
    IntegralMixedRoadmapBadProbeSearch.hintPacket hn ht ha hR (pair (base q word) bits) = request (hint hn ht ha q bits) word := by
  unfold IntegralMixedRoadmapBadProbeSearch.hintPacket IntegralMixedRoadmapBadProbeSearch.block hint
  simp only [pairFst_pair, pairSnd_pair, blockWidth_base hn ht ha hR q word]
  simp only [request, CoefficientMarkedRoadmapBadProbeMetadata.request,
    IntegralMixedRoadmapBadProbeSearch.hintPacket, IntegralMixedRoadmapBadProbeSearch.block, pairFst_pair, pairSnd_pair,
    canonical, base, IntegralMixedRoadmapBadProbePacket.packet,
    IntegralMixedRoadmapBadProbePacket.candidate, IntegralMixedRoadmapBadProbePacket.raw,
    IntegralMixedRoadmapBadProbePacket.labels, IntegralMixedRoadmapBadProbePacket.endpoints]

theorem leftContext_hint (q bits : List Bool) : leftContext (hint hn ht ha q bits) = leftContext q := by
  simp only [leftContext, baseRoot, hint, IntegralMixedRoadmapBadProbeSearch.hintPacket,
    IntegralMixedRoadmapBadProbePacket.root, canonical, base, IntegralMixedRoadmapBadProbePacket.packet,
    IntegralMixedRoadmapBadProbePacket.candidate, IntegralMixedRoadmapBadProbePacket.raw, pairFst_pair, pairSnd_pair]

theorem roots_original (q : List Bool) :
    IntegralMixedAuxiliaryMarkedIntegerSource.original (leftRoot q) =
      IntegralMixedAuxiliaryMarkedIntegerSource.original (rightRoot n q) := by
  rw [leftRoot_eq, rightRoot_eq]
  unfold IntegralMixedAuxiliaryMarkedIntegerSource.original IntegralMixedAuxiliaryMarkedIntegerSource.candidate
    baseRoot preparedRoot
  rw [IntegralMixedRoadmapBadProbePacket.prepared_candidate]
  simp only [IntegralMixedRoadmapBadProbePacket.root, anchor, request, CoefficientMarkedRoadmapBadProbeMetadata.request,
    IntegralMixedRoadmapBadProbePacket.packet, IntegralMixedRoadmapBadProbePacket.candidate, pairFst_pair]

theorem radius_common (R0 : List Bool → ℕ) (q : List Bool) :
    IntegralMixedOriginalRegularSource.radius R0 (leftRoot q) =
      IntegralMixedOriginalRegularSource.radius R0 (rightRoot n q) :=
  congrArg R0 (roots_original (n := n) q)

end LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeTransport
