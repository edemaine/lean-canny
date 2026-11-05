/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeSearchLayout
/-! # ALL native NoBad hints on one actual base-root curve -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)

private theorem at_context (q c : List Bool) (hc : leftContext q = c)
    (hReq : R (pairFst c) = R (rightRoot n q)) (hSeq : S (pairFst c) = S (rightRoot n q))
    (hRc : cutoff hn ht ha q ≤ R (pairFst c)) (hSc : cutoff hn ht ha q ≤ S (pairFst c))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a) (s : Ioo a b)
    (x : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha c))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (pairFst c)
      (IntegralMixedCausalRecordPlanBits.count (pairFst c)) le_rfl u.val (x u))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R (pairFst c)) (hv : v.val = (2 : ℝ)^S (pairFst c))
    (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) c wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) c wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) c wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) c wS hwS).val (x v)) :
    IntegralMixedRoadmapBadProbeTest.HasWitness hn ht ha hR (request q wR) ↔
      IntegralMixedRoadmapBadProbeTest.HasWitness hn ht ha hS (request q wS) := by
  cases hc
  exact hasWitness_on_curve hn ht ha hR hS q hReq hSeq hRc hSc ha0 s x hx u v hu hv wR wS hwR hwS hjR hjS

variable {R0 S0 : List Bool → ℕ} (hR0 : BinaryFn R0) (hS0 : BinaryFn S0)

/-- The literal bounded NoBad search is preserved, including EVERY hint and
ALL prepared native words. One original Binary cutoff suffices; all prepared
families, fresh OWN widths, metadata and native predicates are derived.
Only the SAME actual base curve and its two OWN words are supplied. -/
theorem noBadProbe_on_curve (q : List Bool)
    (hRc : searchCutoff hn ht ha q ≤ IntegralMixedOriginalRegularSource.radius R0 (leftRoot q))
    (hSc : searchCutoff hn ht ha q ≤ IntegralMixedOriginalRegularSource.radius S0 (leftRoot q))
    {a b : ℝ} (ha0 : (2 : ℝ)^searchCutoff hn ht ha q ≤ a) (s : Ioo a b)
    (x : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (leftContext q)))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (leftRoot q)
      (IntegralMixedCausalRecordPlanBits.count (leftRoot q)) le_rfl u.val (x u))
    (u v : Ioo a b)
    (hu : u.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (leftRoot q))
    (hv : v.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius S0 (leftRoot q))
    (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false) (leftContext q) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false) (leftContext q) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false) (leftContext q) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false) (leftContext q) wS hwS).val (x v)) :
    IntegralMixedRoadmapBadProbeSearch.NoBadProbe hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) (base q wR) ↔
      IntegralMixedRoadmapBadProbeSearch.NoBadProbe hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) (base q wS) := by
  have H : IntegralMixedRoadmapBadProbeSearch.HasBadProbe hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) (base q wR) ↔
      IntegralMixedRoadmapBadProbeSearch.HasBadProbe hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) (base q wS) := by
    unfold IntegralMixedRoadmapBadProbeSearch.HasBadProbe
    rw [hintWidth_base hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) q wR,
      hintWidth_base hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) q wS]
    apply exists_congr
    intro bits
    apply and_congr_right
    intro hlen
    rw [hintPacket_base hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) q wR bits,
      hintPacket_base hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) q wS bits]
    have hctx := leftContext_hint hn ht ha q bits
    have HR := radius_common (n := n) R0 (hint hn ht ha q bits)
    have HS := radius_common (n := n) S0 (hint hn ht ha q bits)
    change IntegralMixedOriginalRegularSource.radius R0 (pairFst (leftContext (hint hn ht ha q bits))) = _ at HR
    change IntegralMixedOriginalRegularSource.radius S0 (pairFst (leftContext (hint hn ht ha q bits))) = _ at HS
    rw [hctx] at HR HS
    have hbudget := hint_cutoff_le hn ht ha q bits hlen
    have hstart := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hbudget).trans ha0
    exact at_context hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) (IntegralMixedOriginalRegularSource.radius_binary hS0)
      (hint hn ht ha q bits) (leftContext q) hctx HR HS (hbudget.trans hRc) (hbudget.trans hSc)
      hstart s x hx u v hu hv wR wS hwR hwS hjR hjS
  exact H.not

end LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeTransport
