/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedProperCriticalBranchTransport
public import LeanCanny.Encoding.CoefficientMarkedProperCriticalWordErasure
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalScanTransport
/-! # Fresh own-word transport of actual native NoCritical -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedProperCriticalRadiusTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def replaceWord (q w : List Bool) :=
  IntegralMixedRoadmapAtomic.packet (IntegralMixedRoadmapAtomic.candidate q) (IntegralMixedRoadmapAtomic.payload q) w

abbrev contextRoot (q : List Bool) := pairFst (IntegralMixedRoadmapAtomic.context q)

theorem candidate_replace (q w : List Bool) :
    IntegralMixedRoadmapAtomic.candidate (replaceWord q w) = IntegralMixedRoadmapAtomic.candidate q := by
  unfold replaceWord IntegralMixedRoadmapAtomic.packet IntegralMixedRoadmapAtomic.candidate
  exact pairFst_pair _ _

theorem payload_replace (q w : List Bool) :
    IntegralMixedRoadmapAtomic.payload (replaceWord q w) = IntegralMixedRoadmapAtomic.payload q := by
  simp only [replaceWord, IntegralMixedRoadmapAtomic.packet, IntegralMixedRoadmapAtomic.payload, pairFst_pair, pairSnd_pair]

theorem word_replace (q w : List Bool) : IntegralMixedRoadmapAtomic.word (replaceWord q w) = w := by
  simp only [replaceWord, IntegralMixedRoadmapAtomic.packet, IntegralMixedRoadmapAtomic.word, pairSnd_pair]

theorem original_replace (q w : List Bool) : IntegralMixedRoadmapAtomic.original (replaceWord q w) =
    IntegralMixedRoadmapAtomic.original q := congrArg pairFst (candidate_replace q w)

private theorem contextRoot_eq (q : List Bool) : contextRoot q = IntegralMixedRoadmapAtomic.root q := by
  unfold contextRoot IntegralMixedRoadmapAtomic.context
  exact pairFst_pair _ _

private theorem sample_context (q : List Bool) :
    IntegralMixedPhysicalMarkedTest.sampleContext (contextRoot q) = IntegralMixedRoadmapAtomic.context q := by
  rw [contextRoot_eq]
  rfl

private theorem sample_replace_context (q w : List Bool) :
    IntegralMixedPhysicalMarkedTest.sampleContext (contextRoot q) = IntegralMixedRoadmapAtomic.context (replaceWord q w) :=
  (sample_context q).trans (CoefficientMarkedProperCriticalWordErasure.atomic_context_readers q (replaceWord q w)
    (candidate_replace q w).symm (payload_replace q w).symm)

private theorem radius_context (R0 : List Bool → ℕ) (q : List Bool) :
    IntegralMixedOriginalRegularSource.radius R0 (contextRoot q) = R0 (IntegralMixedRoadmapAtomic.original q) := by
  rw [contextRoot_eq]
  unfold IntegralMixedOriginalRegularSource.radius IntegralMixedAuxiliaryMarkedIntegerSource.original
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate IntegralMixedRoadmapAtomic.root IntegralMixedRoadmapAtomic.original
  rw [pairFst_pair]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def cutoff (q : List Bool) := CoefficientMarkedProperCriticalBranchTransport.cutoff hn ht ha q +
  CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha (contextRoot q) +
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root (CoefficientMarkedProperCriticalPredicate.query n q)) + 1

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) := by
  have hc : contextRoot ∈ FP := mem_FP_comp IntegralMixedRoadmapAtomic.context_FP pairFst_mem_FP
  have hp : (fun q => IntegralMixedPhysicalCriticalQuery.root (CoefficientMarkedProperCriticalPredicate.query n q)) ∈ FP :=
    CoefficientMarkedProperCriticalLayout.root_FP hn
  exact ((BinaryFn.add (CoefficientMarkedProperCriticalBranchTransport.cutoff_binary hn ht ha)
    ((CoefficientMarkedRecordCriticalBranchSign.cutoff_binary hn ht ha).comp hc)).add
    ((CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff_binary hn ht ha).comp hp)).add (BinaryFn.const 1)

private theorem branch_cutoff_le (q : List Bool) : CoefficientMarkedProperCriticalBranchTransport.cutoff hn ht ha q ≤ cutoff hn ht ha q := by
  unfold cutoff
  omega

private theorem critical_cutoff_le (q : List Bool) :
    CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha (contextRoot q) ≤ cutoff hn ht ha q := by
  unfold cutoff
  omega

private theorem old_effective_le (q : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (IntegralMixedRoadmapAtomic.root q) ≤ cutoff hn ht ha q := by
  rw [← contextRoot_eq q]
  exact ((CoefficientMarkedRecordCartesianRows.effectiveCutoff_le hn ht ha _).trans
    (CoefficientMarkedRecordCriticalBranchSign.row_cutoff_le hn ht ha _)).trans (critical_cutoff_le hn ht ha q)

private theorem prepared_effective_le (q : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root (CoefficientMarkedProperCriticalPredicate.query n q)) ≤ cutoff hn ht ha q := by
  unfold cutoff
  omega

private theorem valid_at (I : SquareSampleInput.Inputs) (q r w v : List Bool) (hc : q = r) (hw : w = v)
    (hv : SquareSampleCompleteVertices.Valid I q w) : SquareSampleCompleteVertices.Valid I r v := by
  subst r
  subst v
  exact hv

private theorem candidate_at (I : SquareSampleInput.Inputs) (q r w v : List Bool) (hc : q = r) (hw : w = v)
    (hq : SquareSampleCompleteVertices.Valid I q w) (hr : SquareSampleCompleteVertices.Valid I r v) :
    HEq (SquareSampleCompleteVertices.candidate I q w hq).val (SquareSampleCompleteVertices.candidate I r v hr).val := by
  subst r
  subst v
  rfl

private theorem cast_heq {A B : Type} (h : A = B) (x : A) : HEq (Eq.mp h x) x := by
  cases h
  rfl

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic cutoff
  CoefficientMarkedProperCriticalPredicate.query CoefficientMarkedProperCriticalPredicate.context
  IntegralMixedRoadmapAtomic.context IntegralMixedRoadmapAtomic.root

/-- One actual original-root curve and a freshly sampled OWN target word
preserve the ENTIRE native NoCritical predicate and the entire critical scan.
Both prepared witnesses and every quantified child root are handled internally. -/
theorem transport_on_interval (q : List Bool) {R0 S0 : List Bool → ℕ} (hR0 : BinaryFn R0) (hS0 : BinaryFn S0)
    (hRlarge : cutoff hn ht ha q ≤ R0 (IntegralMixedRoadmapAtomic.original q))
    (hSlarge : cutoff hn ht ha q ≤ S0 (IntegralMixedRoadmapAtomic.original q))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a) (s u v : Ioo a b)
    (hu : u.val = (2 : ℝ)^R0 (IntegralMixedRoadmapAtomic.original q))
    (hv : v.val = (2 : ℝ)^S0 (IntegralMixedRoadmapAtomic.original q))
    (ho : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)) :
    ∃ x : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (IntegralMixedRoadmapAtomic.context q)),
      (∀ t : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (contextRoot q)
        (IntegralMixedCausalRecordPlanBits.count (contextRoot q)) le_rfl t.val (x t)) ∧
      HEq (SquareSampleCompleteVertices.candidate
        (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
        (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) ho).val (x u) ∧
      ∃ w, ∃ hTargetWord : SquareSampleCompleteVertices.Valid
        (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false)
        (IntegralMixedRoadmapAtomic.context (replaceWord q w)) (IntegralMixedRoadmapAtomic.word (replaceWord q w)),
        w.length = SquareSampleCompleteVertices.width
          (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false)
          (IntegralMixedRoadmapAtomic.context (replaceWord q w)) ∧
        HEq (SquareSampleCompleteVertices.candidate
          (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false)
          (IntegralMixedRoadmapAtomic.context (replaceWord q w)) (IntegralMixedRoadmapAtomic.word (replaceWord q w)) hTargetWord).val (x v) ∧
        (IntegralMixedRoadmapProperCritical.NoCritical hn ht ha hR0 q ↔
          IntegralMixedRoadmapProperCritical.NoCritical hn ht ha hS0 (replaceWord q w)) ∧
        (IntegralMixedRoadmapAtomic.fullQuery q ∈ IntegralMixedPhysicalGuardScan.language hn ht ha
            (IntegralMixedOriginalRegularSource.radius_binary hR0) false ↔
          IntegralMixedRoadmapAtomic.fullQuery (replaceWord q w) ∈ IntegralMixedPhysicalGuardScan.language hn ht ha
            (IntegralMixedOriginalRegularSource.radius_binary hS0) false) := by
  have hRC : CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha (contextRoot q) ≤
      IntegralMixedOriginalRegularSource.radius R0 (contextRoot q) := by
    rw [radius_context]
    exact (critical_cutoff_le hn ht ha q).trans hRlarge
  have hSC : CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha (contextRoot q) ≤
      IntegralMixedOriginalRegularSource.radius S0 (contextRoot q) := by
    rw [radius_context]
    exact (critical_cutoff_le hn ht ha q).trans hSlarge
  have hstart : (2 : ℝ)^CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha (contextRoot q) ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (critical_cutoff_le hn ht ha q)).trans ha0
  have hs := valid_at _ _ _ _ _ (sample_context q).symm rfl ho
  have hru : u.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (contextRoot q) := by
    rw [radius_context]
    exact hu
  have hrv : v.val = (2 : ℝ)^IntegralMixedOriginalRegularSource.radius S0 (contextRoot q) := by
    rw [radius_context]
    exact hv
  obtain ⟨x, hx, heU, w, hw, hlen, heV, hscan⟩ := CoefficientMarkedRecordCriticalScanTransport.transport_on_interval hn ht ha
    (contextRoot q) (IntegralMixedOriginalRegularSource.radius_binary hR0) (IntegralMixedOriginalRegularSource.radius_binary hS0)
    hRC hSC hstart s u v hru hrv (IntegralMixedRoadmapAtomic.word q) hs
  have hsource := (candidate_at _ _ _ _ _ (sample_context q).symm rfl ho hs).trans heU
  have htarget := valid_at _ _ _ _ _ (sample_replace_context q w) (word_replace q w).symm hw
  have htargetPoint := (candidate_at _ _ _ _ _ (sample_replace_context q w).symm (word_replace q w) htarget hw).trans heV
  have hc := (candidate_replace q w).symm
  have hp := (payload_replace q w).symm
  have hctx := CoefficientMarkedProperCriticalWordErasure.atomic_context_readers q (replaceWord q w) hc hp
  have hpointType := congrArg (CoefficientMarkedRecordFieldListIncidence.Point hn ht ha) hctx
  let targetPoint := Eq.mp hpointType (x v)
  have hpoint : HEq (x v) targetPoint := (cast_heq hpointType (x v)).symm
  have hquery := CoefficientMarkedProperCriticalWordErasure.query_readers n q (replaceWord q w) hc hp
  have hroot : IntegralMixedRoadmapAtomic.root (replaceWord q w) = IntegralMixedRoadmapAtomic.root q := by
    unfold IntegralMixedRoadmapAtomic.root
    rw [candidate_replace, payload_replace]
  have hSrc := CoefficientMarkedProperCriticalPredicate.noCritical_iff hn ht ha hR0 q
    ((old_effective_le hn ht ha q).trans hRlarge) ((prepared_effective_le hn ht ha q).trans hRlarge) ho (x u) hsource
  have hTgt := CoefficientMarkedProperCriticalPredicate.noCritical_iff hn ht ha hS0 (replaceWord q w)
    (by rw [hroot, original_replace]; exact (old_effective_le hn ht ha q).trans hSlarge)
    (by rw [← hquery, original_replace]; exact (prepared_effective_le hn ht ha q).trans hSlarge)
    htarget targetPoint (htargetPoint.trans hpoint)
  have hBranch : (2 : ℝ)^CoefficientMarkedProperCriticalBranchTransport.cutoff hn ht ha q ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (branch_cutoff_le hn ht ha q)).trans ha0
  have hFormula := CoefficientMarkedProperCriticalBranchTransport.holds_on_root_curve hn ht ha q hBranch x hx u v
  have hErase := CoefficientMarkedProperCriticalWordErasure.holds_readers_iff hn ht ha q (replaceWord q w) hc hp v.val
    (x v) targetPoint hpoint
  rw [original_replace] at hTgt
  rw [← hu] at hSrc
  rw [← hv] at hTgt
  have hwidth : SquareSampleCompleteVertices.width
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false)
      (IntegralMixedPhysicalMarkedTest.sampleContext (contextRoot q)) =
      SquareSampleCompleteVertices.width
        (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false)
        (IntegralMixedRoadmapAtomic.context (replaceWord q w)) :=
    congrArg (SquareSampleCompleteVertices.width
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false))
        (sample_replace_context q w)
  refine ⟨x, hx, hsource, w, htarget, hlen.trans hwidth, htargetPoint,
    hSrc.trans (hFormula.trans (hErase.trans hTgt.symm)), ?_⟩
  have hSourcePacket : IntegralMixedRoadmapAtomic.fullQuery q = pair (contextRoot q) (IntegralMixedRoadmapAtomic.word q) := by
    unfold IntegralMixedRoadmapAtomic.fullQuery
    rw [contextRoot_eq]
  have hTargetPacket : IntegralMixedRoadmapAtomic.fullQuery (replaceWord q w) = pair (contextRoot q) w := by
    unfold IntegralMixedRoadmapAtomic.fullQuery
    rw [hroot, word_replace, contextRoot_eq]
  rw [hSourcePacket, hTargetPacket]
  exact hscan

/-- Concrete fresh OWN word transport. The interval, all row-root branches,
prepared witnesses and whole inner rejection are constructed internally. -/
theorem transport_word (q : List Bool) {R0 S0 : List Bool → ℕ} (hR0 : BinaryFn R0) (hS0 : BinaryFn S0)
    (hRlarge : cutoff hn ht ha q + 1 ≤ R0 (IntegralMixedRoadmapAtomic.original q))
    (hSlarge : cutoff hn ht ha q + 1 ≤ S0 (IntegralMixedRoadmapAtomic.original q))
    (ho : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)) :
    ∃ w, ∃ _hTargetWord : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false)
      (IntegralMixedRoadmapAtomic.context (replaceWord q w)) (IntegralMixedRoadmapAtomic.word (replaceWord q w)),
      w.length = SquareSampleCompleteVertices.width
        (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hS0) false)
        (IntegralMixedRoadmapAtomic.context (replaceWord q w)) ∧
      (IntegralMixedRoadmapProperCritical.NoCritical hn ht ha hR0 q ↔
        IntegralMixedRoadmapProperCritical.NoCritical hn ht ha hS0 (replaceWord q w)) ∧
      (IntegralMixedRoadmapAtomic.fullQuery q ∈ IntegralMixedPhysicalGuardScan.language hn ht ha
          (IntegralMixedOriginalRegularSource.radius_binary hR0) false ↔
        IntegralMixedRoadmapAtomic.fullQuery (replaceWord q w) ∈ IntegralMixedPhysicalGuardScan.language hn ht ha
          (IntegralMixedOriginalRegularSource.radius_binary hS0) false) := by
  let a : ℝ := 2 ^ cutoff hn ht ha q
  let b : ℝ := max ((2 : ℝ)^R0 (IntegralMixedRoadmapAtomic.original q))
    ((2 : ℝ)^S0 (IntegralMixedRoadmapAtomic.original q)) + 1
  have hu0 : a < (2 : ℝ)^R0 (IntegralMixedRoadmapAtomic.original q) :=
    pow_lt_pow_right₀ (by norm_num) (Nat.lt_of_succ_le hRlarge)
  have hv0 : a < (2 : ℝ)^S0 (IntegralMixedRoadmapAtomic.original q) :=
    pow_lt_pow_right₀ (by norm_num) (Nat.lt_of_succ_le hSlarge)
  let u : Ioo a b := ⟨(2 : ℝ)^R0 (IntegralMixedRoadmapAtomic.original q), hu0,
    lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)⟩
  let v : Ioo a b := ⟨(2 : ℝ)^S0 (IntegralMixedRoadmapAtomic.original q), hv0,
    lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)⟩
  obtain ⟨_, _, _, w, hw, hlen, _, hNoCrit, hCritical⟩ := transport_on_interval hn ht ha q hR0 hS0
    (Nat.le_of_succ_le hRlarge) (Nat.le_of_succ_le hSlarge) (le_refl a) u u v rfl rfl ho
  exact ⟨w, hw, hlen, hNoCrit, hCritical⟩

end LeanCanny.Encoding.CoefficientMarkedProperCriticalRadiusTransport
