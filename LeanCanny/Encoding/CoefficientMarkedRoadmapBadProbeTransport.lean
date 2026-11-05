/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeMetadata
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldListTransport
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutIntervalTransport
/-! # Fixed-hint NoBad witnesses retain their literal own-word slots -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def request (q word : List Bool) := CoefficientMarkedRoadmapBadProbeMetadata.request
  (IntegralMixedRoadmapBadProbePacket.candidate (pairFst q)) (IntegralMixedRoadmapBadProbePacket.raw (pairFst q))
  (IntegralMixedRoadmapBadProbePacket.labels (pairFst q))
  (pairFst (IntegralMixedRoadmapBadProbePacket.endpoints (pairFst q)))
  (pairSnd (IntegralMixedRoadmapBadProbePacket.endpoints (pairFst q))) (pairSnd q) word
def anchor (q : List Bool) := request q []
def baseRoot (q : List Bool) := IntegralMixedRoadmapBadProbePacket.root (pairFst q)
def preparedRoot (n : List Bool → ℕ) (q : List Bool) := IntegralMixedRoadmapBadProbePacket.preparedRoot
  (CoefficientMarkedRoadmapBadProbeMetadata.dimension n (anchor q)) (anchor q)
def leftContext (q : List Bool) := pair (baseRoot q) []
def rightContext (n : List Bool → ℕ) (q : List Bool) := pair (preparedRoot n q) []
def leftRoot (q : List Bool) := pairFst (leftContext q)
def rightRoot (n : List Bool → ℕ) (q : List Bool) := pairFst (rightContext n q)
def table (n : List Bool → ℕ) (q : List Bool) := IntegralMixedRoadmapBadProbePacket.matchTable
  (CoefficientMarkedRoadmapBadProbeMetadata.initial n (anchor q)) (pairFst (anchor q))
def stage (q : List Bool) := IntegralMixedRoadmapBadProbePacket.count (pairFst (anchor q))-1
def index (n : List Bool → ℕ) (right : Bool) (q : List Bool) :=
  IntegralMixedRoadmapBadProbePacket.creating (CoefficientMarkedRoadmapBadProbeMetadata.initial n (anchor q)) (pairFst (anchor q))-
    IntegralMixedRoadmapBadProbePacket.producer right (pairFst (anchor q))
def context (n : List Bool → ℕ) (q : List Bool) := CoefficientMarkedRecordFullCutInstalled.context (n := n)
  (rightRoot n q) (stage q) (index n false q) (index n true q)

theorem context_root {n : List Bool → ℕ} (q : List Bool) : pairFst (context n q) = rightRoot n q :=
  CoefficientMarkedRecordFullCutInstalled.context_root (n := n) _ _ _ _

theorem anchor_FP : anchor ∈ FP := by
  polytime [anchor, request, CoefficientMarkedRoadmapBadProbeMetadata.request,
    IntegralMixedRoadmapBadProbePacket.packet, IntegralMixedRoadmapBadProbePacket.candidate,
    IntegralMixedRoadmapBadProbePacket.raw, IntegralMixedRoadmapBadProbePacket.labels, IntegralMixedRoadmapBadProbePacket.endpoints]
theorem baseRoot_FP : baseRoot ∈ FP := mem_FP_comp pairFst_mem_FP IntegralMixedRoadmapBadProbePacket.root_FP

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

include hn in
theorem preparedRoot_FP : preparedRoot n ∈ FP := by
  have HC : (fun q => pairFst (IntegralMixedRoadmapBadProbePacket.candidate (pairFst q))) ∈ FP :=
    mem_FP_comp (mem_FP_comp pairFst_mem_FP IntegralMixedRoadmapBadProbePacket.candidate_FP) pairFst_mem_FP
  have HD : UnaryFn (CoefficientMarkedRoadmapBadProbeMetadata.dimension n) :=
    (hn.comp HC).add (UnaryFn.const 3)
  have HP : (fun q => IntegralMixedRoadmapBadProbePacket.preparedRoot (CoefficientMarkedRoadmapBadProbeMetadata.dimension n q) q) ∈ FP :=
    IntegralMixedRoadmapBadProbePacket.preparedRoot_FP HD
  have HT := mem_FP_comp (f := anchor)
    (g := fun q => IntegralMixedRoadmapBadProbePacket.preparedRoot (CoefficientMarkedRoadmapBadProbeMetadata.dimension n q) q) anchor_FP HP
  exact HT

theorem leftContext_FP : leftContext ∈ FP := mem_FP_pair baseRoot_FP (constFn_mem_FP [])
include hn in
theorem rightContext_FP : rightContext n ∈ FP := mem_FP_pair (preparedRoot_FP hn) (constFn_mem_FP [])
theorem leftRoot_FP : leftRoot ∈ FP := mem_FP_comp leftContext_FP pairFst_mem_FP
include hn in
theorem rightRoot_FP : rightRoot n ∈ FP :=
  mem_FP_of_eq (f := preparedRoot n) (g := rightRoot n) (preparedRoot_FP hn)
    (fun q => (pairFst_pair (preparedRoot n q) []).symm)

theorem leftRoot_eq (q : List Bool) : leftRoot q = baseRoot q := pairFst_pair _ _
theorem rightRoot_eq (q : List Bool) : rightRoot n q = preparedRoot n q := pairFst_pair _ _

noncomputable def cutoff (q : List Bool) := CoefficientMarkedRecordFieldListTransport.cutoff hn ht ha
  (pair (leftContext q) (rightContext n q))+CoefficientMarkedRecordFullCutIntervalTransport.cutoff hn ht ha (rightRoot n q)+1

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) := by
  have HF : BinaryFn (fun q => CoefficientMarkedRecordFieldListTransport.cutoff hn ht ha
      (pair (leftContext q) (rightContext n q))) :=
    (CoefficientMarkedRecordFieldListTransport.cutoff_binary hn ht ha).comp
      (mem_FP_pair leftContext_FP (rightContext_FP hn))
  have HI : BinaryFn (fun q => CoefficientMarkedRecordFullCutIntervalTransport.cutoff hn ht ha (rightRoot n q)) :=
    (CoefficientMarkedRecordFullCutIntervalTransport.cutoff_binary hn ht ha).comp (rightRoot_FP hn)
  exact (HF.add HI).add (BinaryFn.const 1)

theorem field_cutoff_le (q : List Bool) : CoefficientMarkedRecordFieldListTransport.cutoff hn ht ha
    (pair (leftContext q) (rightContext n q)) ≤ cutoff hn ht ha q := by
  unfold cutoff
  omega
theorem interval_cutoff_le (q : List Bool) : CoefficientMarkedRecordFullCutIntervalTransport.cutoff hn ht ha (rightRoot n q) ≤ cutoff hn ht ha q := by
  unfold cutoff
  omega

private theorem anchor_dimension (q : List Bool) : CoefficientMarkedRoadmapBadProbeMetadata.dimension n (anchor q) =
    n (pairFst (IntegralMixedRoadmapBadProbePacket.candidate (pairFst q)))+3 := by
  simp only [anchor, request, CoefficientMarkedRoadmapBadProbeMetadata.request, CoefficientMarkedRoadmapBadProbeMetadata.dimension,
    IntegralMixedRoadmapBadProbePacket.packet, IntegralMixedRoadmapBadProbePacket.candidate, pairFst_pair]

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic
  IntegralMixedPhysicalMarkedPlan.bank

variable {R : List Bool → ℕ} (hR : BinaryFn R)

theorem field_packet (q word fresh : List Bool) :
    IntegralMixedRoadmapBadProbeTest.fieldPacket hn ht ha hR (pair (request q word) fresh) =
      IntegralMixedPhysicalFieldEqualityList.packet (leftContext q) word (rightContext n q) fresh (table n q) := by
  unfold request
  rw [CoefficientMarkedRoadmapBadProbeMetadata.fieldPacket_request hn ht ha hR]
  unfold leftContext baseRoot rightContext preparedRoot table CoefficientMarkedRoadmapBadProbeMetadata.initial
  rw [anchor_dimension (n := n)]
  simp only [anchor, request, CoefficientMarkedRoadmapBadProbeMetadata.request,
    CoefficientMarkedRoadmapBadProbeMetadata.baseRoot, IntegralMixedRoadmapBadProbePacket.root, pairFst_pair]

theorem interval_context (q word : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (pairFst (anchor q))) :
    IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha hR (request q word) =
      context n q := by
  have HE := CoefficientMarkedRoadmapBadProbeMetadata.intervalContext_request hn ht ha hR (BinaryFn.const 0)
    (IntegralMixedRoadmapBadProbePacket.candidate (pairFst q)) (IntegralMixedRoadmapBadProbePacket.raw (pairFst q))
    (IntegralMixedRoadmapBadProbePacket.labels (pairFst q))
    (pairFst (IntegralMixedRoadmapBadProbePacket.endpoints (pairFst q)))
    (pairSnd (IntegralMixedRoadmapBadProbePacket.endpoints (pairFst q))) (pairSnd q) word []
  have H := HE.trans (CoefficientMarkedRoadmapBadProbeMetadata.intervalContext_installed hn ht ha (BinaryFn.const 0) (anchor q) hc)
  change IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha hR (request q word) =
    CoefficientMarkedRecordFullCutInstalled.context (n := n) (preparedRoot n q) (stage q) (index n false q) (index n true q) at H
  unfold context
  rw [rightRoot_eq]
  exact H

noncomputable def Hint (q : List Bool) := IntegralMixedRoadmapBadProbePacket.HintGood
  (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha hR q) (IntegralMixedRoadmapBadProbeTest.initial hn ht ha hR q)
  (IntegralMixedRoadmapBadProbeTest.width hn ht ha hR q) q

theorem count_request (q word : List Bool) :
    IntegralMixedRoadmapBadProbePacket.count (pairFst (request q word)) =
      IntegralMixedRoadmapBadProbePacket.count (pairFst (anchor q)) := by
  simp only [anchor, request, CoefficientMarkedRoadmapBadProbeMetadata.request, IntegralMixedRoadmapBadProbePacket.count,
    IntegralMixedRoadmapBadProbePacket.raw, IntegralMixedRoadmapBadProbePacket.packet, pairFst_pair, pairSnd_pair]

theorem stage_lt (q : List Bool) (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (pairFst (anchor q))) :
    stage q < IntegralMixedCausalRecordPlanBits.count (rightRoot n q) := by
  have H := IntegralMixedRoadmapBadProbePacket.prepared_count
    (CoefficientMarkedRoadmapBadProbeMetadata.dimension n (anchor q)) (anchor q) hc
  change IntegralMixedCausalRecordPlanBits.count (preparedRoot n q) = _ at H
  unfold stage
  rw [rightRoot_eq, H]
  omega

/-- Every byte-level slot and native validity in the outer witness is kept
literal; only the normalized request metadata is exposed. -/
theorem witness_iff (q word fresh : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (pairFst (anchor q)))
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (context n q) fresh) :
    IntegralMixedRoadmapBadProbeTest.Witness hn ht ha hR (pair (request q word) fresh) ↔
      Hint hn ht ha hR (request q word) ∧
      IntegralMixedPhysicalFieldEqualityList.packet (leftContext q) word (rightContext n q) fresh (table n q) ∈
        IntegralMixedPhysicalFieldEqualityList.language hn ht ha hR ∧
      IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha hR false (pair (context n q) fresh) ∧
      IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha hR false (pair (context n q) fresh) ∧
      pair (context n q) fresh ∉ IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha hR false := by
  simp only [IntegralMixedRoadmapBadProbeTest.Witness, IntegralMixedRoadmapBadProbeTest.intervalPacket,
    Hint, pairFst_pair, pairSnd_pair]
  rw [field_packet hn ht ha hR q word fresh, interval_context hn ht ha hR q word hc]
  simp only [hv, true_and]

attribute [local irreducible] SquareSampleCompleteVertices.Valid SquareSampleCompleteVertices.candidate

theorem valid_interval (q fresh : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (rightContext n q) fresh) :
    SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (context n q) fresh := by
  have hr : pairFst (rightContext n q) = pairFst (context n q) := (context_root (n := n) q).symm
  have H := IntegralMixedPhysicalMarkedContext.valid_iff hn ht ha hR (rightContext n q) (context n q) fresh hr
  exact H.mp hv

theorem candidate_interval (q fresh : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (rightContext n q) fresh) :
    HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (context n q) fresh (valid_interval hn ht ha hR q fresh hv)).val
      (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (rightContext n q) fresh hv).val :=
  CoefficientMarkedRecordFullCutComparison.candidate_context hn ht ha hR (context n q) (rightContext n q) fresh
    (context_root q) (valid_interval hn ht ha hR q fresh hv) hv

variable {S : List Bool → ℕ} (hS : BinaryFn S)

theorem hint_iff (q w v : List Bool) : Hint hn ht ha hR (request q w) ↔ Hint hn ht ha hS (request q v) := by
  unfold Hint request
  rw [CoefficientMarkedRoadmapBadProbeMetadata.dimension_request hn ht ha hR hS _ _ _ _ _ _ w v,
    CoefficientMarkedRoadmapBadProbeMetadata.initial_request hn ht ha hR hS _ _ _ _ _ _ w v,
    CoefficientMarkedRoadmapBadProbeMetadata.width_request hn ht ha hR hS _ _ _ _ _ _ w v]
  unfold IntegralMixedRoadmapBadProbePacket.HintGood
  simp only [CoefficientMarkedRoadmapBadProbeMetadata.request, IntegralMixedRoadmapBadProbePacket.packet,
    IntegralMixedRoadmapBadProbePacket.count, IntegralMixedRoadmapBadProbePacket.raw,
    IntegralMixedRoadmapBadProbePacket.creating, IntegralMixedRoadmapBadProbePacket.labels,
    IntegralMixedRoadmapBadProbePacket.field, IntegralMixedRoadmapBadProbePacket.producer,
    IntegralMixedRoadmapBadProbePacket.endpoints, pairFst_pair, pairSnd_pair]

/-- The complete native fixed-hint Witness is preserved on the same two
actual full-row curves. All four words are independently valid at their OWN
resource functions; no native guard, compatibility hom or degree premise is
supplied. The common requested radius at the two roots is explicit. -/
theorem witness_on_curves (q : List Bool)
    (hReq : R (leftRoot q) = R (rightRoot n q)) (hSeq : S (leftRoot q) = S (rightRoot n q))
    (hRc : cutoff hn ht ha q ≤ R (leftRoot q)) (hSc : cutoff hn ht ha q ≤ S (leftRoot q))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a)
    (xL : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (leftContext q)))
    (xR : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (rightContext n q)))
    (hxL : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (leftRoot q)
      (IntegralMixedCausalRecordPlanBits.count (leftRoot q)) le_rfl u.val (xL u))
    (hxR : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (rightRoot n q)
      (IntegralMixedCausalRecordPlanBits.count (rightRoot n q)) le_rfl u.val (xR u))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R (leftRoot q)) (hv : v.val = (2 : ℝ)^S (leftRoot q))
    (wRL wRR wSL wSR : List Bool)
    (hwRL : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (leftContext q) wRL)
    (hwRR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (rightContext n q) wRR)
    (hwSL : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (leftContext q) wSL)
    (hwSR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (rightContext n q) wSR)
    (heRL : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (leftContext q) wRL hwRL).val (xL u))
    (heRR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (rightContext n q) wRR hwRR).val (xR u))
    (heSL : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (leftContext q) wSL hwSL).val (xL v))
    (heSR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (rightContext n q) wSR hwSR).val (xR v)) :
    IntegralMixedRoadmapBadProbeTest.Witness hn ht ha hR (pair (request q wRL) wRR) ↔
      IntegralMixedRoadmapBadProbeTest.Witness hn ht ha hS (pair (request q wSL) wSR) := by
  have HH := hint_iff hn ht ha hR hS q wRL wSL
  by_cases hH : Hint hn ht ha hR (request q wRL)
  · have hH' := HH.mp hH
    have hc : 0 < IntegralMixedRoadmapBadProbePacket.count (pairFst (anchor q)) := by
      have H : 0 < IntegralMixedRoadmapBadProbePacket.count (pairFst (request q wRL)) := hH.1
      rw [count_request] at H
      exact H
    have hk := stage_lt (n := n) q hc
    let iwR := valid_interval hn ht ha hR q wRR hwRR
    let iwS := valid_interval hn ht ha hS q wSR hwSR
    have iJR := (candidate_interval hn ht ha hR q wRR hwRR).trans heRR
    have iJS := (candidate_interval hn ht ha hS q wSR hwSR).trans heSR
    have hRi : CoefficientMarkedRecordFullCutIntervalTransport.cutoff hn ht ha (rightRoot n q) ≤ R (rightRoot n q) := by
      rw [← hReq]
      exact (interval_cutoff_le hn ht ha q).trans hRc
    have hSi : CoefficientMarkedRecordFullCutIntervalTransport.cutoff hn ht ha (rightRoot n q) ≤ S (rightRoot n q) := by
      rw [← hSeq]
      exact (interval_cutoff_le hn ht ha q).trans hSc
    have startF := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (field_cutoff_le hn ht ha q)).trans ha0
    have startI := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (interval_cutoff_le hn ht ha q)).trans ha0
    have huI := hu.trans (congrArg (fun r : ℕ => (2 : ℝ)^r) hReq)
    have hvI := hv.trans (congrArg (fun r : ℕ => (2 : ℝ)^r) hSeq)
    have HF := CoefficientMarkedRecordFieldListTransport.language_on_curves hn ht ha hR hS
      (leftContext q) (rightContext n q) (table n q) hReq hSeq
      ((field_cutoff_le hn ht ha q).trans hRc) ((field_cutoff_le hn ht ha q).trans hSc)
      startF xL xR hxL hxR u v hu hv wRL wRR wSL wSR hwRL hwRR hwSL hwSR heRL heRR heSL heSR
    have HL := CoefficientMarkedRecordFullCutIntervalTransport.language_on_curve hn ht ha hR hS (rightRoot n q)
      (stage q) hk (index n false q) (index n true q) hRi hSi startI xR hxR u v huI hvI wRR wSR iwR iwS iJR iJS
    have HB := (CoefficientMarkedRecordFullCutCoefficientGuards.bounds_iff hn ht ha hR (rightRoot n q) wRR
      (stage q) (index n false q) (index n true q) hk).trans
        (CoefficientMarkedRecordFullCutCoefficientGuards.bounds_iff hn ht ha hS (rightRoot n q) wSR
          (stage q) (index n false q) (index n true q) hk).symm
    rw [witness_iff hn ht ha hR q wRL wRR hc iwR, witness_iff hn ht ha hS q wSL wSR hc iwS]
    by_cases hb : IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha hR false (pair (context n q) wRR)
    · have hcut := ((CoefficientMarkedRecordFullCutCoefficientGuards.bounds_iff hn ht ha hR (rightRoot n q) wRR
        (stage q) (index n false q) (index n true q) hk).mp hb).2.2.2
      have gR := (CoefficientMarkedRecordFullCutIntervalTransport.coefficient_cutoff_le hn ht ha _).trans hRi
      have gS := (CoefficientMarkedRecordFullCutIntervalTransport.coefficient_cutoff_le hn ht ha _).trans hSi
      have startG := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (CoefficientMarkedRecordFullCutIntervalTransport.coefficient_cutoff_le hn ht ha (rightRoot n q))).trans startI
      have HG := CoefficientMarkedRecordFullCutCoefficientGuards.guards_on_curve hn ht ha hR hS (rightRoot n q)
        gR gS startG xR hxR u v huI hvI (stage q) (index n false q) (index n true q) hk hcut wRR wSR iwR iwS iJR iJS
      exact and_congr HH (and_congr HF (and_congr HB (and_congr HG HL.not)))
    · have hb' : ¬IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha hS false (pair (context n q) wSR) := mt HB.mpr hb
      simp only [hb, hb', false_and, and_false]
  · have hH' := mt HH.mpr hH
    simp only [IntegralMixedRoadmapBadProbeTest.Witness, pairFst_pair, Hint] at hH hH' ⊢
    simp only [hH, hH', false_and]

end LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeTransport
