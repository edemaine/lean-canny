/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeTransport
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullSemantics
/-! # Prepared-word search is transported by the actual complete row family -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

theorem prepared_row_cutoff_le (q : List Bool) :
    CoefficientMarkedRecordCartesianRows.cutoff hn ht ha (rightRoot n q) ≤ cutoff hn ht ha q := by
  let z := IntegralMixedPhysicalFieldEquality.packet (leftContext q) [] (rightContext n q) [] 0 0
  have H := CoefficientMarkedRecordFieldSign.row_cutoff_le hn ht ha true z
  have H' : CoefficientMarkedRecordCartesianRows.cutoff hn ht ha (rightRoot n q) ≤
      CoefficientMarkedRecordFieldSign.cutoff hn ht ha true z := by
    simpa only [z, CoefficientMarkedRecordFieldQuery.rightRoot, IntegralMixedPhysicalFieldEquality.context,
      IntegralMixedPhysicalFieldEquality.sample, IntegralMixedPhysicalFieldEquality.packet, ite_true,
      pairFst_pair, pairSnd_pair, rightRoot] using H
  exact H'.trans ((CoefficientMarkedRecordFieldListTransport.member_cutoff_le hn ht ha true
    (leftContext q) (rightContext n q) 0 0).trans (field_cutoff_le hn ht ha q))

theorem prepared_effective_le (q : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (rightRoot n q) ≤ cutoff hn ht ha q :=
  (CoefficientMarkedRecordCartesianRows.effectiveCutoff_le hn ht ha (rightRoot n q)).trans
    (prepared_row_cutoff_le hn ht ha q)

private theorem valid_length (I : SquareSampleInput.Inputs) (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid I c w) : w.length = SquareSampleCompleteVertices.width I c :=
  (Classical.choose hv).1

attribute [local irreducible] SquareSampleCompleteVertices.Valid SquareSampleCompleteVertices.candidate
  CoefficientMarkedRecordRows.symbolic IntegralMixedPhysicalMarkedPlan.bank

variable {R : List Bool → ℕ} (hR : BinaryFn R)

private theorem rows_of_context_word (c w : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (pairFst c) ≤ R (pairFst c))
    (hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) c w) :
    ∃ z : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha c,
      CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (pairFst c) (IntegralMixedCausalRecordPlanBits.count (pairFst c)) le_rfl
        ((2 : ℝ)^R (pairFst c)) z ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) c w hw).val z := by
  have hr : pairFst c = pairFst (IntegralMixedPhysicalMarkedTest.sampleContext (pairFst c)) := (pairFst_pair _ []).symm
  let hs := (IntegralMixedPhysicalMarkedContext.valid_iff hn ht ha hR c
    (IntegralMixedPhysicalMarkedTest.sampleContext (pairFst c)) w hr).mp hw
  have he := CoefficientMarkedRecordFullCutComparison.candidate_context hn ht ha hR c
    (IntegralMixedPhysicalMarkedTest.sampleContext (pairFst c)) w hr hw hs
  obtain ⟨z, hz, hj⟩ := CoefficientMarkedRecordCriticalFullSemantics.rows_of_word hn ht ha hR (pairFst c) hlarge w hs
  exact ⟨z, hz, he.trans hj⟩

private theorem exists_context_word (c : List Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (pairFst c) ≤ R (pairFst c))
    (z : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha c)
    (hz : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (pairFst c) (IntegralMixedCausalRecordPlanBits.count (pairFst c)) le_rfl
      ((2 : ℝ)^R (pairFst c)) z) :
    ∃ w, ∃ hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) c w,
      w.length = SquareSampleCompleteVertices.width (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) c ∧
      HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) c w hw).val z := by
  obtain ⟨w, hw, _, hj⟩ := CoefficientMarkedRecordFullRealization.exists_word hn ht ha (pairFst c) hR hlarge z hz
  have hr : pairFst c = pairFst (IntegralMixedPhysicalMarkedTest.sampleContext (pairFst c)) := (pairFst_pair _ []).symm
  let hc := (IntegralMixedPhysicalMarkedContext.valid_iff hn ht ha hR
    (IntegralMixedPhysicalMarkedTest.sampleContext (pairFst c)) c w hr.symm).mp hw
  have he := CoefficientMarkedRecordFullCutComparison.candidate_context hn ht ha hR c
    (IntegralMixedPhysicalMarkedTest.sampleContext (pairFst c)) w hr hc hw
  exact ⟨w, hc, valid_length _ _ _ hc, he.trans hj⟩

private theorem right_valid_of_witness (q word fresh : List Bool)
    (H : IntegralMixedRoadmapBadProbeTest.Witness hn ht ha hR (pair (request q word) fresh)) :
    SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (rightContext n q) fresh := by
  have HF := H.2.1
  rw [field_packet hn ht ha hR] at HF
  have HV := HF.2.1
  simpa only [IntegralMixedPhysicalFieldEqualityList.packet, IntegralMixedPhysicalFieldEquality.context,
    IntegralMixedPhysicalFieldEquality.word, IntegralMixedPhysicalFieldEquality.sample, ite_true, pairFst_pair, pairSnd_pair] using HV

variable {S : List Bool → ℕ} (hS : BinaryFn S)

/-- The prepared root curve and target word are CONSTRUCTED from the actual
source witness. Every prepared native word is covered; no prepared curve,
model, guards or target word are supplied. -/
theorem transfer_witness (q : List Bool)
    (hReq : R (leftRoot q) = R (rightRoot n q)) (hSeq : S (leftRoot q) = S (rightRoot n q))
    (hRc : cutoff hn ht ha q ≤ R (leftRoot q)) (hSc : cutoff hn ht ha q ≤ S (leftRoot q))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a) (s : Ioo a b)
    (x : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (leftContext q)))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (leftRoot q)
      (IntegralMixedCausalRecordPlanBits.count (leftRoot q)) le_rfl u.val (x u))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R (leftRoot q)) (hv : v.val = (2 : ℝ)^S (leftRoot q))
    (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (leftContext q) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (leftContext q) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (leftContext q) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (leftContext q) wS hwS).val (x v))
    (fresh : List Bool) (H : IntegralMixedRoadmapBadProbeTest.Witness hn ht ha hR (pair (request q wR) fresh)) :
    ∃ target, ∃ _hw : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (rightContext n q) target,
      target.length = SquareSampleCompleteVertices.width (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (rightContext n q) ∧
      IntegralMixedRoadmapBadProbeTest.Witness hn ht ha hS (pair (request q wS) target) := by
  have hrR : cutoff hn ht ha q ≤ R (rightRoot n q) := hReq ▸ hRc
  have hrS : cutoff hn ht ha q ≤ S (rightRoot n q) := hSeq ▸ hSc
  have huI := hu.trans (congrArg (fun r : ℕ => (2 : ℝ)^r) hReq)
  have hvI := hv.trans (congrArg (fun r : ℕ => (2 : ℝ)^r) hSeq)
  have hstart := (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (prepared_row_cutoff_le hn ht ha q)).trans ha0
  obtain ⟨curve, _, hrows, hcover⟩ := CoefficientMarkedRecordRootBranches.exists_branches hn ht ha (rightRoot n q)
    (IntegralMixedCausalRecordPlanBits.count (rightRoot n q)) le_rfl hstart s
  let hFresh := right_valid_of_witness hn ht ha hR q wR fresh H
  obtain ⟨z, hz, he⟩ := rows_of_context_word hn ht ha hR (rightContext n q) fresh
    ((prepared_effective_le hn ht ha q).trans hrR) hFresh
  have hzu : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (rightRoot n q)
    (IntegralMixedCausalRecordPlanBits.count (rightRoot n q)) le_rfl u.val z := huI.symm ▸ hz
  obtain ⟨l, hl, _⟩ := (hcover u z).mp hzu
  have heU := he.trans (heq_of_eq hl.symm)
  have hzv : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (rightRoot n q)
    (IntegralMixedCausalRecordPlanBits.count (rightRoot n q)) le_rfl ((2 : ℝ)^S (rightRoot n q)) (curve l.val v) := hvI ▸ hrows l v
  obtain ⟨target, hw, hlen, heV⟩ := exists_context_word hn ht ha hS (rightContext n q)
    ((prepared_effective_le hn ht ha q).trans hrS) (curve l.val v) hzv
  have HT := witness_on_curves hn ht ha hR hS q hReq hSeq hRc hSc ha0 x (curve l.val) hx (hrows l)
    u v hu hv wR fresh wS target hwR hFresh hwS hw hjR heU hjS heV
  exact ⟨target, hw, hlen, HT.mp H⟩

/-- The literal bounded prepared-word search has the same truth on the
chosen base curve. Its complete prepared family and OWN native widths are
derived internally in BOTH directions. -/
theorem hasWitness_on_curve (q : List Bool)
    (hReq : R (leftRoot q) = R (rightRoot n q)) (hSeq : S (leftRoot q) = S (rightRoot n q))
    (hRc : cutoff hn ht ha q ≤ R (leftRoot q)) (hSc : cutoff hn ht ha q ≤ S (leftRoot q))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a) (s : Ioo a b)
    (x : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (leftContext q)))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (leftRoot q)
      (IntegralMixedCausalRecordPlanBits.count (leftRoot q)) le_rfl u.val (x u))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R (leftRoot q)) (hv : v.val = (2 : ℝ)^S (leftRoot q))
    (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (leftContext q) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (leftContext q) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (leftContext q) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (leftContext q) wS hwS).val (x v)) :
    IntegralMixedRoadmapBadProbeTest.HasWitness hn ht ha hR (request q wR) ↔
      IntegralMixedRoadmapBadProbeTest.HasWitness hn ht ha hS (request q wS) := by
  rw [IntegralMixedRoadmapBadProbeTest.hasWitness_iff, IntegralMixedRoadmapBadProbeTest.hasWitness_iff]
  constructor
  · rintro ⟨fresh, H⟩
    obtain ⟨target, _, _, HT⟩ := transfer_witness hn ht ha hR hS q hReq hSeq hRc hSc ha0 s x hx u v hu hv wR wS hwR hwS hjR hjS fresh H
    exact ⟨target, HT⟩
  · rintro ⟨fresh, H⟩
    obtain ⟨target, _, _, HT⟩ := transfer_witness hn ht ha hS hR q hSeq hReq hSc hRc ha0 s x hx v u hv hu wS wR hwS hwR hjS hjR fresh H
    exact ⟨target, HT⟩

end LeanCanny.Encoding.CoefficientMarkedRoadmapBadProbeTransport
