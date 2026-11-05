/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldListIncidence
public import LeanCanny.Encoding.CoefficientMarkedProperCriticalLayout
public import LeanCanny.Encoding.CoefficientMarkedCriticalWordContext
public import LeanCanny.Encoding.CoefficientMarkedCriticalIntervalPredicate
public import LeanCanny.Encoding.CoefficientMarkedCriticalPredicateContext
public import LeanCanny.Encoding.CoefficientMarkedCriticalParentWord
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCriticalMetadata
/-! # One coupled raw-tuple formula for the actual no-critical witness -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedProperCriticalPredicate
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def query (n : List Bool → ℕ) (q : List Bool) := CoefficientMarkedProperCriticalLayout.canonical n q
def context (n : List Bool → ℕ) (q : List Bool) := CoefficientMarkedProperCriticalLayout.context n q
def table (n : List Bool → ℕ) (q : List Bool) :=
  IntegralMixedRoadmapBadProbePacket.matchTable (n (IntegralMixedRoadmapAtomic.original q) + 8)
    (IntegralMixedRoadmapProper.badPacket q)

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic

theorem full_type (q : List Bool) :
    CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (context n q) =
      CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true (query n q) := by
  unfold CoefficientMarkedRecordFieldListIncidence.Point CoefficientMarkedCriticalIntervalPredicate.Point
    CoefficientMarkedCriticalBankQuery.stage context query CoefficientMarkedProperCriticalLayout.context
    CoefficientMarkedProperCriticalLayout.root
  simp only [pairFst_pair, ite_true, Nat.sub_zero]

noncomputable def fullPoint (q : List Bool)
    (z : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (context n q)) :
    CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true (query n q) :=
  Eq.mp (full_type hn ht ha q) z

private theorem cast_heq {A B : Type} (h : A = B) (x : A) : HEq (Eq.mp h x) x := by
  cases h
  rfl

theorem full_heq (q : List Bool)
    (z : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (context n q)) :
    HEq (fullPoint hn ht ha q z) z := by
  exact cast_heq (full_type hn ht ha q) z

/-- One prepared FULL tuple supplies all old-field comparisons and parent
incidence. One prepared PARENT tuple supplies that incidence and the rejection
of the complete inner child search. There are no sampled words in this formula. -/
noncomputable def Holds (q : List Bool) (β : ℝ)
    (original : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (IntegralMixedRoadmapAtomic.context q)) : Prop :=
  IntegralMixedPhysicalCriticalInterval.Guard n false (query n q) ∧
  ∃ child : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (context n q),
  ∃ parent : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha false (query n q),
    CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root (query n q))
      (CoefficientMarkedCriticalBankQuery.stage true (query n q)) (Nat.sub_le _ _) β (fullPoint hn ht ha q child) ∧
    CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root (query n q))
      (CoefficientMarkedCriticalBankQuery.stage false (query n q)) (Nat.sub_le _ _) β parent ∧
    CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha (IntegralMixedRoadmapAtomic.context q)
      (context n q) (table n q) β original child ∧
    CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha (query n q) β parent (fullPoint hn ht ha q child) ∧
    ¬ CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha (query n q) β parent

variable {R0 : List Bool → ℕ} (hR0 : BinaryFn R0)

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  SquareSampleCompleteVertices.Valid IntegralMixedRoadmapAtomic.initial

private theorem native_canonical (q : List Bool) :
    IntegralMixedRoadmapProperCritical.canonical hn ht ha hR0 q = query n q := by
  unfold IntegralMixedRoadmapProperCritical.canonical query CoefficientMarkedProperCriticalLayout.canonical
  rw [CoefficientMarkedProperCriticalLayout.native_query hn ht ha hR0]

private theorem actual_root (q w : List Bool) :
    IntegralMixedPhysicalCriticalQuery.root (IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q w)) =
      IntegralMixedPhysicalCriticalQuery.root (query n q) := by
  exact (IntegralMixedRoadmapProperCritical.root_word hn ht ha hR0 q w).trans
    (CoefficientMarkedProperCriticalLayout.native_root hn ht ha hR0 q)

private theorem radius_query (q w : List Bool) :
    IntegralMixedOriginalRegularSource.radius R0
      (IntegralMixedPhysicalCriticalQuery.root (IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q w))) =
      R0 (IntegralMixedRoadmapAtomic.original q) := by
  unfold IntegralMixedOriginalRegularSource.radius IntegralMixedAuxiliaryMarkedIntegerSource.original
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate
  rw [IntegralMixedRoadmapProperCritical.query_candidate hn ht ha hR0]
  rfl

include hn ht ha hR0 in
private theorem radius_canonical (q : List Bool) :
    IntegralMixedOriginalRegularSource.radius R0 (IntegralMixedPhysicalCriticalQuery.root (query n q)) =
      R0 (IntegralMixedRoadmapAtomic.original q) := by
  have hh := radius_query hn ht ha hR0 q []
  rw [actual_root hn ht ha hR0 q []] at hh
  exact hh

private theorem radius_atomic (q : List Bool) :
    IntegralMixedOriginalRegularSource.radius R0 (IntegralMixedRoadmapAtomic.root q) =
      R0 (IntegralMixedRoadmapAtomic.original q) := by
  unfold IntegralMixedOriginalRegularSource.radius IntegralMixedAuxiliaryMarkedIntegerSource.original
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate IntegralMixedRoadmapAtomic.root
    IntegralMixedRoadmapAtomic.original
  rw [pairFst_pair]

private theorem valid_at (I : SquareSampleInput.Inputs) (q r w : List Bool) (he : q = r)
    (hq : SquareSampleCompleteVertices.Valid I q w) : SquareSampleCompleteVertices.Valid I r w := by
  subst r
  exact hq

private theorem candidate_at (I : SquareSampleInput.Inputs) (q r w : List Bool) (he : q = r)
    (hq : SquareSampleCompleteVertices.Valid I q w) (hr : SquareSampleCompleteVertices.Valid I r w) :
    HEq (SquareSampleCompleteVertices.candidate I q w hq).val (SquareSampleCompleteVertices.candidate I r w hr).val := by
  subst r
  rfl

private theorem valid_context (child : Bool) (q r w : List Bool) (he : pairFst q = pairFst r) :
    SquareSampleCompleteVertices.Valid
        (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false child) q w ↔
      SquareSampleCompleteVertices.Valid
        (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false child) r w := by
  cases child
  · exact IntegralMixedPhysicalCriticalParentContext.valid_iff hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) q r w he
  · rw [IntegralMixedPhysicalCriticalContext.input_factor,
      SquareSampleCompleteNaturality.complete_valid_comp, SquareSampleCompleteNaturality.complete_valid_comp, he]

private theorem full_context (q : List Bool) :
    IntegralMixedPhysicalCriticalContext.context (query n q) = context n q := rfl

private theorem fields_packet (q wF wP : List Bool) :
    IntegralMixedRoadmapProperCritical.fields hn ht ha hR0 (pair (pair q wF) wP) =
      IntegralMixedPhysicalFieldEqualityList.packet (IntegralMixedRoadmapAtomic.context q)
        (IntegralMixedRoadmapAtomic.word q) (context n q) wF (table n q) := by
  unfold IntegralMixedRoadmapProperCritical.fields IntegralMixedRoadmapProperCritical.atomic
    IntegralMixedRoadmapProperCritical.fullWord
  simp only [pairFst_pair, pairSnd_pair]
  rw [IntegralMixedRoadmapAtomic.initial_eq hn ht ha hR0,
    CoefficientMarkedProperCriticalLayout.native_context hn ht ha hR0]
  rfl

private noncomputable def rootPoint (child : Bool) (ctx : List Bool) :=
  Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx
    (IntegralMixedCausalRecordPlanBits.count ctx - if child then 0 else 1) (Nat.sub_le _ _)).count → ℝ

private theorem point_factor (child : Bool) (q : List Bool) :
    CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha child q =
      rootPoint hn ht ha child (IntegralMixedPhysicalCriticalQuery.root q) := rfl

private theorem point_type (child : Bool) (q r : List Bool)
    (he : IntegralMixedPhysicalCriticalQuery.root q = IntegralMixedPhysicalCriticalQuery.root r) :
    CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha child q =
      CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha child r :=
  (point_factor hn ht ha child q).trans
    ((congrArg (rootPoint hn ht ha child) he).trans (point_factor hn ht ha child r).symm)

private noncomputable def pointAt (child : Bool) (q r : List Bool)
    (he : IntegralMixedPhysicalCriticalQuery.root q = IntegralMixedPhysicalCriticalQuery.root r)
    (p : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha child q) :
    CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha child r :=
  Eq.mp (point_type hn ht ha child q r he) p

private theorem pointAt_heq (child : Bool) (q r : List Bool)
    (he : IntegralMixedPhysicalCriticalQuery.root q = IntegralMixedPhysicalCriticalQuery.root r)
    (p : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha child q) :
    HEq (pointAt hn ht ha child q r he p) p :=
  cast_heq (point_type hn ht ha child q r he) p

private theorem guard_root (q r : List Bool)
    (he : IntegralMixedPhysicalCriticalQuery.root q = IntegralMixedPhysicalCriticalQuery.root r) :
    IntegralMixedPhysicalCriticalInterval.Guard n false q ↔ IntegralMixedPhysicalCriticalInterval.Guard n false r := by
  unfold IntegralMixedPhysicalCriticalInterval.Guard IntegralMixedPhysicalCriticalQuery.critical
    IntegralMixedPhysicalCriticalQuery.lastCode IntegralMixedPhysicalCriticalQuery.leftWord
    IntegralMixedPhysicalCriticalQuery.rightWord IntegralMixedPhysicalCriticalPrefixes.birth
  rw [he]

private theorem full_actual_context (q wP : List Bool) :
    IntegralMixedPhysicalCriticalContext.context
        (IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q wP)) = context n q := by
  exact congrArg (fun ctx => pair ctx []) (actual_root hn ht ha hR0 q wP)

private theorem full_candidate (q wF wP : List Bool)
    (hf : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false true)
      (IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q wP)) wF)
    (hs : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false) (context n q) wF) :
    HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false true)
      (IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q wP)) wF hf).val
      (SquareSampleCompleteVertices.candidate
        (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
        (context n q) wF hs).val := by
  have hctx := (IntegralMixedPhysicalCriticalContext.valid_full hn ht ha
    (IntegralMixedOriginalRegularSource.radius_binary hR0) _ wF).mp hf
  exact (CoefficientMarkedCriticalWordContext.candidate_full hn ht ha
    (IntegralMixedOriginalRegularSource.radius_binary hR0) _ wF hf hctx).trans
    (candidate_at _ _ _ wF (full_actual_context hn ht ha hR0 q wP) hctx hs)

private theorem critical_packet (q wF wP : List Bool) :
    IntegralMixedRoadmapProperCritical.critical hn ht ha hR0 (pair (pair q wF) wP) =
      IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q wP) := by
  simp only [IntegralMixedRoadmapProperCritical.critical, IntegralMixedRoadmapProperCritical.atomic,
    IntegralMixedRoadmapProperCritical.parentWord, pairFst_pair, pairSnd_pair]

private theorem valid_word (I : SquareSampleInput.Inputs) (q w v : List Bool) (he : w = v)
    (hw : SquareSampleCompleteVertices.Valid I q w) : SquareSampleCompleteVertices.Valid I q v := by
  subst v
  exact hw

private theorem candidate_word (I : SquareSampleInput.Inputs) (q w v : List Bool) (he : w = v)
    (hw : SquareSampleCompleteVertices.Valid I q w) (hv : SquareSampleCompleteVertices.Valid I q v) :
    HEq (SquareSampleCompleteVertices.candidate I q v hv).val (SquareSampleCompleteVertices.candidate I q w hw).val := by
  subst v
  rfl

attribute [local irreducible] IntegralMixedRoadmapProperCritical.query query context table fullPoint pointAt

private theorem inner_iff (Q wF : List Bool)
    (hg : IntegralMixedPhysicalCriticalInterval.Guard n false Q)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root Q) ≤
      IntegralMixedOriginalRegularSource.radius R0 (IntegralMixedPhysicalCriticalQuery.root Q))
    (hp : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false false)
      Q (IntegralMixedPhysicalCriticalQuery.parentWord Q))
    (hf : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false true) Q wF)
    (parent : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha false Q)
    (child : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true Q)
    (heP : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false false)
      Q (IntegralMixedPhysicalCriticalQuery.parentWord Q) hp).val parent)
    (heF : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false true) Q wF hf).val child) :
    (IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false (pair Q wF) ∧
      Q ∉ IntegralMixedPhysicalCriticalInterval.language hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false) ↔
    CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha Q
      ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (IntegralMixedPhysicalCriticalQuery.root Q)) parent child ∧
      ¬ CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha Q
        ((2 : ℝ)^IntegralMixedOriginalRegularSource.radius R0 (IntegralMixedPhysicalCriticalQuery.root Q)) parent := by
  have hb := CoefficientMarkedCriticalBankIncidence.agrees_iff hn ht ha
    (IntegralMixedOriginalRegularSource.radius_binary hR0) Q hg.1.1 hlarge
    (IntegralMixedPhysicalCriticalQuery.parentWord Q) wF rfl hp hf parent child heP heF
  have hi := CoefficientMarkedCriticalIntervalPredicate.language_iff hn ht ha
    (IntegralMixedOriginalRegularSource.radius_binary hR0) Q hg hlarge hp parent heP
  exact and_congr hb (not_congr hi)

private theorem witness_iff (q wF wP : List Bool)
    (hL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (IntegralMixedRoadmapAtomic.root q) ≤
      R0 (IntegralMixedRoadmapAtomic.original q))
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
        (IntegralMixedPhysicalCriticalQuery.root (query n q)) ≤ R0 (IntegralMixedRoadmapAtomic.original q))
    (ho : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q))
    (hp : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false false)
      (IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q wP)) wP)
    (hf : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false true)
      (IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q wP)) wF)
    (hs : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false) (context n q) wF)
    (original : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (IntegralMixedRoadmapAtomic.context q))
    (child : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (context n q))
    (parent : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha false (query n q))
    (heO : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) ho).val original)
    (heF : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
      (context n q) wF hs).val child)
    (heP : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false false)
      (IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q wP)) wP hp).val parent) :
    IntegralMixedRoadmapProperCritical.Witness hn ht ha hR0 (pair (pair q wF) wP) ↔
      IntegralMixedPhysicalCriticalInterval.Guard n false (query n q) ∧
      CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha (IntegralMixedRoadmapAtomic.context q)
        (context n q) (table n q) ((2 : ℝ)^R0 (IntegralMixedRoadmapAtomic.original q)) original child ∧
      CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha (query n q)
        ((2 : ℝ)^R0 (IntegralMixedRoadmapAtomic.original q)) parent (fullPoint hn ht ha q child) ∧
      ¬ CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha (query n q)
        ((2 : ℝ)^R0 (IntegralMixedRoadmapAtomic.original q)) parent := by
  let Q := IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q wP)
  have hr := actual_root hn ht ha hR0 q wP
  let p := pointAt hn ht ha false (query n q) Q hr.symm parent
  let f := pointAt hn ht ha true (query n q) Q hr.symm (fullPoint hn ht ha q child)
  have hpe : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false false)
      Q wP hp).val p := heP.trans (pointAt_heq hn ht ha false _ _ hr.symm parent).symm
  have hfe : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false true)
      Q wF hf).val f := (full_candidate hn ht ha hR0 q wF wP hf hs).trans
        (heF.trans ((full_heq hn ht ha q child).symm.trans
          (pointAt_heq hn ht ha true _ _ hr.symm (fullPoint hn ht ha q child)).symm))
  have hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root Q) ≤
      IntegralMixedOriginalRegularSource.radius R0 (IntegralMixedPhysicalCriticalQuery.root Q) := by
    rw [hr, radius_canonical hn ht ha hR0]
    exact hR
  have hv : IntegralMixedOriginalRegularSource.radius R0 (IntegralMixedPhysicalCriticalQuery.root Q) =
      R0 (IntegralMixedRoadmapAtomic.original q) := radius_query hn ht ha hR0 q wP
  have hcL : pairFst (IntegralMixedRoadmapAtomic.context q) = IntegralMixedRoadmapAtomic.root q := by
    unfold IntegralMixedRoadmapAtomic.context
    exact pairFst_pair _ _
  have hcR : pairFst (context n q) = IntegralMixedPhysicalCriticalQuery.root (query n q) := by
    unfold context CoefficientMarkedProperCriticalLayout.context CoefficientMarkedProperCriticalLayout.root query
    exact pairFst_pair _ _
  have hfields := CoefficientMarkedRecordFieldListIncidence.language_iff hn ht ha
    (IntegralMixedOriginalRegularSource.radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) (context n q) wF (table n q)
    (by rw [hcL, hcR]; exact (radius_atomic (R0 := R0) q).trans (radius_canonical hn ht ha hR0 q).symm)
    (by rw [hcL, radius_atomic]; exact hL) (by rw [hcR, radius_canonical hn ht ha hR0]; exact hR)
    ho hs original child heO heF
  rw [hcL, radius_atomic] at hfields
  have htail (hg : IntegralMixedPhysicalCriticalInterval.Guard n false Q) :
      (IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false (pair Q wF) ∧
        Q ∉ IntegralMixedPhysicalCriticalInterval.language hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false) ↔
      CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha (query n q)
        ((2 : ℝ)^R0 (IntegralMixedRoadmapAtomic.original q)) parent (fullPoint hn ht ha q child) ∧
        ¬ CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha (query n q)
          ((2 : ℝ)^R0 (IntegralMixedRoadmapAtomic.original q)) parent := by
    have hw : wP = IntegralMixedPhysicalCriticalQuery.parentWord Q := by
      simp only [Q, IntegralMixedRoadmapProperCritical.query, IntegralMixedPhysicalCriticalQuery.packet,
        IntegralMixedPhysicalCriticalQuery.parentWord, pairFst_pair, pairSnd_pair]
    have hwp := valid_word _ Q wP (IntegralMixedPhysicalCriticalQuery.parentWord Q) hw hp
    have hep := (candidate_word _ Q wP (IntegralMixedPhysicalCriticalQuery.parentWord Q) hw hp hwp).trans hpe
    have hi := inner_iff hn ht ha hR0 Q wF hg hlarge hwp hf p f hep hfe
    rw [hv] at hi
    apply hi.trans
    exact and_congr (CoefficientMarkedCriticalPredicateContext.bank_agrees_iff hn ht ha Q _ hr _ p f
      parent (fullPoint hn ht ha q child) (pointAt_heq hn ht ha false _ _ hr.symm parent)
      (pointAt_heq hn ht ha true _ _ hr.symm (fullPoint hn ht ha q child)))
      (not_congr (CoefficientMarkedCriticalPredicateContext.counterexample_iff hn ht ha Q _ hr _ p parent
        (pointAt_heq hn ht ha false _ _ hr.symm parent)))
  have hnativ : IntegralMixedRoadmapProperCritical.Witness hn ht ha hR0 (pair (pair q wF) wP) ↔
      IntegralMixedPhysicalCriticalInterval.Guard n false Q ∧
      IntegralMixedPhysicalFieldEqualityList.packet (IntegralMixedRoadmapAtomic.context q)
        (IntegralMixedRoadmapAtomic.word q) (context n q) wF (table n q) ∈
          IntegralMixedPhysicalFieldEqualityList.language hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) ∧
      IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false (pair Q wF) ∧
      Q ∉ IntegralMixedPhysicalCriticalInterval.language hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false := by
    simp only [IntegralMixedRoadmapProperCritical.Witness, critical_packet hn ht ha hR0,
      IntegralMixedRoadmapProperCritical.parentWord, IntegralMixedRoadmapProperCritical.fullWord,
      pairFst_pair, pairSnd_pair, hp, hf, true_and, fields_packet hn ht ha hR0,
      IntegralMixedRoadmapProperCritical.joint, Q]
  exact hnativ.trans ((and_congr_right fun hg => and_congr hfields (htail hg)).trans
    (and_congr (guard_root Q _ hr) Iff.rfl))

private theorem cast_inverse {A B : Type} (h : A = B) (x : B) :
    Eq.mp h (Eq.mp h.symm x) = x := by
  cases h
  rfl

private theorem full_width (q : List Bool) :
    IntegralMixedRoadmapProperCritical.fullWidth hn ht ha hR0 q =
      SquareSampleCompleteVertices.width
        (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false true)
        (query n q) := by
  unfold IntegralMixedRoadmapProperCritical.fullWidth
  rw [native_canonical hn ht ha hR0]

private theorem parent_width (q : List Bool) :
    IntegralMixedRoadmapProperCritical.parentWidth hn ht ha hR0 q =
      SquareSampleCompleteVertices.width
        (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false false)
        (query n q) := by
  unfold IntegralMixedRoadmapProperCritical.parentWidth
  rw [native_canonical hn ht ha hR0]

/-- Exact native NoCritical incidence on one shared witness bundle. BOTH
prepared words are eliminated using actual complete samplers, including fresh
allocation before the parent word enters AUX. No parent word, native guard,
homomorphism, solvability, or model is assumed. -/
theorem noCritical_iff (q : List Bool)
    (hL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (IntegralMixedRoadmapAtomic.root q) ≤
      R0 (IntegralMixedRoadmapAtomic.original q))
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
        (IntegralMixedPhysicalCriticalQuery.root (query n q)) ≤ R0 (IntegralMixedRoadmapAtomic.original q))
    (ho : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q))
    (original : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (IntegralMixedRoadmapAtomic.context q))
    (heO : HEq (SquareSampleCompleteVertices.candidate
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR0) false)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q) ho).val original) :
    IntegralMixedRoadmapProperCritical.NoCritical hn ht ha hR0 q ↔
      Holds hn ht ha q ((2 : ℝ)^R0 (IntegralMixedRoadmapAtomic.original q)) original := by
  have hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root (query n q)) ≤
      IntegralMixedOriginalRegularSource.radius R0 (IntegralMixedPhysicalCriticalQuery.root (query n q)) := by
    rw [radius_canonical hn ht ha hR0]
    exact hR
  constructor
  · rintro ⟨wF, _, wP, _, hw⟩
    let Q := IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q wP)
    have hg := hw.1
    rw [critical_packet hn ht ha hR0] at hg
    have hp := hw.2.1
    simp only [critical_packet hn ht ha hR0, IntegralMixedRoadmapProperCritical.parentWord, pairSnd_pair] at hp
    have hf := hw.2.2.1
    simp only [critical_packet hn ht ha hR0, IntegralMixedRoadmapProperCritical.fullWord, pairFst_pair, pairSnd_pair] at hf
    have hr := actual_root hn ht ha hR0 q wP
    have hc := hg.1.1
    rw [hr] at hc
    have hp0 := (valid_context hn ht ha hR0 false Q (query n q) wP hr).mp hp
    have hf0 := (valid_context hn ht ha hR0 true Q (query n q) wF hr).mp hf
    obtain ⟨parent, hpRows, heParent⟩ := CoefficientMarkedCriticalPrefixIncidence.rows_of_word hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) false (query n q) hc hlarge wP hp0
    obtain ⟨rawChild, hfRows, heChild⟩ := CoefficientMarkedCriticalPrefixIncidence.rows_of_word hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) true (query n q) hc hlarge wF hf0
    let child := Eq.mp (full_type hn ht ha q).symm rawChild
    have hfull : fullPoint hn ht ha q child = rawChild := by
      unfold fullPoint child
      exact cast_inverse (full_type hn ht ha q) rawChild
    have hs0 := (IntegralMixedPhysicalCriticalContext.valid_full hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) Q wF).mp hf
    have hs := valid_at _ _ _ wF (full_actual_context hn ht ha hR0 q wP) hs0
    have heP := (CoefficientMarkedCriticalWordContext.candidate_context hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) false Q (query n q) wP hr hp hp0).trans heParent
    have heF := (full_candidate hn ht ha hR0 q wF wP hf hs).symm.trans
      ((CoefficientMarkedCriticalWordContext.candidate_context hn ht ha
        (IntegralMixedOriginalRegularSource.radius_binary hR0) true Q (query n q) wF hr hf hf0).trans
          (heChild.trans (cast_heq (full_type hn ht ha q).symm rawChild).symm))
    have hbody := (witness_iff hn ht ha hR0 q wF wP hL hR ho hp hf hs original child parent heO heF heP).mp hw
    rw [radius_canonical hn ht ha hR0] at hpRows hfRows
    refine ⟨hbody.1, child, parent, ?_, ?_, hbody.2⟩
    · rw [hfull]
      exact hfRows
    · exact hpRows
  · rintro ⟨hg, child, parent, hfRows, hpRows, hfields, hbank, hreject⟩
    have hc := hg.1.1
    rw [← radius_canonical hn ht ha hR0 q] at hpRows hfRows
    obtain ⟨wP, hpSelf, hlP, hePSelf⟩ := CoefficientMarkedCriticalParentWord.exists_self_word hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) (query n q) hc hlarge parent hpRows
    let Q := IntegralMixedRoadmapProperCritical.query hn ht ha hR0 (pair q wP)
    let self := pair (IntegralMixedPhysicalCriticalQuery.root (query n q)) (pair wP [])
    have hr := actual_root hn ht ha hR0 q wP
    have hself : IntegralMixedPhysicalCriticalQuery.root self = IntegralMixedPhysicalCriticalQuery.root (query n q) :=
      pairFst_pair _ _
    have hp := (valid_context hn ht ha hR0 false Q self wP (hr.trans hself.symm)).mpr hpSelf
    have heP := (CoefficientMarkedCriticalWordContext.candidate_context hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) false Q self wP (hr.trans hself.symm) hp hpSelf).trans hePSelf
    obtain ⟨wF, hf0, hlF, heF0⟩ := CoefficientMarkedCriticalPrefixIncidence.exists_word hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) true (query n q) hc hlarge (fullPoint hn ht ha q child) hfRows
    have hf := (valid_context hn ht ha hR0 true (query n q) Q wF hr.symm).mp hf0
    have hs0 := (IntegralMixedPhysicalCriticalContext.valid_full hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) Q wF).mp hf
    have hs := valid_at _ _ _ wF (full_actual_context hn ht ha hR0 q wP) hs0
    have heF := (full_candidate hn ht ha hR0 q wF wP hf hs).symm.trans
      ((CoefficientMarkedCriticalWordContext.candidate_context hn ht ha
        (IntegralMixedOriginalRegularSource.radius_binary hR0) true Q (query n q) wF hr hf hf0).trans
          (heF0.trans (full_heq hn ht ha q child)))
    have hbody := (witness_iff hn ht ha hR0 q wF wP hL hR ho hp hf hs original child parent heO heF heP).mpr
      ⟨hg, hfields, hbank, hreject⟩
    refine ⟨wF, hlF.trans (full_width hn ht ha hR0 q).symm, wP, ?_, hbody⟩
    exact hlP.trans ((CoefficientMarkedCriticalWordContext.width_context hn ht ha
      (IntegralMixedOriginalRegularSource.radius_binary hR0) false self (query n q) hself).trans
        (parent_width hn ht ha hR0 q).symm)

end LeanCanny.Encoding.CoefficientMarkedProperCriticalPredicate
