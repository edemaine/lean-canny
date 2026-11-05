/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedProperCriticalPredicate
/-! # The shared NoCritical formula uses metadata, not sampled word bytes -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedProperCriticalWordErasure
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem query_readers (n : List Bool → ℕ) (q r : List Bool)
    (hc : IntegralMixedRoadmapAtomic.candidate q = IntegralMixedRoadmapAtomic.candidate r)
    (hp : IntegralMixedRoadmapAtomic.payload q = IntegralMixedRoadmapAtomic.payload r) :
    CoefficientMarkedProperCriticalPredicate.query n q = CoefficientMarkedProperCriticalPredicate.query n r := by
  unfold CoefficientMarkedProperCriticalPredicate.query CoefficientMarkedProperCriticalLayout.canonical
    CoefficientMarkedProperCriticalLayout.query CoefficientMarkedProperCriticalLayout.code
    IntegralMixedRoadmapProperCritical.prefixRoot IntegralMixedRoadmapProper.badPacket
    IntegralMixedRoadmapBadProbePacket.prefixWord IntegralMixedRoadmapBadProbePacket.prefixCodes
    IntegralMixedRoadmapBadProbePacket.count IntegralMixedRoadmapBadProbePacket.raw IntegralMixedRoadmapBadProbePacket.packet
  simp only [pairFst_pair, pairSnd_pair]
  unfold IntegralMixedRoadmapProper.labels IntegralMixedRoadmapProper.producer IntegralMixedRoadmapProper.levelIndex
    IntegralMixedRoadmapAtomic.original IntegralMixedRoadmapAtomic.depth
  rw [hc, hp]

theorem context_readers (n : List Bool → ℕ) (q r : List Bool)
    (hc : IntegralMixedRoadmapAtomic.candidate q = IntegralMixedRoadmapAtomic.candidate r)
    (hp : IntegralMixedRoadmapAtomic.payload q = IntegralMixedRoadmapAtomic.payload r) :
    CoefficientMarkedProperCriticalPredicate.context n q = CoefficientMarkedProperCriticalPredicate.context n r :=
  congrArg (fun Q => pair (IntegralMixedPhysicalCriticalQuery.root Q) []) (query_readers n q r hc hp)

theorem atomic_context_readers (q r : List Bool)
    (hc : IntegralMixedRoadmapAtomic.candidate q = IntegralMixedRoadmapAtomic.candidate r)
    (hp : IntegralMixedRoadmapAtomic.payload q = IntegralMixedRoadmapAtomic.payload r) :
    IntegralMixedRoadmapAtomic.context q = IntegralMixedRoadmapAtomic.context r := by
  unfold IntegralMixedRoadmapAtomic.context IntegralMixedRoadmapAtomic.root
  rw [hc, hp]

theorem table_readers (n : List Bool → ℕ) (q r : List Bool)
    (hc : IntegralMixedRoadmapAtomic.candidate q = IntegralMixedRoadmapAtomic.candidate r)
    (hp : IntegralMixedRoadmapAtomic.payload q = IntegralMixedRoadmapAtomic.payload r) :
    CoefficientMarkedProperCriticalPredicate.table n q = CoefficientMarkedProperCriticalPredicate.table n r := by
  unfold CoefficientMarkedProperCriticalPredicate.table IntegralMixedRoadmapBadProbePacket.matchTable
    IntegralMixedRoadmapBadProbePacket.creating IntegralMixedRoadmapBadProbePacket.count
    IntegralMixedRoadmapBadProbePacket.raw IntegralMixedRoadmapProper.badPacket
    IntegralMixedRoadmapBadProbePacket.packet IntegralMixedRoadmapAtomic.original
  simp only [pairFst_pair, pairSnd_pair]
  rw [hc, hp]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic

private noncomputable def predicate (old prepared Q table : List Bool)
    (view : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha prepared →
      CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true Q)
    (β : ℝ) (original : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha old) : Prop :=
  IntegralMixedPhysicalCriticalInterval.Guard n false Q ∧
  ∃ child : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha prepared,
  ∃ parent : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha false Q,
    CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root Q)
      (CoefficientMarkedCriticalBankQuery.stage true Q) (Nat.sub_le _ _) β (view child) ∧
    CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root Q)
      (CoefficientMarkedCriticalBankQuery.stage false Q) (Nat.sub_le _ _) β parent ∧
    CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha old prepared table β original child ∧
    CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha Q β parent (view child) ∧
    ¬ CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha Q β parent

private theorem predicate_heq (old prepared Q table old' prepared' Q' table' : List Bool)
    (view : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha prepared →
      CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true Q)
    (view' : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha prepared' →
      CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true Q')
    (ho : old = old') (hp : prepared = prepared') (hq : Q = Q') (hTable : table = table') (hv : HEq view view') :
    HEq (predicate hn ht ha old prepared Q table view) (predicate hn ht ha old' prepared' Q' table' view') := by
  cases ho
  cases hp
  cases hq
  cases hTable
  cases eq_of_heq hv
  rfl

private theorem cast_function_heq {A B A' B' : Type} (h : A = B) (h' : A' = B')
    (ha : A = A') (hb : B = B') : HEq (@Eq.mp A B h) (@Eq.mp A' B' h') := by
  cases ha
  cases hb
  have hh : h = h' := Subsingleton.elim _ _
  cases hh
  rfl

private theorem fullPoint_heq (q r : List Bool)
    (hc : IntegralMixedRoadmapAtomic.candidate q = IntegralMixedRoadmapAtomic.candidate r)
    (hp : IntegralMixedRoadmapAtomic.payload q = IntegralMixedRoadmapAtomic.payload r) :
    HEq (CoefficientMarkedProperCriticalPredicate.fullPoint hn ht ha q)
      (CoefficientMarkedProperCriticalPredicate.fullPoint hn ht ha r) := by
  unfold CoefficientMarkedProperCriticalPredicate.fullPoint
  exact cast_function_heq _ _
    (congrArg (CoefficientMarkedRecordFieldListIncidence.Point hn ht ha) (context_readers n q r hc hp))
    (congrArg (CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true) (query_readers n q r hc hp))

private theorem factor (q : List Bool) :
    HEq (CoefficientMarkedProperCriticalPredicate.Holds hn ht ha q)
      (predicate hn ht ha (IntegralMixedRoadmapAtomic.context q) (CoefficientMarkedProperCriticalPredicate.context n q)
        (CoefficientMarkedProperCriticalPredicate.query n q) (CoefficientMarkedProperCriticalPredicate.table n q)
        (CoefficientMarkedProperCriticalPredicate.fullPoint hn ht ha q)) := HEq.rfl

/-- ALL metadata and query factories are literal actual ones; only candidate
and history payload are retained, never sampled word bytes. -/
theorem holds_readers_heq (q r : List Bool)
    (hc : IntegralMixedRoadmapAtomic.candidate q = IntegralMixedRoadmapAtomic.candidate r)
    (hp : IntegralMixedRoadmapAtomic.payload q = IntegralMixedRoadmapAtomic.payload r) :
    HEq (CoefficientMarkedProperCriticalPredicate.Holds hn ht ha q)
      (CoefficientMarkedProperCriticalPredicate.Holds hn ht ha r) := by
  have hh := predicate_heq hn ht ha _ _ _ _ _ _ _ _
    (CoefficientMarkedProperCriticalPredicate.fullPoint hn ht ha q)
    (CoefficientMarkedProperCriticalPredicate.fullPoint hn ht ha r)
    (atomic_context_readers q r hc hp) (context_readers n q r hc hp)
    (query_readers n q r hc hp) (table_readers n q r hc hp) (fullPoint_heq hn ht ha q r hc hp)
  exact (factor hn ht ha q).trans (hh.trans (factor hn ht ha r).symm)

private theorem apply_iff {A B : Type} (f : ℝ → A → Prop) (g : ℝ → B → Prop)
    (hf : HEq f g) (β : ℝ) (a : A) (b : B) (ha : HEq a b) : f β a ↔ g β b := by
  cases ha
  cases eq_of_heq hf
  rfl

theorem holds_readers_iff (q r : List Bool)
    (hc : IntegralMixedRoadmapAtomic.candidate q = IntegralMixedRoadmapAtomic.candidate r)
    (hp : IntegralMixedRoadmapAtomic.payload q = IntegralMixedRoadmapAtomic.payload r) (β : ℝ)
    (original : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (IntegralMixedRoadmapAtomic.context q))
    (original' : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (IntegralMixedRoadmapAtomic.context r))
    (he : HEq original original') :
    CoefficientMarkedProperCriticalPredicate.Holds hn ht ha q β original ↔
      CoefficientMarkedProperCriticalPredicate.Holds hn ht ha r β original' :=
  apply_iff _ _ (holds_readers_heq hn ht ha q r hc hp) β original original' he

end LeanCanny.Encoding.CoefficientMarkedProperCriticalWordErasure
