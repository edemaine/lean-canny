/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalInnerBranchTransport
public import LeanCanny.Encoding.CoefficientMarkedProperCriticalPredicate
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldListTransport
/-! # The whole shared NoCritical formula on actual coherent root branches -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedProperCriticalBranchTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def cutoff (q : List Bool) :=
  CoefficientMarkedCriticalInnerBranchTransport.cutoff hn ht ha (CoefficientMarkedProperCriticalPredicate.query n q) +
    CoefficientMarkedRecordFieldListTransport.cutoff hn ht ha
      (pair (IntegralMixedRoadmapAtomic.context q) (CoefficientMarkedProperCriticalPredicate.context n q)) + 1

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) := by
  have hq : CoefficientMarkedProperCriticalPredicate.query n ∈ FP :=
    CoefficientMarkedProperCriticalLayout.canonical_FP hn
  have hp : (fun q => pair (IntegralMixedRoadmapAtomic.context q) (CoefficientMarkedProperCriticalPredicate.context n q)) ∈ FP :=
    mem_FP_pair IntegralMixedRoadmapAtomic.context_FP (CoefficientMarkedProperCriticalLayout.context_FP hn)
  exact (BinaryFn.add ((CoefficientMarkedCriticalInnerBranchTransport.cutoff_binary hn ht ha).comp hq)
    ((CoefficientMarkedRecordFieldListTransport.cutoff_binary hn ht ha).comp hp)).add (BinaryFn.const 1)

private theorem inner_cutoff_le (q : List Bool) :
    CoefficientMarkedCriticalInnerBranchTransport.cutoff hn ht ha (CoefficientMarkedProperCriticalPredicate.query n q) ≤
      cutoff hn ht ha q := by
  unfold cutoff
  omega

private theorem field_cutoff_le (q : List Bool) :
    CoefficientMarkedRecordFieldListTransport.cutoff hn ht ha
      (pair (IntegralMixedRoadmapAtomic.context q) (CoefficientMarkedProperCriticalPredicate.context n q)) ≤
        cutoff hn ht ha q := by
  unfold cutoff
  omega

private noncomputable def fieldCount (q : List Bool) :=
  (CoefficientMarkedRecordRows.symbolic hn ht ha (pairFst (CoefficientMarkedProperCriticalPredicate.context n q))
    (IntegralMixedCausalRecordPlanBits.count (pairFst (CoefficientMarkedProperCriticalPredicate.context n q))) le_rfl).count

private noncomputable def fullCount (q : List Bool) :=
  (CoefficientMarkedRecordRows.symbolic hn ht ha
    (IntegralMixedPhysicalCriticalQuery.root (CoefficientMarkedProperCriticalPredicate.query n q))
    (CoefficientMarkedCriticalBankQuery.stage true (CoefficientMarkedProperCriticalPredicate.query n q)) (Nat.sub_le _ _)).count

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic

private theorem full_count (q : List Bool) : fieldCount hn ht ha q = fullCount hn ht ha q := by
  unfold fieldCount fullCount CoefficientMarkedCriticalBankQuery.stage
    CoefficientMarkedProperCriticalPredicate.context CoefficientMarkedProperCriticalPredicate.query
    CoefficientMarkedProperCriticalLayout.context CoefficientMarkedProperCriticalLayout.root
  simp only [pairFst_pair, ite_true, Nat.sub_zero]

private theorem cast_heq {A B : Type} (h : A = B) (x : A) : HEq (Eq.mp h x) x := by
  cases h
  rfl

private theorem cast_continuous {N M : ℕ} (h : N = M) :
    Continuous (Eq.mp (congrArg (fun K => Fin K → ℝ) h)) := by
  cases h
  exact continuous_id

private noncomputable def fieldPoint (q : List Bool)
    (z : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true (CoefficientMarkedProperCriticalPredicate.query n q)) :
    CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (CoefficientMarkedProperCriticalPredicate.context n q) :=
  Eq.mp (congrArg (fun K => Fin K → ℝ) (full_count hn ht ha q).symm) z

private theorem fieldPoint_heq (q : List Bool)
    (z : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true (CoefficientMarkedProperCriticalPredicate.query n q)) :
    HEq (fieldPoint hn ht ha q z) z := cast_heq _ z

private theorem field_full (q : List Bool)
    (z : CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (CoefficientMarkedProperCriticalPredicate.context n q)) :
    fieldPoint hn ht ha q (CoefficientMarkedProperCriticalPredicate.fullPoint hn ht ha q z) = z := by
  exact eq_of_heq ((fieldPoint_heq hn ht ha q _).trans (CoefficientMarkedProperCriticalPredicate.full_heq hn ht ha q z))

private theorem full_field (q : List Bool)
    (z : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true (CoefficientMarkedProperCriticalPredicate.query n q)) :
    CoefficientMarkedProperCriticalPredicate.fullPoint hn ht ha q (fieldPoint hn ht ha q z) = z := by
  exact eq_of_heq ((CoefficientMarkedProperCriticalPredicate.full_heq hn ht ha q _).trans (fieldPoint_heq hn ht ha q z))

private noncomputable def fieldCurve (q : List Bool) {a b : ℝ}
    (x : C(Ioo a b, CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true (CoefficientMarkedProperCriticalPredicate.query n q))) :
    C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (CoefficientMarkedProperCriticalPredicate.context n q)) :=
  ⟨fun u => fieldPoint hn ht ha q (x u), (cast_continuous (full_count hn ht ha q).symm).comp x.continuous⟩

attribute [local irreducible] CoefficientMarkedProperCriticalPredicate.query
  CoefficientMarkedProperCriticalPredicate.context IntegralMixedRoadmapAtomic.context

private theorem fieldCurve_apply (q : List Bool) {a b : ℝ}
    (x : C(Ioo a b, CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true (CoefficientMarkedProperCriticalPredicate.query n q)))
    (u : Ioo a b) : fieldCurve hn ht ha q x u = fieldPoint hn ht ha q (x u) := by
  unfold fieldCurve
  rfl

private theorem dependent_heq {α : Sort*} {B : α → Sort*} (f : (a : α) → B a)
    (a b : α) (h : a = b) : HEq (f a) (f b) := by
  subst b
  rfl

private theorem apply_iff {A B : Type} (f : A → Prop) (g : B → Prop) (hf : HEq f g)
    (a : A) (b : B) (ha : HEq a b) : f a ↔ g b := by
  cases ha
  cases eq_of_heq hf
  rfl

attribute [local irreducible] CoefficientMarkedProperCriticalPredicate.table fieldPoint fieldCurve

private theorem field_rows (q : List Bool) (β : ℝ)
    (z : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true (CoefficientMarkedProperCriticalPredicate.query n q))
    (hz : CoefficientMarkedRecordRootBranches.RowsAt hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root (CoefficientMarkedProperCriticalPredicate.query n q))
      (CoefficientMarkedCriticalBankQuery.stage true (CoefficientMarkedProperCriticalPredicate.query n q)) (Nat.sub_le _ _) β z) :
    CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (pairFst (CoefficientMarkedProperCriticalPredicate.context n q))
      (IntegralMixedCausalRecordPlanBits.count (pairFst (CoefficientMarkedProperCriticalPredicate.context n q))) le_rfl β
      (fieldPoint hn ht ha q z) := by
  have hr : IntegralMixedPhysicalCriticalQuery.root (CoefficientMarkedProperCriticalPredicate.query n q) =
      pairFst (CoefficientMarkedProperCriticalPredicate.context n q) := by
    unfold CoefficientMarkedProperCriticalPredicate.context CoefficientMarkedProperCriticalPredicate.query
      CoefficientMarkedProperCriticalLayout.context CoefficientMarkedProperCriticalLayout.root
    exact (pairFst_pair _ _).symm
  have hh := dependent_heq (fun ctx => CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl β) _ _ hr
  exact (apply_iff _ _ hh z (fieldPoint hn ht ha q z) (fieldPoint_heq hn ht ha q z).symm).mp hz

/-- The complete prepared parent/full families are constructed internally.
The original curve, prepared FULL curve and prepared PARENT curve share every
conjunct of Holds; no field/incidence/guard compatibility premise is supplied. -/
theorem holds_on_root_curve (q : List Bool) {a b : ℝ}
    (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a)
    (original : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha (IntegralMixedRoadmapAtomic.context q)))
    (hOriginal : ∀ t : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha
      (pairFst (IntegralMixedRoadmapAtomic.context q))
      (IntegralMixedCausalRecordPlanBits.count (pairFst (IntegralMixedRoadmapAtomic.context q))) le_rfl t.val (original t))
    (u v : Ioo a b) :
    CoefficientMarkedProperCriticalPredicate.Holds hn ht ha q u.val (original u) ↔
      CoefficientMarkedProperCriticalPredicate.Holds hn ht ha q v.val (original v) := by
  by_cases hg : IntegralMixedPhysicalCriticalInterval.Guard n false (CoefficientMarkedProperCriticalPredicate.query n q)
  · have hc := hg.1.1
    have hInner : (2 : ℝ)^CoefficientMarkedCriticalInnerBranchTransport.cutoff hn ht ha
        (CoefficientMarkedProperCriticalPredicate.query n q) ≤ a :=
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (inner_cutoff_le hn ht ha q)).trans ha0
    have hField : (2 : ℝ)^CoefficientMarkedRecordFieldListTransport.cutoff hn ht ha
        (pair (IntegralMixedRoadmapAtomic.context q) (CoefficientMarkedProperCriticalPredicate.context n q)) ≤ a :=
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (field_cutoff_le hn ht ha q)).trans ha0
    have hrow : (2 : ℝ)^CoefficientMarkedRecordCartesianRows.cutoff hn ht ha
        (IntegralMixedPhysicalCriticalQuery.root (CoefficientMarkedProperCriticalPredicate.query n q)) ≤ a :=
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (CoefficientMarkedCriticalInnerBranchTransport.row_cutoff_le hn ht ha _)).trans hInner
    obtain ⟨parentCurve, _, hpRows, hpCoverage⟩ := CoefficientMarkedRecordRootBranches.exists_branches hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root (CoefficientMarkedProperCriticalPredicate.query n q))
      (CoefficientMarkedCriticalBankQuery.stage false (CoefficientMarkedProperCriticalPredicate.query n q)) (Nat.sub_le _ _) hrow u
    obtain ⟨childCurve, _, hcRows, hcCoverage⟩ := CoefficientMarkedRecordRootBranches.exists_branches hn ht ha
      (IntegralMixedPhysicalCriticalQuery.root (CoefficientMarkedProperCriticalPredicate.query n q))
      (CoefficientMarkedCriticalBankQuery.stage true (CoefficientMarkedProperCriticalPredicate.query n q)) (Nat.sub_le _ _) hrow u
    have htail (p : CoefficientMarkedRecordRootBranches.RootIndex hn ht ha
        (IntegralMixedPhysicalCriticalQuery.root (CoefficientMarkedProperCriticalPredicate.query n q))
        (CoefficientMarkedCriticalBankQuery.stage false (CoefficientMarkedProperCriticalPredicate.query n q)) (Nat.sub_le _ _) u parentCurve)
      (c : CoefficientMarkedRecordRootBranches.RootIndex hn ht ha
        (IntegralMixedPhysicalCriticalQuery.root (CoefficientMarkedProperCriticalPredicate.query n q))
        (CoefficientMarkedCriticalBankQuery.stage true (CoefficientMarkedProperCriticalPredicate.query n q)) (Nat.sub_le _ _) u childCurve) :
      (CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha (IntegralMixedRoadmapAtomic.context q)
        (CoefficientMarkedProperCriticalPredicate.context n q) (CoefficientMarkedProperCriticalPredicate.table n q)
        u.val (original u) (fieldPoint hn ht ha q (childCurve c.val u)) ∧
      CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha (CoefficientMarkedProperCriticalPredicate.query n q)
        u.val (parentCurve p.val u) (childCurve c.val u) ∧
      ¬ CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha (CoefficientMarkedProperCriticalPredicate.query n q)
        u.val (parentCurve p.val u)) ↔
      (CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha (IntegralMixedRoadmapAtomic.context q)
        (CoefficientMarkedProperCriticalPredicate.context n q) (CoefficientMarkedProperCriticalPredicate.table n q)
        v.val (original v) (fieldPoint hn ht ha q (childCurve c.val v)) ∧
      CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha (CoefficientMarkedProperCriticalPredicate.query n q)
        v.val (parentCurve p.val v) (childCurve c.val v) ∧
      ¬ CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha (CoefficientMarkedProperCriticalPredicate.query n q)
        v.val (parentCurve p.val v)) := by
      have hFields := CoefficientMarkedRecordFieldListTransport.holds_on_curves hn ht ha
        (IntegralMixedRoadmapAtomic.context q) (CoefficientMarkedProperCriticalPredicate.context n q)
        (CoefficientMarkedProperCriticalPredicate.table n q) hField original (fieldCurve hn ht ha q (childCurve c.val))
        hOriginal (fun t => by simpa only [fieldCurve_apply] using field_rows hn ht ha q t.val _ (hcRows c t)) u v
      simp only [fieldCurve_apply] at hFields
      have hBank := CoefficientMarkedCriticalInnerBranchTransport.bank_on_root_curves hn ht ha
        (CoefficientMarkedProperCriticalPredicate.query n q) hc hInner (parentCurve p.val) (childCurve c.val) (hpRows p) (hcRows c) u v
      have hCounter := CoefficientMarkedCriticalInnerBranchTransport.counterexample_on_root_curve hn ht ha
        (CoefficientMarkedProperCriticalPredicate.query n q) hc hInner (parentCurve p.val) (hpRows p) u v
      exact and_congr hFields (and_congr hBank (not_congr hCounter))
    constructor
    · rintro ⟨_, child, parent, hf, hp, hFields, hBank, hCounter⟩
      obtain ⟨p, hep, _⟩ := (hpCoverage u parent).mp hp
      obtain ⟨c, hec, _⟩ := (hcCoverage u (CoefficientMarkedProperCriticalPredicate.fullPoint hn ht ha q child)).mp hf
      have hin : CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha (IntegralMixedRoadmapAtomic.context q)
          (CoefficientMarkedProperCriticalPredicate.context n q) (CoefficientMarkedProperCriticalPredicate.table n q)
          u.val (original u) (fieldPoint hn ht ha q (childCurve c.val u)) ∧
        CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha (CoefficientMarkedProperCriticalPredicate.query n q)
          u.val (parentCurve p.val u) (childCurve c.val u) ∧
        ¬ CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha (CoefficientMarkedProperCriticalPredicate.query n q)
          u.val (parentCurve p.val u) := by
        simpa only [hep, hec, field_full] using And.intro hFields (And.intro hBank hCounter)
      have hout := (htail p c).mp hin
      refine ⟨hg, fieldPoint hn ht ha q (childCurve c.val v), parentCurve p.val v, ?_, hpRows p v, hout.1, ?_, hout.2.2⟩
      · simpa only [full_field] using hcRows c v
      · simpa only [full_field] using hout.2.1
    · rintro ⟨_, child, parent, hf, hp, hFields, hBank, hCounter⟩
      obtain ⟨p, hep, _⟩ := (hpCoverage v parent).mp hp
      obtain ⟨c, hec, _⟩ := (hcCoverage v (CoefficientMarkedProperCriticalPredicate.fullPoint hn ht ha q child)).mp hf
      have hin : CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha (IntegralMixedRoadmapAtomic.context q)
          (CoefficientMarkedProperCriticalPredicate.context n q) (CoefficientMarkedProperCriticalPredicate.table n q)
          v.val (original v) (fieldPoint hn ht ha q (childCurve c.val v)) ∧
        CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha (CoefficientMarkedProperCriticalPredicate.query n q)
          v.val (parentCurve p.val v) (childCurve c.val v) ∧
        ¬ CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha (CoefficientMarkedProperCriticalPredicate.query n q)
          v.val (parentCurve p.val v) := by
        simpa only [hep, hec, field_full] using And.intro hFields (And.intro hBank hCounter)
      have hout := (htail p c).mpr hin
      refine ⟨hg, fieldPoint hn ht ha q (childCurve c.val u), parentCurve p.val u, ?_, hpRows p u, hout.1, ?_, hout.2.2⟩
      · simpa only [full_field] using hcRows c u
      · simpa only [full_field] using hout.2.1
  · simp only [CoefficientMarkedProperCriticalPredicate.Holds, hg, false_and]

end LeanCanny.Encoding.CoefficientMarkedProperCriticalBranchTransport
