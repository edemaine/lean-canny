/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalIntervalSign
public import LeanCanny.Encoding.CoefficientMarkedCriticalBankSign
public import LeanCanny.Encoding.CoefficientMarkedCriticalPredicateContext
/-! # Coherent transport of the complete critical counterexample search -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalInnerBranchTransport
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def cutoff (q : List Bool) := CoefficientMarkedCriticalBankSign.cutoff hn ht ha q +
  CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) +
    CoefficientMarkedCriticalIntervalSign.cutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) + 1

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) :=
  ((BinaryFn.add (CoefficientMarkedCriticalBankSign.cutoff_binary hn ht ha)
    ((CoefficientMarkedRecordCriticalBranchSign.cutoff_binary hn ht ha).comp pairFst_mem_FP)).add
    ((CoefficientMarkedCriticalIntervalSign.cutoff_binary hn ht ha).comp pairFst_mem_FP)).add (BinaryFn.const 1)

private theorem bank_cutoff_le (q : List Bool) : CoefficientMarkedCriticalBankSign.cutoff hn ht ha q ≤ cutoff hn ht ha q := by
  unfold cutoff
  omega

private theorem critical_cutoff_le (q : List Bool) :
    CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) ≤ cutoff hn ht ha q := by
  unfold cutoff
  omega

private theorem interval_cutoff_le (q : List Bool) :
    CoefficientMarkedCriticalIntervalSign.cutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) ≤ cutoff hn ht ha q := by
  unfold cutoff
  omega

theorem row_cutoff_le (q : List Bool) :
    CoefficientMarkedRecordCartesianRows.cutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) ≤ cutoff hn ht ha q :=
  (CoefficientMarkedCriticalBankSign.row_cutoff_le hn ht ha q).trans (bank_cutoff_le hn ht ha q)

private theorem bank_evaluation (child : Bool) (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) (k : ℕ) (β : ℝ)
    (z : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha child q) :
    (CoefficientMarkedCriticalBankVariables.polynomial hn ht ha child q hc i k).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation β) z =
      (CoefficientMarkedCriticalBankQuery.physical hn ht ha child q i k).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation β) (CoefficientMarkedCriticalBankIncidence.natural z) :=
  CoefficientFinitePhysicalQuery.evaluation _ _ _ (CoefficientMarkedCriticalBankVariables.variable_box hn ht ha child q hc i k) z

private theorem correlation_empty (q : List Bool) :
    CoefficientMarkedCriticalCorrelationIncidence.polynomial hn ht ha q =
      CoefficientMarkedRecordCriticalFullQuery.polynomial hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
        (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) le_rfl []
        (IntegralMixedPhysicalCriticalPrefixes.birth n false false q) := by
  unfold CoefficientMarkedCriticalCorrelationIncidence.polynomial
  exact CoefficientMarkedCriticalRootContext.correlation_aux hn ht ha _ _ le_rfl q [] _

private theorem zero_iff {x y : ℝ} (hs : SignType.sign x = SignType.sign y) : x = 0 ↔ y = 0 := by
  have hx : SignType.sign x = 0 ↔ x = 0 := sign_eq_zero_iff
  have hy : SignType.sign y = 0 ↔ y = 0 := sign_eq_zero_iff
  exact hx.symm.trans ((Iff.of_eq (congrArg (fun s : SignType => s = 0) hs)).trans hy)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic CoefficientMarkedCriticalBankVariables.polynomial
  CoefficientMarkedCriticalBankQuery.physical CoefficientMarkedRecordCriticalFullQuery.polynomial
  CoefficientMarkedCriticalCorrelationIncidence.polynomial CoefficientMarkedCriticalIntervalQuery.polynomial
  cutoff

/-- Bank incidence is preserved using the SAME two complete row-root curves.
All catalogue coordinates and derivative orders are checked. -/
theorem bank_on_root_curves (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a)
    (parent : C(Ioo a b, CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha false q))
    (child : C(Ioo a b, CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true q))
    (hp : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage false q) (Nat.sub_le _ _) u.val (parent u))
    (hf : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage true q) (Nat.sub_le _ _) u.val (child u)) (u v : Ioo a b) :
    CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha q u.val (parent u) (child u) ↔
      CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha q v.val (parent v) (child v) := by
  have hstart : (2 : ℝ)^CoefficientMarkedCriticalBankSign.cutoff hn ht ha q ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (bank_cutoff_le hn ht ha q)).trans ha0
  unfold CoefficientMarkedCriticalBankIncidence.Agrees
  apply forall_congr'
  intro i
  apply forall_congr'
  intro k
  apply forall_congr'
  intro _
  have hsP := CoefficientMarkedCriticalBankSign.sign_on_root_curve hn ht ha false q hc hstart parent hp i k u v
  have hsF := CoefficientMarkedCriticalBankSign.sign_on_root_curve hn ht ha true q hc hstart child hf i k u v
  rw [bank_evaluation, bank_evaluation] at hsP hsF
  exact Iff.of_eq (congrArg₂ Eq hsP hsF)

/-- Correlation and both endpoint inequalities accompany bank incidence on
the SAME two raw curves. No separate existential branch is selected. -/
theorem tests_on_root_curves (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a)
    (parent : C(Ioo a b, CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha false q))
    (child : C(Ioo a b, CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true q))
    (hp : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage false q) (Nat.sub_le _ _) u.val (parent u))
    (hf : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage true q) (Nat.sub_le _ _) u.val (child u)) (u v : Ioo a b) :
    CoefficientMarkedCriticalIntervalPredicate.Tests hn ht ha q u.val (parent u) (child u) ↔
      CoefficientMarkedCriticalIntervalPredicate.Tests hn ht ha q v.val (parent v) (child v) := by
  have hstartC : (2 : ℝ)^CoefficientMarkedRecordCriticalBranchSign.cutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (critical_cutoff_le hn ht ha q)).trans ha0
  have hstartI : (2 : ℝ)^CoefficientMarkedCriticalIntervalSign.cutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (interval_cutoff_le hn ht ha q)).trans ha0
  have hs := CoefficientMarkedRecordCriticalBranchSign.sign_on_root_curve hn ht ha
    (IntegralMixedPhysicalCriticalQuery.root q) hstartC child hf (IntegralMixedPhysicalCriticalPrefixes.birth n false false q) u v
  rw [← correlation_empty hn ht ha q] at hs
  have hz : (CoefficientMarkedCriticalCorrelationIncidence.polynomial hn ht ha q).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation u.val) (child u) = 0 ↔
      (CoefficientMarkedCriticalCorrelationIncidence.polynomial hn ht ha q).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation v.val) (child v) = 0 := zero_iff hs
  have hi (upper : Bool) := CoefficientMarkedCriticalIntervalSign.sign_on_root_curve hn ht ha upper
    (IntegralMixedPhysicalCriticalQuery.root q) hstartI child hf u v
  unfold CoefficientMarkedCriticalIntervalPredicate.Tests
  exact and_congr (bank_on_root_curves hn ht ha q hc ha0 parent child hp hf u v)
    (and_congr hz (and_congr (Iff.of_eq (congrArg (fun s : SignType => s = 1) (hi false)))
      (Iff.of_eq (congrArg (fun s : SignType => s = 1) (hi true)))))

/-- Complete child coverage is CONSTRUCTED once. Thus existence and absence
of a critical counterexample are preserved along any actual parent root curve,
without a supplied child family, incidence oracle, or selected witness. -/
theorem counterexample_on_root_curve (q : List Bool)
    (hc : 0 < IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha q ≤ a)
    (parent : C(Ioo a b, CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha false q))
    (hp : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (CoefficientMarkedCriticalBankQuery.stage false q) (Nat.sub_le _ _) u.val (parent u)) (u v : Ioo a b) :
    CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha q u.val (parent u) ↔
      CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha q v.val (parent v) := by
  have hrow : (2 : ℝ)^CoefficientMarkedRecordCartesianRows.cutoff hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (row_cutoff_le hn ht ha q)).trans ha0
  obtain ⟨curve, _, hroots, hcoverage⟩ := CoefficientMarkedRecordRootBranches.exists_branches hn ht ha
    (IntegralMixedPhysicalCriticalQuery.root q) (CoefficientMarkedCriticalBankQuery.stage true q) (Nat.sub_le _ _) hrow u
  constructor
  · rintro ⟨child, hchild, htests⟩
    obtain ⟨l, he, _⟩ := (hcoverage u child).mp hchild
    rw [← he] at htests
    exact ⟨curve l.val v, hroots l v,
      (tests_on_root_curves hn ht ha q hc ha0 parent (curve l.val) hp (hroots l) u v).mp htests⟩
  · rintro ⟨child, hchild, htests⟩
    obtain ⟨l, he, _⟩ := (hcoverage v child).mp hchild
    rw [← he] at htests
    exact ⟨curve l.val u, hroots l u,
      (tests_on_root_curves hn ht ha q hc ha0 parent (curve l.val) hp (hroots l) u v).mpr htests⟩

end LeanCanny.Encoding.CoefficientMarkedCriticalInnerBranchTransport
