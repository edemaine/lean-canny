/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutWordValue
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedContext
/-! # Native full-cut comparisons on own words along one actual row curve -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutComparison
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial PrincipalSubresultant Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem comparison_packet (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (parent terminal : List Bool → List Bool) (d left right : List Bool → ℕ)
    (hp : ∀ q, 0 < (IntegralMixedFramedHistoryFamilyBits.family P D H).birth (terminal q))
    (hf : ∀ r, 1 ≤ F r) (hd : ∀ key, IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (q w : List Bool) :
    pair q w ∈ IntegralFramedFullCutOpenInterval.language P D H L F C hs parent terminal d left right hp hf hd ↔
      d q = 0 ∨
      IntegralFramedFullCutIntervalStatistic.value P D H L F C hs parent terminal d left hp hf hd 1 true (pair (pair q w) []) =
      IntegralFramedFullCutIntervalStatistic.value P D H L F C hs parent terminal d right hp hf hd 1 false (pair (pair q w) []) := by
  simp only [IntegralFramedFullCutOpenInterval.language, Set.mem_ofPred_eq, pairFst_pair,
    IntegralFramedFullCutOpenInterval.endpoint, IntegralFramedFullCutOpenInterval.integerCode_injective.eq_iff]

private theorem natural_ext {N M : ℕ} (hc : N = M) (z : Fin N → ℝ) (w : Fin M → ℝ)
    (he : CoefficientFinitePhysicalQuery.natural z = CoefficientFinitePhysicalQuery.natural w) : HEq z w := by
  cases hc
  apply heq_of_eq
  funext i
  have hi := congrFun he i.val
  simpa only [CoefficientFinitePhysicalQuery.natural, dite_eq_left i.isLt] using hi

private theorem input_count (B : IntegralFramedBankQuery.Bank) (q : List Bool) :
    (IntegralFramedPhysicalBankTerm.input B).count q = IntegralFramedPhysicalSquare.count B.parameters B.plan (B.key q) := rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
local notation "CTX" => CoefficientMarkedRecordFullCutInstalled.context (n := n)

noncomputable def cutoff := CoefficientMarkedRecordFullCutPrincipalSign.cutoff hn ht ha
theorem cutoff_binary : BinaryFn (cutoff hn ht ha) := CoefficientMarkedRecordFullCutPrincipalSign.cutoff_binary hn ht ha
theorem effective_le (ctx : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ cutoff hn ht ha ctx :=
  (CoefficientMarkedRecordCartesianRows.effectiveCutoff_le hn ht ha ctx).trans
    (CoefficientMarkedRecordFullCutPrincipalSign.row_cutoff_le hn ht ha ctx)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

theorem statistic_on_curve (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (left right : ℕ) (side negative : Bool) {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)
    (hRlarge : cutoff hn ht ha ctx ≤ R ctx) (hSlarge : cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutPrincipalSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx)
    (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (CTX ctx k left right) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (CTX ctx k left right) wS hwS).val (x v)) :
    CoefficientMarkedRecordFullCutWordValue.statistic hn ht ha hR side negative (CTX ctx k left right) wR =
      CoefficientMarkedRecordFullCutWordValue.statistic hn ht ha hS side negative (CTX ctx k left right) wS := by
  have HR := CoefficientMarkedRecordFullCutWordValue.value_eq hn ht ha hR ctx k hk hc left right side negative
    ((effective_le hn ht ha ctx).trans hRlarge) wR hwR (x u) hjR
  have HS := CoefficientMarkedRecordFullCutWordValue.value_eq hn ht ha hS ctx k hk hc left right side negative
    ((effective_le hn ht ha ctx).trans hSlarge) wS hwS (x v) hjS
  have HV : permanencesMinusVariations ((List.range (CoefficientMarkedRecordFullCutPrincipalHeight.degree hn ht ha ctx k+1)).reverse.map
      (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordFullCutLex.principal hn ht ha ctx k hk (if side then right else left) negative j ((2 : ℝ)^R ctx) (x u)))) =
      permanencesMinusVariations ((List.range (CoefficientMarkedRecordFullCutPrincipalHeight.degree hn ht ha ctx k+1)).reverse.map
      (fun j => RealIteratedTarski.lex (CoefficientMarkedRecordFullCutLex.principal hn ht ha ctx k hk (if side then right else left) negative j ((2 : ℝ)^S ctx) (x v)))) := by
    apply permanencesMinusVariations_congr
    simp only [List.map_map]
    apply List.map_congr_left
    intro j _
    simpa only [Function.comp_apply, hu, hv] using CoefficientMarkedRecordFullCutLex.lex_on_root_curve hn ht ha ctx ha0 x hx
      k hk hc (if side then right else left) negative j u v
  exact HR.trans (HV.trans HS.symm)

variable {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false

/-- Only AUX changes here: each radius keeps its own native word. -/
theorem candidate_context (q d w : List Bool) (hroot : pairFst q = pairFst d)
    (hq : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) q w)
    (hd : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) d w) :
    HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) q w hq).val
      (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) d w hd).val := by
  have hk := IntegralMixedPhysicalMarkedContext.key_eq hn ht ha hR q d hroot
  have hc := (input_count B q).trans ((congrArg (IntegralFramedPhysicalSquare.count (B).parameters (B).plan) hk).trans (input_count B d).symm)
  have hNatural := IntegralMixedPhysicalMarkedContext.natural_eq hn ht ha hR q d w hroot hq hd
  change CoefficientFinitePhysicalQuery.natural
      (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) q w hq).val =
    CoefficientFinitePhysicalQuery.natural
      (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) d w hd).val at hNatural
  exact natural_ext hc _ _ hNatural

theorem comparison_at (q w : List Bool) :
    pair q w ∈ IntegralMixedPhysicalCutOpenInterval.comparison hn ht ha hR false ↔
      IntegralMixedPhysicalCutOpenInterval.degree hn ht ha hR false q = 0 ∨
      CoefficientMarkedRecordFullCutWordValue.statistic hn ht ha hR false true q w =
        CoefficientMarkedRecordFullCutWordValue.statistic hn ht ha hR true false q w :=
  comparison_packet (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha hR false) (B).key
    (IntegralMixedPhysicalCutOpenInterval.degree hn ht ha hR false)
    (IntegralMixedPhysicalCutOpenInterval.selected false) (IntegralMixedPhysicalCutOpenInterval.selected true)
    (B).positive (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR false)
    (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR false) q w

/-- Actual native comparison truth, on OWN complete words along ANY same
actual full-row curve. Constant factors retain the literal degree-zero bypass. -/
theorem comparison_on_curve (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (left right : ℕ) {S : List Bool → ℕ} (hS : BinaryFn S)
    (hRlarge : cutoff hn ht ha ctx ≤ R ctx) (hSlarge : cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutPrincipalSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx)
    (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (CTX ctx k left right) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) (CTX ctx k left right) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) (CTX ctx k left right) wS hwS).val (x v)) :
    pair (CTX ctx k left right) wR ∈ IntegralMixedPhysicalCutOpenInterval.comparison hn ht ha hR false ↔
      pair (CTX ctx k left right) wS ∈ IntegralMixedPhysicalCutOpenInterval.comparison hn ht ha hS false := by
  rw [comparison_at hn ht ha hR, comparison_at hn ht ha hS]
  have HD := (CoefficientMarkedRecordFullCutInstalled.degree_context hn ht ha hR ctx k left right hk hc).trans
    (CoefficientMarkedRecordFullCutInstalled.degree_context hn ht ha hS ctx k left right hk hc).symm
  have HL := statistic_on_curve hn ht ha ctx k hk hc left right false true hR hS hRlarge hSlarge ha0 x hx u v hu hv wR wS hwR hwS hjR hjS
  have HR := statistic_on_curve hn ht ha ctx k hk hc left right true false hR hS hRlarge hSlarge ha0 x hx u v hu hv wR wS hwR hwS hjR hjS
  exact or_congr (Iff.of_eq (congrArg (fun d => d = 0) HD)) (Iff.of_eq (congrArg₂ (fun a b : ℤ => a = b) HL HR))

/-- This consumes the exact sampleContext words and readbacks produced by
RootBranches/FullRealization and FullCutTransport. Interval AUX conversion is
derived internally, separately at each radius. -/
theorem comparison_on_sampled_curve (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (left right : ℕ) {S : List Bool → ℕ} (hS : BinaryFn S)
    (hRlarge : cutoff hn ht ha ctx ≤ R ctx) (hSlarge : cutoff hn ht ha ctx ≤ S ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha ctx ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutPrincipalSign.count hn ht ha ctx) → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R ctx) (hv : v.val = (2 : ℝ)^S ctx)
    (wR wS : List Bool)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wR)
    (hwS : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wS)
    (hjR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wR hwR).val (x u))
    (hjS : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false)
      (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wS hwS).val (x v)) :
    pair (CTX ctx k left right) wR ∈ IntegralMixedPhysicalCutOpenInterval.comparison hn ht ha hR false ↔
      pair (CTX ctx k left right) wS ∈ IntegralMixedPhysicalCutOpenInterval.comparison hn ht ha hS false := by
  have hroot : pairFst (CTX ctx k left right) = pairFst (IntegralMixedPhysicalMarkedTest.sampleContext ctx) :=
    (CoefficientMarkedRecordFullCutInstalled.context_root (n := n) ctx k left right).trans (pairFst_pair ctx []).symm
  let hRctx := (IntegralMixedPhysicalMarkedContext.valid_iff hn ht ha hR
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (CTX ctx k left right) wR hroot.symm).mp hwR
  let hSctx := (IntegralMixedPhysicalMarkedContext.valid_iff hn ht ha hS
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) (CTX ctx k left right) wS hroot.symm).mp hwS
  have hJR := (candidate_context hn ht ha hR (CTX ctx k left right)
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wR hroot hRctx hwR).trans hjR
  have hJS := (candidate_context hn ht ha hS (CTX ctx k left right)
    (IntegralMixedPhysicalMarkedTest.sampleContext ctx) wS hroot hSctx hwS).trans hjS
  exact comparison_on_curve hn ht ha hR ctx k hk hc left right hS hRlarge hSlarge ha0 x hx u v hu hv wR wS hRctx hSctx hJR hJS

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutComparison
