/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldSign
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldListIncidence
/-! # One original cutoff for streamed Field matches on two actual root curves -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFieldListTransport
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

def packet (q : List Bool) := IntegralMixedPhysicalFieldEquality.packet (pairFst q) [] (pairSnd q) [] 0 0

theorem packet_FP : packet ∈ FP := by
  exact mem_FP_pair (mem_FP_pair pairFst_mem_FP (constFn_mem_FP []))
    (mem_FP_pair (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP []))
      (mem_FP_pair (constFn_mem_FP (BinaryNatCode.encode 0)) (constFn_mem_FP (BinaryNatCode.encode 0))))

noncomputable def cutoff (q : List Bool) :=
  CoefficientMarkedRecordFieldSign.cutoff hn ht ha false (packet q)+
    CoefficientMarkedRecordFieldSign.cutoff hn ht ha true (packet q)+1

theorem cutoff_binary : BinaryFn (cutoff hn ht ha) := by
  have HL : BinaryFn (fun q => CoefficientMarkedRecordFieldSign.cutoff hn ht ha false (packet q)) :=
    (CoefficientMarkedRecordFieldSign.cutoff_binary hn ht ha false).comp packet_FP
  have HR : BinaryFn (fun q => CoefficientMarkedRecordFieldSign.cutoff hn ht ha true (packet q)) :=
    (CoefficientMarkedRecordFieldSign.cutoff_binary hn ht ha true).comp packet_FP
  exact (HL.add HR).add (BinaryFn.const 1)

theorem member_cutoff_le (right : Bool) (cL cR : List Bool) (a b : ℕ) :
    CoefficientMarkedRecordFieldSign.cutoff hn ht ha right
      (IntegralMixedPhysicalFieldEquality.packet cL [] cR [] a b) ≤ cutoff hn ht ha (pair cL cR) := by
  rw [CoefficientMarkedRecordFieldSign.cutoff_packet hn ht ha right cL cR [] [] a b]
  unfold cutoff packet
  simp only [pairFst_pair, pairSnd_pair]
  cases right <;> omega

private theorem sign_at_root (right : Bool) (z ctx : List Bool)
    (hroot : CoefficientMarkedRecordFieldQuery.rightRoot right z = ctx) {a b : ℝ}
    (ha0 : (2 : ℝ)^CoefficientMarkedRecordFieldSign.cutoff hn ht ha right z ≤ a)
    (x : C(Ioo a b, Fin (CoefficientMarkedRecordFullCutPhysical.rawData hn ht ha ctx).count → ℝ))
    (hx : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
      (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val (x u))
    (k : ℕ) (u v : Ioo a b) :
    SignType.sign ((CoefficientMarkedRecordFieldQuery.physical hn ht ha right z k).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation u.val) (CoefficientFinitePhysicalQuery.natural (x u))) =
    SignType.sign ((CoefficientMarkedRecordFieldQuery.physical hn ht ha right z k).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation v.val) (CoefficientFinitePhysicalQuery.natural (x v))) := by
  subst ctx
  have H := CoefficientMarkedRecordFieldSign.sign_on_root_curve hn ht ha right z ha0 x hx k u v
  unfold CoefficientMarkedRecordFieldVariables.polynomial at H
  rw [CoefficientFinitePhysicalQuery.evaluation, CoefficientFinitePhysicalQuery.evaluation] at H
  exact H

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic

/-- Both independent root curves preserve every derivative sign comparison;
the cutoff is uniform over all labels, including malformed/out-of-range ones. -/
theorem agrees_on_curves (cL cR : List Bool) {a b : ℝ}
    (ha0 : (2 : ℝ)^cutoff hn ht ha (pair cL cR) ≤ a)
    (xL : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha cL))
    (xR : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha cR))
    (hxL : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (pairFst cL)
      (IntegralMixedCausalRecordPlanBits.count (pairFst cL)) le_rfl u.val (xL u))
    (hxR : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (pairFst cR)
      (IntegralMixedCausalRecordPlanBits.count (pairFst cR)) le_rfl u.val (xR u))
    (l r : ℕ) (u v : Ioo a b) :
    CoefficientMarkedRecordFieldListIncidence.Agrees hn ht ha cL cR l r u.val (xL u) (xR u) ↔
      CoefficientMarkedRecordFieldListIncidence.Agrees hn ht ha cL cR l r v.val (xL v) (xR v) := by
  let z := IntegralMixedPhysicalFieldEquality.packet cL [] cR [] l r
  have hrootL : CoefficientMarkedRecordFieldQuery.rightRoot false z = pairFst cL := by
    simp only [z, CoefficientMarkedRecordFieldQuery.rightRoot, IntegralMixedPhysicalFieldEquality.context,
      IntegralMixedPhysicalFieldEquality.sample, IntegralMixedPhysicalFieldEquality.packet, Bool.false_eq_true, ite_false, pairFst_pair]
  have hrootR : CoefficientMarkedRecordFieldQuery.rightRoot true z = pairFst cR := by
    simp only [z, CoefficientMarkedRecordFieldQuery.rightRoot, IntegralMixedPhysicalFieldEquality.context,
      IntegralMixedPhysicalFieldEquality.sample, IntegralMixedPhysicalFieldEquality.packet, ite_true, pairFst_pair, pairSnd_pair]
  have hstart (right : Bool) : (2 : ℝ)^CoefficientMarkedRecordFieldSign.cutoff hn ht ha right z ≤ a :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (member_cutoff_le hn ht ha right cL cR l r)).trans ha0
  unfold CoefficientMarkedRecordFieldListIncidence.Agrees
  apply forall_congr'
  intro k
  apply forall_congr'
  intro _
  have HL := sign_at_root hn ht ha false z (pairFst cL) hrootL (hstart false) xL hxL k u v
  have HR := sign_at_root hn ht ha true z (pairFst cR) hrootR (hstart true) xR hxR k u v
  exact ⟨fun H => (HL.symm.trans H).trans HR, fun H => (HL.trans H).trans HR.symm⟩

/-- One shared pair of curves transports the entire original streamed table. -/
theorem holds_on_curves (cL cR table : List Bool) {a b : ℝ}
    (ha0 : (2 : ℝ)^cutoff hn ht ha (pair cL cR) ≤ a)
    (xL : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha cL))
    (xR : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha cR))
    (hxL : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (pairFst cL)
      (IntegralMixedCausalRecordPlanBits.count (pairFst cL)) le_rfl u.val (xL u))
    (hxR : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (pairFst cR)
      (IntegralMixedCausalRecordPlanBits.count (pairFst cR)) le_rfl u.val (xR u))
    (u v : Ioo a b) :
    CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha cL cR table u.val (xL u) (xR u) ↔
      CoefficientMarkedRecordFieldListIncidence.Holds hn ht ha cL cR table v.val (xL v) (xR v) := by
  unfold CoefficientMarkedRecordFieldListIncidence.Holds
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  exact and_congr Iff.rfl (agrees_on_curves hn ht ha cL cR ha0 xL xR hxL hxR _ _ u v)

attribute [local irreducible] cutoff CoefficientMarkedRecordFieldSign.cutoff
  CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff

theorem effective_cutoffs (cL cR : List Bool) :
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (pairFst cL) ≤ cutoff hn ht ha (pair cL cR) ∧
    CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (pairFst cR) ≤ cutoff hn ht ha (pair cL cR) := by
  have H := (CoefficientMarkedRecordFieldSign.query_cutoff_le hn ht ha true
    (IntegralMixedPhysicalFieldEquality.packet cL [] cR [] 0 0)).trans
      (member_cutoff_le hn ht ha true cL cR 0 0)
  simp only [CoefficientMarkedRecordFieldQuery.cutoff, CoefficientMarkedRecordFieldSource.root,
    CoefficientMarkedRecordFieldQuery.rightRoot, IntegralMixedPhysicalFieldEquality.context,
    IntegralMixedPhysicalFieldEquality.sample, IntegralMixedPhysicalFieldEquality.packet,
    Bool.false_eq_true, ite_false, ite_true, pairFst_pair, pairSnd_pair] at H
  exact ⟨(le_max_left _ _).trans H, (le_max_right _ _).trans H⟩

variable {R S : List Bool → ℕ} (hR : BinaryFn R) (hS : BinaryFn S)

/-- The literal streamed native language has the same truth at two radii on
the same two root curves. Each of the four words belongs to its OWN sampler;
only the two requested radii at each endpoint are required to agree. -/
theorem language_on_curves (cL cR table : List Bool)
    (hReq : R (pairFst cL) = R (pairFst cR)) (hSeq : S (pairFst cL) = S (pairFst cR))
    (hRc : cutoff hn ht ha (pair cL cR) ≤ R (pairFst cL))
    (hSc : cutoff hn ht ha (pair cL cR) ≤ S (pairFst cL))
    {a b : ℝ} (ha0 : (2 : ℝ)^cutoff hn ht ha (pair cL cR) ≤ a)
    (xL : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha cL))
    (xR : C(Ioo a b, CoefficientMarkedRecordFieldListIncidence.Point hn ht ha cR))
    (hxL : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (pairFst cL)
      (IntegralMixedCausalRecordPlanBits.count (pairFst cL)) le_rfl u.val (xL u))
    (hxR : ∀ u : Ioo a b, CoefficientMarkedRecordRootBranches.RowsAt hn ht ha (pairFst cR)
      (IntegralMixedCausalRecordPlanBits.count (pairFst cR)) le_rfl u.val (xR u))
    (u v : Ioo a b) (hu : u.val = (2 : ℝ)^R (pairFst cL)) (hv : v.val = (2 : ℝ)^S (pairFst cL))
    (wRL wRR wSL wSR : List Bool)
    (hwRL : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) cL wRL)
    (hwRR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) cR wRR)
    (hwSL : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) cL wSL)
    (hwSR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) cR wSR)
    (heRL : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) cL wRL hwRL).val (xL u))
    (heRR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false) cR wRR hwRR).val (xR u))
    (heSL : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) cL wSL hwSL).val (xL v))
    (heSR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hS false) cR wSR hwSR).val (xR v)) :
    IntegralMixedPhysicalFieldEqualityList.packet cL wRL cR wRR table ∈ IntegralMixedPhysicalFieldEqualityList.language hn ht ha hR ↔
      IntegralMixedPhysicalFieldEqualityList.packet cL wSL cR wSR table ∈ IntegralMixedPhysicalFieldEqualityList.language hn ht ha hS := by
  have hEff := effective_cutoffs hn ht ha cL cR
  have hRL := hEff.1.trans hRc
  have hRR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (pairFst cR) ≤ R (pairFst cR) := by
    rw [← hReq]
    exact hEff.2.trans hRc
  have hSL := hEff.1.trans hSc
  have hSR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (pairFst cR) ≤ S (pairFst cR) := by
    rw [← hSeq]
    exact hEff.2.trans hSc
  have hLeft := CoefficientMarkedRecordFieldListIncidence.language_iff hn ht ha hR cL wRL cR wRR table
    hReq hRL hRR hwRL hwRR (xL u) (xR u) heRL heRR
  have hRight := CoefficientMarkedRecordFieldListIncidence.language_iff hn ht ha hS cL wSL cR wSR table
    hSeq hSL hSR hwSL hwSR (xL v) (xR v) heSL heSR
  rw [← hu] at hLeft
  rw [← hv] at hRight
  exact hLeft.trans ((holds_on_curves hn ht ha cL cR table ha0 xL xR hxL hxR u v).trans hRight.symm)

end LeanCanny.Encoding.CoefficientMarkedRecordFieldListTransport
