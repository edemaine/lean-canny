/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldIncidence
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldContext
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityList
/-! # Streamed default Field comparisons on ONE shared pair of tuples -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFieldListIncidence
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem valid_at (I : SquareSampleInput.Inputs) (c w c' w' : List Bool)
    (hc : c' = c) (hw : w' = w) (hv : SquareSampleCompleteVertices.Valid I c w) :
    SquareSampleCompleteVertices.Valid I c' w' := by
  cases hc
  cases hw
  exact hv

private theorem candidate_at (I : SquareSampleInput.Inputs) (c w c' w' : List Bool)
    (hc : c' = c) (hw : w' = w) (hv : SquareSampleCompleteVertices.Valid I c w)
    (hv' : SquareSampleCompleteVertices.Valid I c' w') :
    HEq (SquareSampleCompleteVertices.candidate I c' w' hv').val (SquareSampleCompleteVertices.candidate I c w hv).val := by
  cases hc
  cases hw
  rfl

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalMarkedPlan.bank CoefficientMarkedRecordRows.symbolic

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable abbrev Point (c : List Bool) :=
  Fin (CoefficientMarkedRecordRows.symbolic hn ht ha (pairFst c)
    (IntegralMixedCausalRecordPlanBits.count (pairFst c)) le_rfl).count → ℝ

private theorem point_type (right : Bool) (z c : List Bool) (hc : IntegralMixedPhysicalFieldEquality.context right z = c) :
    CoefficientMarkedRecordFieldIncidence.Point hn ht ha right z = Point hn ht ha c := by
  exact congrArg (Point hn ht ha) hc

private noncomputable def pointAt (right : Bool) (z c : List Bool)
    (hc : IntegralMixedPhysicalFieldEquality.context right z = c) (x : Point hn ht ha c) :
    CoefficientMarkedRecordFieldIncidence.Point hn ht ha right z :=
  Eq.mp (point_type hn ht ha right z c hc).symm x

private theorem pointAt_heq (right : Bool) (z c : List Bool)
    (hc : IntegralMixedPhysicalFieldEquality.context right z = c) (x : Point hn ht ha c) :
    HEq (pointAt hn ht ha right z c hc x) x := by
  cases hc
  rfl

private theorem pointAt_natural (right : Bool) (z c : List Bool)
    (hc : IntegralMixedPhysicalFieldEquality.context right z = c) (x : Point hn ht ha c) :
    CoefficientFinitePhysicalQuery.natural (pointAt hn ht ha right z c hc x) = CoefficientFinitePhysicalQuery.natural x := by
  cases hc
  rfl

/-- Both words are erased from the constructed comparison coefficients. The
same two raw tuples supply EVERY comparison in the streamed table. -/
noncomputable def Agrees (cL cR : List Bool) (a b : ℕ) (β : ℝ)
    (left : Point hn ht ha cL) (right : Point hn ht ha cR) : Prop :=
  ∀ k < IntegralMixedPhysicalFieldEquality.catalogDegree hn ht ha (pairFst cL) + 1,
    SignType.sign ((CoefficientMarkedRecordFieldQuery.physical hn ht ha false
      (IntegralMixedPhysicalFieldEquality.packet cL [] cR [] a b) k).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation β) (CoefficientFinitePhysicalQuery.natural left)) =
    SignType.sign ((CoefficientMarkedRecordFieldQuery.physical hn ht ha true
      (IntegralMixedPhysicalFieldEquality.packet cL [] cR [] a b) k).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation β) (CoefficientFinitePhysicalQuery.natural right))

private theorem agrees_at (cL wL cR wR : List Bool) (a b : ℕ) (β : ℝ)
    (left : Point hn ht ha cL) (right : Point hn ht ha cR)
    (hcL : IntegralMixedPhysicalFieldEquality.context false (IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b) = cL)
    (hcR : IntegralMixedPhysicalFieldEquality.context true (IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b) = cR) :
    CoefficientMarkedRecordFieldIncidence.Agrees hn ht ha (IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b) β
      (pointAt hn ht ha false _ cL hcL left) (pointAt hn ht ha true _ cR hcR right) ↔
      Agrees hn ht ha cL cR a b β left right := by
  unfold CoefficientMarkedRecordFieldIncidence.Agrees Agrees CoefficientMarkedRecordFieldSource.root
  rw [hcL, pointAt_natural, pointAt_natural]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro _
  rw [CoefficientMarkedRecordFieldContext.polynomial_packet_words hn ht ha false cL cR wL wR [] [] a b k,
    CoefficientMarkedRecordFieldContext.polynomial_packet_words hn ht ha true cL cR wL wR [] [] a b k]

variable {R : List Bool → ℕ} (hRad : BinaryFn R)

attribute [local irreducible] SquareSampleCompleteVertices.Valid

/-- Literal query constructor, actual OWN words and their entire raw readbacks
yield the computed polynomial comparison; no native Field guard is assumed. -/
theorem packet_iff (cL wL cR wR : List Bool) (a b : ℕ)
    (hEq : R (pairFst cL) = R (pairFst cR))
    (hL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (pairFst cL) ≤ R (pairFst cL))
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (pairFst cR) ≤ R (pairFst cR))
    (hwL : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false) cL wL)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false) cR wR)
    (left : Point hn ht ha cL) (right : Point hn ht ha cR)
    (heL : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false) cL wL hwL).val left)
    (heR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false) cR wR hwR).val right) :
    IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b ∈ IntegralMixedPhysicalFieldEquality.language hn ht ha hRad ↔
      (a < IntegralMixedPhysicalFieldEquality.catalogCount n cL ∧ b < IntegralMixedPhysicalFieldEquality.catalogCount n cR) ∧
        Agrees hn ht ha cL cR a b ((2 : ℝ)^R (pairFst cL)) left right := by
  let z := IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b
  rcases IntegralMixedPhysicalFieldEquality.packet_fields cL wL cR wR a b with ⟨hcL, hwordL, hcR, hwordR, hlabelL, hlabelR⟩
  let hl := valid_at (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false) cL wL _ _ hcL hwordL hwL
  let hr := valid_at (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false) cR wR _ _ hcR hwordR hwR
  have hxL := (candidate_at _ cL wL _ _ hcL hwordL hwL hl).trans
    (heL.trans (pointAt_heq hn ht ha false z cL hcL left).symm)
  have hxR := (candidate_at _ cR wR _ _ hcR hwordR hwR hr).trans
    (heR.trans (pointAt_heq hn ht ha true z cR hcR right).symm)
  have hrootL : CoefficientMarkedRecordFieldSource.root z = pairFst cL := congrArg pairFst hcL
  have hrootR : CoefficientMarkedRecordFieldQuery.rightRoot true z = pairFst cR := congrArg pairFst hcR
  have hEq' : R (CoefficientMarkedRecordFieldSource.root z) = R (CoefficientMarkedRecordFieldQuery.rightRoot true z) := by
    rw [hrootL, hrootR]
    exact hEq
  have hL' : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (CoefficientMarkedRecordFieldSource.root z) ≤
      R (CoefficientMarkedRecordFieldSource.root z) := by rw [hrootL]; exact hL
  have hR' : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (CoefficientMarkedRecordFieldQuery.rightRoot true z) ≤
      R (CoefficientMarkedRecordFieldQuery.rightRoot true z) := by rw [hrootR]; exact hR
  have hh := CoefficientMarkedRecordFieldIncidence.language_iff hn ht ha hRad z hEq' hL' hR' hl hr
    (pointAt hn ht ha false z cL hcL left) (pointAt hn ht ha true z cR hcR right) hxL hxR
  have hz : IntegralMixedPhysicalFieldEquality.Wellformed z := CoefficientMarkedRecordFieldIncidence.packet_wellformed cL wL cR wR a b
  simp only [hz, true_and] at hh
  rw [hrootL] at hh
  have hlabels : CoefficientMarkedRecordFieldIncidence.Labels (n := n) z ↔
      a < IntegralMixedPhysicalFieldEquality.catalogCount n cL ∧ b < IntegralMixedPhysicalFieldEquality.catalogCount n cR := by
    unfold CoefficientMarkedRecordFieldIncidence.Labels
    rw [hcL, hcR, hlabelL, hlabelR]
  exact hh.trans (and_congr hlabels (agrees_at hn ht ha cL wL cR wR a b _ left right hcL hcR))

noncomputable def Holds (cL cR table : List Bool) (β : ℝ)
    (left : Point hn ht ha cL) (right : Point hn ht ha cR) : Prop :=
  ∀ i < WordListRecords.count table,
    let a := IntegralMixedPhysicalFieldEqualityList.label false (WordList.get table i)
    let b := IntegralMixedPhysicalFieldEqualityList.label true (WordList.get table i)
    (a < IntegralMixedPhysicalFieldEquality.catalogCount n cL ∧ b < IntegralMixedPhysicalFieldEquality.catalogCount n cR) ∧
      Agrees hn ht ha cL cR a b β left right

/-- The literal streamed list uses ONE shared tuple pair for every comparison.
The constructed polynomial family erases BOTH sampled words. -/
theorem language_iff (cL wL cR wR table : List Bool)
    (hEq : R (pairFst cL) = R (pairFst cR))
    (hL : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (pairFst cL) ≤ R (pairFst cL))
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha (pairFst cR) ≤ R (pairFst cR))
    (hwL : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false) cL wL)
    (hwR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false) cR wR)
    (left : Point hn ht ha cL) (right : Point hn ht ha cR)
    (heL : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false) cL wL hwL).val left)
    (heR : HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hRad false) cR wR hwR).val right) :
    IntegralMixedPhysicalFieldEqualityList.packet cL wL cR wR table ∈ IntegralMixedPhysicalFieldEqualityList.language hn ht ha hRad ↔
      Holds hn ht ha cL cR table ((2 : ℝ)^R (pairFst cL)) left right := by
  simp only [IntegralMixedPhysicalFieldEqualityList.language, Set.mem_ofPred_eq,
    IntegralMixedPhysicalFieldEquality.context, IntegralMixedPhysicalFieldEquality.word,
    IntegralMixedPhysicalFieldEquality.sample, IntegralMixedPhysicalFieldEqualityList.packet,
    Bool.false_eq_true, ite_false, ite_true, pairFst_pair, pairSnd_pair, hwL, hwR, true_and]
  unfold IntegralMixedPhysicalFieldEqualityList.holds IntegralMixedPhysicalFieldEqualityList.count
    IntegralMixedPhysicalFieldEqualityList.table Holds
  simp only [pairSnd_pair]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  rw [show pair (pair cL wL) (pair (pair cR wR) table) =
    IntegralMixedPhysicalFieldEqualityList.packet cL wL cR wR table from rfl,
    IntegralMixedPhysicalFieldEqualityList.query_packet]
  exact packet_iff hn ht ha hRad cL wL cR wR _ _ hEq hL hR hwL hwR left right heL heR

end LeanCanny.Encoding.CoefficientMarkedRecordFieldListIncidence
