/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyTermSemantics
/-! # Native replies test the original equation at the decoded candidate point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliaryRecipeRoot
open IntegralMixedAuxiliaryPreparedRoot (dimension term dimension_unary term_FP)
open scoped Classical

theorem term_vertex_valid {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : Valid hn ht ha q) :
    SquareSampleCompleteVertices.Valid (termInput hn ht ha) (source n t q) (vertex hn ht ha q) := by
  rw [termInput_eq]
  exact hq.2

private theorem extended_candidate_congr (F G : SquareSampleInput.Inputs) (h : F=G)
    (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid F c w) (hw : SquareSampleCompleteVertices.Valid G c w) :
    IntegralMixedFramedBankObservation.extend (SquareSampleCompleteVertices.candidate F c w hv).val=
      IntegralMixedFramedBankObservation.extend (SquareSampleCompleteVertices.candidate G c w hw).val := by
  cases h
  rfl

attribute [local irreducible] parameters scalarWidth scalarCeiling spatialDegree degreeCharge augmented
  planAt dataAt input source vertex bankData joint point
  IntegralMixedEmptyUnitPlan.plan IntegralMixedEmptyUnitPlan.data

theorem tested_point {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : Valid hn ht ha q) (i : Fin (n (pairFst q))) :
    IntegralMixedAuxiliaryEmptyPlan.termPoint (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))
      (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id)
      (IntegralMixedAuxiliaryPositivePrefix.key_positive (dimension n) (term t) id)
      (source n t q) (vertex hn ht ha q) (term_vertex_valid hn ht ha q hq) i.val=point hn ht ha q hq i := by
  have HJ := extended_candidate_congr (termInput hn ht ha) (input hn ht ha) (termInput_eq hn ht ha)
    (source n t q) (vertex hn ht ha q) (term_vertex_valid hn ht ha q hq) hq.2
  let P := parameters (dimension n) (term t)
  let D := IntegralMixedAuxiliaryEmptyPlan.plan (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))
  let H : IntegralMixedFramedHistoryFamilyBits.Data P D :=
    IntegralMixedAuxiliaryEmptyPlan.data (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))
  let key := IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id (source n t q)
  have HC : (IntegralMixedFramedBankSnapshotBits.atKey P D H key).count=n (pairFst q)+1 := by
    change (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key=_
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth,IntegralMixedAuxiliaryPositivePrefix.key_prefix]
    exact congrArg (fun r=>n r+1) (source_input n t q)
  have HI : i.val<(IntegralMixedFramedBankSnapshotBits.atKey P D H key).count := by rw [HC]; omega
  unfold IntegralMixedAuxiliaryEmptyPlan.termPoint
  change IntegralFramedBankTermTest.observedPoint P D H key
    (IntegralMixedFramedBankObservation.extend
      (SquareSampleCompleteVertices.candidate (termInput hn ht ha) (source n t q) (vertex hn ht ha q) _).val) i.val=_
  rw [HJ]
  unfold IntegralFramedBankTermTest.observedPoint
  rw [ite_eq_left HI,HC]
  simp only [Nat.add_sub_cancel]
  unfold point bankData joint planAt dataAt
  rfl

theorem original_term_syntax {n : List Bool→ℕ} {t : List Bool→Term} (q : List Bool) :
    (IntegralMixedFramedBankTermBits.source (fun root=>(t (pairFst root)).toData.toBits)).syntax
      (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id (source n t q))=t (pairFst q) := by
  unfold IntegralMixedFramedBankTermBits.source IntegralMixedFramedBankTermBits.wordAt
    RationalSubstitutionBits.Source.syntax RationalSubstitutionBits.Source.ofTerm
    IntegralMixedAuxiliaryPositivePrefix.key IntegralMixedFramedHistoryFamilyBits.keyAt
  simp only [id_eq,pairFst_pair,TermView.term_toBits,source_input]

theorem term_sign {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (q : List Bool) (hq : Valid hn ht ha q) :
    termValue hn ht ha (termQuery hn ht ha q)=InfinitesimalSign.encode
      (SignType.sign ((t (pairFst q)).eval (Formula.extend (point hn ht ha q hq)))) := by
  have HE := IntegralMixedAuxiliaryEmptyPlan.term_packet (dimension_unary hn) (term_FP ht) (fun q=>ha (pairFst q))
    (IntegralMixedAuxiliaryPositivePrefix.key (dimension n) id)
    (IntegralMixedAuxiliaryPositivePrefix.key_positive (dimension n) (term t) id)
    (fun root=>(t (pairFst root)).toData.toBits) (source n t q) (vertex hn ht ha q) []
    (term_vertex_valid hn ht ha q hq)
  rw [original_term_syntax q] at HE
  refine HE.trans (congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v)) ?_)
  apply Term.eval_congr
  intro i hi
  have HI : i<n (pairFst q) := hi.trans_le (ha (pairFst q))
  rw [tested_point hn ht ha q hq ⟨i,HI⟩]
  unfold Formula.extend
  rw [dite_eq_left HI]

end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
