/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildTerm
public import LeanCanny.Encoding.BoundedCriticalSampleBlockEvaluation
public import LeanCanny.Encoding.BoundedCriticalSampleChildActualSamples

/-! # Native original-term signs at actual-parent child samples

Input is `pair childSource (pair parentDescriptor childDescriptor)`. Both
descriptors and their parent relation are checked. The term is evaluated at
the original sample with exactly its free block replaced by the child point.
No coordinates, polynomial signs, or coefficient table are supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildTermSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR Brackets
open BoundedCriticalSampleChildSource (Inputs)
open BoundedCriticalSampleChildActualSamples
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildQueries.roots
  BoundedCriticalSampleChildCoordinates.parameter BoundedCriticalSampleChildParameters.decode
  BoundedCriticalSampleLabels.parameter BoundedCriticalSampleHashChoice.descriptor
  BoundedCriticalSampleChildHashChoice.descriptor

noncomputable def value (F : Inputs) (read : List Bool → List Bool) : List Bool → List Bool :=
  BoundedCriticalSampleChildTestSign.value F (BoundedCriticalSampleChildTerm.test F read) ∘
    BoundedCriticalSampleChildParentSelection.childLabel

theorem evaluator {F : Inputs} (h : F.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    SpaceFunction (value F read) :=
  (BoundedCriticalSampleChildTestSign.evaluator h (BoundedCriticalSampleChildTerm.testAccess h read hr)).precompose
    BoundedCriticalSampleChildParentSelection.childLabel BoundedCriticalSampleChildParentSelection.childLabel_FP

noncomputable def assignment (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) : ℕ → ℝ :=
  BoundedCriticalSampleBlockSource.assignment p.val (F.offset u) (F.dim u) (point F u p x)

theorem assignment_block (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p)
    (i : Fin (F.dim u)) : assignment F u p x (F.offset u + i.val) = point F u p x i := by
  have hi : BoundedCriticalSampleBlockSource.InBlock (F.offset u) (F.dim u) (F.offset u + i.val) := by
    constructor <;> omega
  simp only [assignment, BoundedCriticalSampleBlockSource.assignment, hi, dite_true, Nat.add_sub_cancel_left]

theorem assignment_outside (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) (i : ℕ)
    (hi : ¬BoundedCriticalSampleBlockSource.InBlock (F.offset u) (F.dim u) i) :
    assignment F u p x i = Formula.extend p.val i := by
  simp only [assignment, BoundedCriticalSampleBlockSource.assignment, hi, dite_false]

theorem assignment_finite (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p)
    (hk : F.offset u + F.dim u ≤ F.parent.dim (pairFst u) + 4) :
    assignment F u p x = Formula.extend
      (BoundedCriticalSampleBlockSource.finiteAssignment p.val (F.offset u) (F.dim u) (point F u p x)) :=
  BoundedCriticalSampleBlockSource.assignment_finite p.val _ _ _ hk

theorem environment_eq_cons (n : ℕ) (theta : ℝ) (y : Fin n → ℝ) :
    BoundedCriticalSampleBlockSource.environment n theta y = Fin.cons theta y := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact BoundedCriticalSampleBlockSource.environment_zero n theta y
  · simp only [BoundedCriticalSampleBlockSource.environment, Fin.val_succ, Nat.add_sub_cancel,
      Fin.cons_succ, Nat.succ_ne_zero, dite_false]

theorem value_sample (F : Inputs) (read : List Bool → List Bool) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) :
    value F read (pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p)
      (word F u p x))) =
        InfinitesimalSign.encode (SignType.sign ((TermView.term (read u)).eval
          (assignment F u p x))) := by
  let theta := (BoundedCriticalSampleChildHashEnumeration.rootCandidateEquiv F u).symm x.val
  have he : BoundedCriticalSampleChildParameters.decode F u theta.val = x.val.val.val :=
    congrArg (fun z : BoundedCriticalSampleChildParameters.Candidates F u => z.val.val)
      ((BoundedCriticalSampleChildHashEnumeration.rootCandidateEquiv F u).apply_symm_apply x.val)
  have ht := ((BoundedCriticalSampleChildQueries.mem_roots F u theta.val).mp theta.property).1
  have H := BoundedCriticalSampleChildTerm.sign_decode F read u theta.val ht
  rw [he, ← point_cons F u p x, ← environment_eq_cons] at H
  have HS := BoundedCriticalSampleBlockEvaluation.sign F.parent read F.offset F.dim u p (point F u p x)
  change SignType.sign _ = SignType.sign ((TermView.term (read u)).eval (assignment F u p x)) at HS
  have hv := BoundedCriticalSampleChildTestSign.value_descriptor F (BoundedCriticalSampleChildTerm.test F read) u theta
  change value F read (pair u (pair _ (word F u p x))) = _
  simp only [value, Function.comp_apply, BoundedCriticalSampleChildParentSelection.childLabel,
    BoundedCriticalSampleChildParentSelection.source, BoundedCriticalSampleChildParentSelection.childWord,
    pairFst_pair, pairSnd_pair]
  change BoundedCriticalSampleChildTestSign.value F (BoundedCriticalSampleChildTerm.test F read)
    (pair u (BoundedCriticalSampleChildHashChoice.descriptor F u theta)) = _
  rw [hv]
  apply congrArg InfinitesimalSign.encode
  simpa only [BoundedCriticalSampleChildTestMoments.sign, BoundedCriticalSampleChildTerm.test,
    Polynomial.eval_map] using H.trans HS

noncomputable def language (F : Inputs) (read : List Bool → List Bool) (s : SignType) : Language :=
  {q | q ∈ BoundedCriticalSampleChildParentSelection.language F ∧ value F read q = InfinitesimalSign.encode s}

theorem decider {F : Inputs} (h : F.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (s : SignType) : SpaceDecider (language F read s) := by
  have E := (BoundedCriticalSampleChildParentSelection.decider h).flagEvaluator.pairOutputs (evaluator h read hr)
  apply E.decider (BoundedCriticalSampleChildTestSign.accept s) (BoundedCriticalSampleChildTestSign.accept_FP s)
  intro q
  simp only [language, Set.mem_ofPred_eq, BoundedCriticalSampleChildTestSign.accept, pairFst_pair,
    pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (s : SignType) : language F read s ∈ PSPACE := (decider h read hr s).mem_PSPACE

theorem language_sample (F : Inputs) (read : List Bool → List Bool) (s : SignType) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) :
    pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p) (word F u p x)) ∈
      language F read s ↔ SignType.sign ((TermView.term (read u)).eval (assignment F u p x)) = s := by
  change _ ∧ _ ↔ _
  rw [and_iff_right (word_valid F u p x), value_sample,
    BoundedCriticalSampleChildTestSign.encode_eq_iff]

theorem finite_value_sample (F : Inputs) (read : List Bool → List Bool) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p)
    (hk : F.offset u + F.dim u ≤ F.parent.dim (pairFst u) + 4) :
    value F read (pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p)
      (word F u p x))) = InfinitesimalSign.encode (SignType.sign
        ((TermView.term (read u)).eval (Formula.extend
          (BoundedCriticalSampleBlockSource.finiteAssignment p.val (F.offset u)
            (F.dim u) (point F u p x))))) := by
  rw [value_sample, assignment_finite F u p x hk]

theorem constant_value (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) (z : ℤ) :
    value F (fun _ => (Term.const z).toData.toBits)
      (pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p)
        (word F u p x))) = InfinitesimalSign.encode (SignType.sign (z : ℝ)) := by
  rw [value_sample, TermView.term_toBits]
  rfl

theorem source_value (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) :
    value F F.term (pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p)
      (word F u p x))) = [] := by
  have hz := point_zero F u p x (F.pivot u)
  change (ProjectionCriticalFamily.spatialEquation
    (ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ)
      (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val
      (BoundedCriticalSampleBlockTerm.polynomial F.parent F.term F.offset F.dim u))
        (F.pivot u) _ (F.pivot u)).eval (point F u p x) = 0 at hz
  simp only [ProjectionCriticalFamily.spatialEquation, ite_true] at hz
  rw [ParameterSpatialSpecialization.eval_specialize, ← environment_eq_cons] at hz
  have HS := BoundedCriticalSampleBlockEvaluation.sign F.parent F.term F.offset F.dim u p (point F u p x)
  rw [hz, sign_zero] at HS
  rw [value_sample, assignment, ← HS]
  rfl

theorem invalid (F : Inputs) (read : List Bool → List Bool) (s : SignType) (q : List Bool)
    (hq : q ∉ BoundedCriticalSampleChildParentSelection.language F) : q ∉ language F read s := fun h => hq h.1

end LeanCanny.Encoding.BoundedCriticalSampleChildTermSign
