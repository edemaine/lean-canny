/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildParentSign
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers

/-! # Native selection of regular children over the actual parent

Input is `pair childSource (pair parentDescriptor childDescriptor)`.
Both descriptors are validated. A binary-counted scan compares every parent
derivative sign, identifying the retained parent parameter exactly. Candidates
over other parent roots are rejected without assuming all joint roots regular.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildParentSelection
open LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter Brackets
open BoundedFullSampleChildSource (Inputs)
open BoundedFullSampleChildParentSign
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildQueries.roots
  BoundedFullSampleChildCoordinates.parameter BoundedFullSampleChildCoordinates.parameterDegree
  BoundedCriticalRationalCoordinates.parameter BoundedCriticalRationalCoordinates.parameterDegree
  BoundedCriticalSampleThom.polynomial
  BoundedCriticalSampleHashChoice.descriptor BoundedFullSampleChildHashChoice.descriptor
  BoundedCriticalSampleLabels.parameter BoundedFullSampleChildParameters.decode

def source (q : List Bool) : List Bool := pairFst q
def parentSource (q : List Bool) : List Bool := pairFst (source q)
def parentWord (q : List Bool) : List Bool := pairFst (pairSnd q)
def childWord (q : List Bool) : List Bool := pairSnd (pairSnd q)
def parentLabel (q : List Bool) : List Bool := pair (parentSource q) (parentWord q)
def childLabel (q : List Bool) : List Bool := pair (source q) (childWord q)

theorem source_FP : source ∈ FP := pairFst_mem_FP
theorem parentSource_FP : parentSource ∈ FP := mem_FP_comp source_FP pairFst_mem_FP
theorem parentWord_FP : parentWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem childWord_FP : childWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem parentLabel_FP : parentLabel ∈ FP := mem_FP_pair parentSource_FP parentWord_FP
theorem childLabel_FP : childLabel ∈ FP := mem_FP_pair source_FP childWord_FP

def childQuery (z : List Bool) : List Bool := pair (childLabel (pairFst z)) (pairSnd z)
def parentQuery (z : List Bool) : List Bool := pair (parentLabel (pairFst z)) (pairSnd z)
theorem childQuery_FP : childQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP childLabel_FP) pairSnd_mem_FP
theorem parentQuery_FP : parentQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP parentLabel_FP) pairSnd_mem_FP

noncomputable def count (F : Inputs) (q : List Bool) : ℕ :=
  BoundedCriticalRationalCoordinates.parameterDegree F.block.parent (parentSource q) + 1

theorem count_binary {F : Inputs} (h : F.PolyTime) : BinaryFn (count F) := by
  have H : BinaryFn (fun q => BoundedCriticalRationalCoordinates.parameterDegree F.block.parent (parentSource q)) :=
    (BoundedCriticalRationalCoordinates.parameterDegree_binary h.block.parent).comp parentSource_FP
  exact H.add (BinaryFn.const 1)

noncomputable def agreement (F : Inputs) (q : List Bool) : Prop :=
  ∀ k < count F q, childValue F (childQuery (pair q (BinaryNatCode.encode k))) =
    parentValue F.block.parent (parentQuery (pair q (BinaryNatCode.encode k)))

theorem agreement_evaluator {F : Inputs} (h : F.PolyTime) :
    SpaceFunction (fun q => [decide (agreement F q)]) := by
  have C := (child_evaluator h).precompose childQuery childQuery_FP
  have P := (parent_evaluator h).precompose parentQuery parentQuery_FP
  have E := (C.pairOutputs P).postcompose _
    (stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have E' : SpaceFunction (fun z => [decide
      (childValue F (childQuery z) = parentValue F.block.parent (parentQuery z))]) :=
    E.congr (funext fun z => by simp only [Function.comp_apply, pairFst_pair, pairSnd_pair])
  have H := SpaceFunction.forall_binary E' (count_binary h)
  exact H.congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [agreement, List.cons.injEq, and_true, decide_eq_true_eq])

noncomputable def language (F : Inputs) : Language := {q |
  parentLabel q ∈ BoundedCriticalSampleDescriptors.language F.block.parent ∧
    childLabel q ∈ BoundedFullSampleChildDescriptors.language F ∧ agreement F q}

theorem decider {F : Inputs} (h : F.PolyTime) : SpaceDecider (language F) := by
  have P := ((BoundedCriticalSampleDescriptors.decider h.block.parent h.parentArity).precompose parentLabel parentLabel_FP).flagEvaluator
  have C := ((BoundedFullSampleChildDescriptors.decider h).precompose childLabel childLabel_FP).flagEvaluator
  have E := P.andFlags (C.andFlags (agreement_evaluator h))
  apply E.decider (fun z => decide (z = [true])) (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true,
    decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.PolyTime) : language F ∈ PSPACE := (decider h).mem_PSPACE

theorem agreement_at (F : Inputs) (q : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (parentSource q))
    (x : BoundedFullSampleChildRecordSpan.Root F (source q))
    (hp : BoundedCriticalSampleHashChoice.descriptor F.block.parent (parentSource q) p = parentWord q)
    (hx : BoundedFullSampleChildHashChoice.descriptor F (source q) x = childWord q) :
    agreement F q ↔ BoundedFullSampleChildParameters.decode F (source q) x.val
      (BoundedFullSampleChildParentThom.first F (source q)) =
        (BoundedCriticalSampleLabels.parameter F.block.parent (parentSource q) p).val := by
  unfold agreement
  simp only [childQuery, parentQuery, pairFst_pair, pairSnd_pair, childLabel, parentLabel]
  simp_rw [← hp, ← hx, child_packet, parent_packet,
    BoundedFullSampleChildTestSign.encode_eq_iff]
  have H := BoundedFullSampleChildParentThom.identifies_parent F (source q) x.val x.property p
  constructor
  · intro hs
    apply H.mpr
    intro k hk
    exact hs k (by dsimp only [count, parentSource]; omega)
  · intro he k hk
    exact H.mp he k (by dsimp only [count, parentSource] at hk; omega)

theorem language_iff (F : Inputs) (q : List Bool) : q ∈ language F ↔
    ∃ (p : BoundedFullCriticalSamples.Samples F.block.parent (parentSource q))
      (x : BoundedFullSampleChildRecordSpan.Root F (source q)),
      BoundedCriticalSampleHashChoice.descriptor F.block.parent (parentSource q) p = parentWord q ∧
      BoundedFullSampleChildHashChoice.descriptor F (source q) x = childWord q ∧
      BoundedFullSampleChildParameters.decode F (source q) x.val
        (BoundedFullSampleChildParentThom.first F (source q)) =
          (BoundedCriticalSampleLabels.parameter F.block.parent (parentSource q) p).val := by
  simp only [language, Set.mem_ofPred_eq, BoundedCriticalSampleDescriptors.language,
    BoundedFullSampleChildDescriptors.language, parentLabel, childLabel]
  rw [pairFst_pair, pairFst_pair]
  simp only [pairSnd_pair]
  constructor
  · rintro ⟨⟨p, hp⟩, ⟨x, hx⟩, ha⟩
    exact ⟨p, x, hp, hx, (agreement_at F q p x hp hx).mp ha⟩
  · rintro ⟨p, x, hp, hx, he⟩
    exact ⟨⟨p, hp⟩, ⟨x, hx⟩, (agreement_at F q p x hp hx).mpr he⟩

theorem invalid_parent (F : Inputs) (q : List Bool)
    (h : parentLabel q ∉ BoundedCriticalSampleDescriptors.language F.block.parent) : q ∉ language F := fun hq => h hq.1

theorem invalid_child (F : Inputs) (q : List Bool)
    (h : childLabel q ∉ BoundedFullSampleChildDescriptors.language F) : q ∉ language F := fun hq => h hq.2.1

theorem at_descriptors (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildRecordSpan.Root F u) :
    pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p)
      (BoundedFullSampleChildHashChoice.descriptor F u x)) ∈ language F ↔
      BoundedFullSampleChildParameters.decode F u x.val (BoundedFullSampleChildParentThom.first F u) =
        (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val := by
  have hs : source (pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p)
      (BoundedFullSampleChildHashChoice.descriptor F u x))) = u := pairFst_pair _ _
  have hp : parentSource (pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p)
      (BoundedFullSampleChildHashChoice.descriptor F u x))) = pairFst u := congrArg pairFst hs
  rw [language_iff, hp, hs]
  simp only [parentWord, childWord, pairFst_pair, pairSnd_pair]
  constructor
  · rintro ⟨p', x', hp, hx, he⟩
    have hpp := BoundedCriticalSampleHashChoice.descriptor_injective F.block.parent (pairFst u) hp
    have hxx := BoundedFullSampleChildHashChoice.descriptor_injective F u hx
    subst p'
    subst x'
    exact he
  · intro he
    exact ⟨p, x, rfl, rfl, he⟩

theorem candidate_packet (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (z : BoundedFullSampleChildParameters.Candidates F u) :
    pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p)
      (BoundedFullSampleChildDescriptors.candidateWord F u z)) ∈ language F ↔
      z.val.val (BoundedFullSampleChildParentThom.first F u) =
        (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val := by
  let x := (BoundedFullSampleChildHashEnumeration.rootCandidateEquiv F u).symm z
  have hx : BoundedFullSampleChildParameters.decode F u x.val = z.val.val :=
    congrArg (fun y : BoundedFullSampleChildParameters.Candidates F u => y.val.val)
      ((BoundedFullSampleChildHashEnumeration.rootCandidateEquiv F u).apply_symm_apply z)
  change pair u (pair _ (BoundedFullSampleChildHashChoice.descriptor F u x)) ∈ language F ↔ _
  rw [at_descriptors, hx]

end LeanCanny.Encoding.BoundedFullSampleChildParentSelection
