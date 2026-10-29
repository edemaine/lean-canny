/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.NamedRationalParents
public import LeanCanny.Encoding.RationalParentChildDerivativeSigns
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers

/-! # Native child selection with ancestor validity

The descriptor is `pair childWord parentWord`. Keeping the parent in the right
tail adds the newest word's length without repeatedly doubling the ancestry.
Both names are validated, the pair is canonical, and a binary scan compares
every parent derivative sign. The parent validity and sign routines are
charged through the named-parent access certificate.
-/

@[expose] public section
namespace LeanCanny.Encoding.NamedParentChildSelection
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd RationalParentChildQueries.roots RationalParentChildCoordinates.parameter
  RationalParentChildHashChoice.descriptor RationalParentChildParameters.decode

structure Inputs where
  parent : NamedRationalParents.Source
  source : BoundedFullWriter.Readers
  offset : List Bool → ℕ
  dim : List Bool → ℕ
  directionWidth : List Bool → ℕ
  direction : List Bool → List Bool
  pivot : (u : List Bool) → Fin (dim u)

structure Inputs.Access (F : Inputs) : Prop where
  parent : NamedRationalParents.Access F.parent
  source : F.source.PolyTime
  offset : BinaryFn F.offset
  dim : UnaryFn F.dim
  directionWidth : UnaryFn F.directionWidth
  direction : SpaceFunction F.direction
  pivot : BinaryFn (fun u => (F.pivot u).val)
  sourceArity : ∀ u, (TermView.term (F.source.source u)).arity ≤ F.source.dim u

noncomputable def generic (F : Inputs) : RationalParentChildSource.Inputs where
  joint := ⟨⟨F.parent.coordinates, F.source, F.offset, F.dim⟩, F.parent.equation⟩
  directionWidth := F.directionWidth
  direction := F.direction
  pivot := F.pivot

theorem generic_access {F : Inputs} (h : F.Access) : (generic F).Access :=
  ⟨⟨⟨h.parent.coordinates, h.source, h.offset, h.dim⟩, h.parent.equation⟩,
    h.directionWidth, h.direction, h.pivot, h.sourceArity⟩

def source (q : List Bool) : List Bool := pairFst q
def childWord (q : List Bool) : List Bool := pairFst (pairSnd q)
def parentWord (q : List Bool) : List Bool := pairSnd (pairSnd q)
def parentLabel (q : List Bool) : List Bool := pair (source q) (parentWord q)
def childLabel (q : List Bool) : List Bool := pair (source q) (childWord q)
def Paired (q : List Bool) : Prop := pair (childWord q) (parentWord q) = pairSnd q

theorem source_FP : source ∈ FP := pairFst_mem_FP
theorem childWord_FP : childWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem parentWord_FP : parentWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem parentLabel_FP : parentLabel ∈ FP := mem_FP_pair source_FP parentWord_FP
theorem childLabel_FP : childLabel ∈ FP := mem_FP_pair source_FP childWord_FP
theorem paired_pred : FPPred Paired := stringEq_fppred (mem_FP_pair childWord_FP parentWord_FP) pairSnd_mem_FP

def childQuery (z : List Bool) : List Bool := pair (childLabel (pairFst z)) (pairSnd z)
def parentQuery (z : List Bool) : List Bool := pair (parentLabel (pairFst z)) (pairSnd z)
theorem childQuery_FP : childQuery ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP childLabel_FP) pairSnd_mem_FP
theorem parentQuery_FP : parentQuery ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP parentLabel_FP) pairSnd_mem_FP

noncomputable def count (F : Inputs) (q : List Bool) : ℕ := F.parent.equation.degree (source q) + 1
theorem count_binary {F : Inputs} (h : F.Access) : BinaryFn (count F) := by
  have hd : BinaryFn (fun q => F.parent.equation.degree (source q)) := h.parent.equation.degree.comp source_FP
  exact hd.add (BinaryFn.const 1)

noncomputable def agreement (F : Inputs) (q : List Bool) : Prop :=
  ∀ k < count F q,
    RationalParentChildDerivativeSigns.parentValue (generic F) (childQuery (pair q (BinaryNatCode.encode k))) =
      F.parent.derivativeValue (parentQuery (pair q (BinaryNatCode.encode k)))

theorem agreement_evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (fun q => [decide (agreement F q)]) := by
  have C := (RationalParentChildDerivativeSigns.parent_evaluator (generic_access h)).precompose childQuery childQuery_FP
  have P := h.parent.derivative.precompose parentQuery parentQuery_FP
  have E := (C.pairOutputs P).postcompose _ (stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have E' : SpaceFunction (fun z => [decide
      (RationalParentChildDerivativeSigns.parentValue (generic F) (childQuery z) =
        F.parent.derivativeValue (parentQuery z))]) :=
    E.congr (funext fun z => by simp only [Function.comp_apply, pairFst_pair, pairSnd_pair])
  have H := SpaceFunction.forall_binary E' (count_binary h)
  exact H.congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [agreement, List.cons.injEq, and_true, decide_eq_true_eq])

noncomputable def language (F : Inputs) : Language := {q | Paired q ∧
  parentLabel q ∈ NamedRationalParents.language F.parent ∧
    childLabel q ∈ RationalParentChildDescriptors.language (generic F) ∧ agreement F q}

theorem decider {F : Inputs} (h : F.Access) : SpaceDecider (language F) := by
  have P := (h.parent.validity.precompose parentLabel parentLabel_FP).flagEvaluator
  have C := ((RationalParentChildDescriptors.decider (generic_access h)).precompose childLabel childLabel_FP).flagEvaluator
  have E := (SpaceFunction.ofFP _ paired_pred.flag_mem_FP).andFlags (P.andFlags (C.andFlags (agreement_evaluator h)))
  apply E.decider (fun z => decide (z = [true])) (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) : language F ∈ PSPACE := (decider h).mem_PSPACE

theorem agreement_at (F : Inputs) (q : List Bool)
    (p : NamedRationalParents.Root F.parent (source q))
    (x : RationalParentChildRecordSpan.Root (generic F) (source q))
    (hp : F.parent.descriptor (source q) p = parentWord q)
    (hx : RationalParentChildHashChoice.descriptor (generic F) (source q) x = childWord q) :
    agreement F q ↔ RationalParentChildParameters.decode (generic F) (source q) x.val
      (RationalParentChildParentThom.first (generic F) (source q)) = p.val := by
  unfold agreement
  simp only [childQuery, parentQuery, pairFst_pair, pairSnd_pair, childLabel, parentLabel]
  simp_rw [← hp, ← hx, RationalParentChildDerivativeSigns.parent_packet, F.parent.derivative_packet,
    RationalParentChildTestSign.encode_eq_iff]
  have H := RationalParentChildParentThom.identifies_parent (generic F) (source q) x.val x.property p.val
    (F.parent.root_zero _ _ p.property)
  simp_rw [RationalParentChildParentThom.sign (generic F) (source q) _ x.val
    ((RationalParentChildQueries.mem_roots (generic F) (source q) x.val).mp x.property).1] at H
  constructor
  · intro hs
    apply H.mpr
    intro k hk
    exact hs k (by
      change k < F.parent.equation.degree (source q) + 1
      change k ≤ F.parent.equation.degree (source q) at hk
      omega)
  · intro he k hk
    exact H.mp he k (by
      change k ≤ F.parent.equation.degree (source q)
      change k < F.parent.equation.degree (source q) + 1 at hk
      omega)

theorem language_iff (F : Inputs) (q : List Bool) : q ∈ language F ↔ Paired q ∧
    ∃ (p : NamedRationalParents.Root F.parent (source q))
      (x : RationalParentChildRecordSpan.Root (generic F) (source q)),
      F.parent.descriptor (source q) p = parentWord q ∧
      RationalParentChildHashChoice.descriptor (generic F) (source q) x = childWord q ∧
      RationalParentChildParameters.decode (generic F) (source q) x.val
        (RationalParentChildParentThom.first (generic F) (source q)) = p.val := by
  change (Paired q ∧
    (∃ p : NamedRationalParents.Root F.parent (pairFst (parentLabel q)),
      F.parent.descriptor (pairFst (parentLabel q)) p = pairSnd (parentLabel q)) ∧
    (∃ x : RationalParentChildRecordSpan.Root (generic F) (pairFst (childLabel q)),
      RationalParentChildHashChoice.descriptor (generic F) (pairFst (childLabel q)) x = pairSnd (childLabel q)) ∧
    agreement F q) ↔ _
  have hp0 : pairFst (parentLabel q) = source q := pairFst_pair _ _
  have hp1 : pairSnd (parentLabel q) = parentWord q := pairSnd_pair _ _
  have hc0 : pairFst (childLabel q) = source q := pairFst_pair _ _
  have hc1 : pairSnd (childLabel q) = childWord q := pairSnd_pair _ _
  rw [hp0, hp1, hc0, hc1]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨⟨p, hp⟩, ⟨x, hx⟩, ha⟩
    exact ⟨p, x, hp, hx, (agreement_at F q p x hp hx).mp ha⟩
  · rintro ⟨p, x, hp, hx, he⟩
    exact ⟨⟨p, hp⟩, ⟨x, hx⟩, (agreement_at F q p x hp hx).mpr he⟩

theorem at_descriptors (F : Inputs) (u : List Bool) (p : NamedRationalParents.Root F.parent u)
    (x : RationalParentChildRecordSpan.Root (generic F) u) :
    pair u (pair (RationalParentChildHashChoice.descriptor (generic F) u x) (F.parent.descriptor u p)) ∈ language F ↔
      RationalParentChildParameters.decode (generic F) u x.val (RationalParentChildParentThom.first (generic F) u) = p.val := by
  generalize hq : pair u (pair (RationalParentChildHashChoice.descriptor (generic F) u x) (F.parent.descriptor u p)) = q
  have hu : source q = u := by rw [source, ← hq, pairFst_pair]
  have hc : childWord q = RationalParentChildHashChoice.descriptor (generic F) u x := by
    rw [childWord, ← hq, pairSnd_pair, pairFst_pair]
  have hp : parentWord q = F.parent.descriptor u p := by rw [parentWord, ← hq, pairSnd_pair, pairSnd_pair]
  have hpair : Paired q := by rw [Paired, hc, hp, ← hq, pairSnd_pair]
  rw [language_iff, and_iff_right hpair, hu, hc, hp]
  constructor
  · rintro ⟨p', x', hp, hx, he⟩
    have hpp := F.parent.descriptor_injective u hp
    have hxx := RationalParentChildHashChoice.descriptor_injective (generic F) u hx
    subst p'
    subst x'
    exact he
  · intro he
    exact ⟨p, x, rfl, rfl, he⟩

end LeanCanny.Encoding.NamedParentChildSelection
