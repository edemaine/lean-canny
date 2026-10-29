/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.NamedParentChildSelection

/-! # Native named-parent closure with complete ancestry

Actual children satisfy the joint equations and Jacobian condition and retain
an actual named parent. Their names store the newest descriptor before the
parent name. Native selection validates precisely these names. The resulting
separable parameter, defined ambient coordinates, validity decider, and
derivative probes give another named parent source.
-/

@[expose] public section
namespace LeanCanny.Encoding.NamedParentChildNext
open LeanCanny.Algebra LeanCanny.Computation
open NamedParentChildSelection (Inputs generic generic_access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd RationalParentChildQueries.roots RationalParentChildCoordinates.parameter
  RationalParentChildHashChoice.descriptor RationalParentChildParameters.decode
  RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight

def Actual (F : Inputs) (u : List Bool) (theta : ℝ) : Prop :=
  theta ∈ RationalParentChildQueries.roots (generic F) u ∧
    RationalParentChildParents.retained (generic F) u theta ∈ F.parent.roots u

abbrev Root (F : Inputs) (u : List Bool) := {theta : ℝ // Actual F u theta}

noncomputable def childRoot (F : Inputs) (u : List Bool) (x : Root F u) :
    RationalParentChildRecordSpan.Root (generic F) u := ⟨x.val, x.property.1⟩
noncomputable def parentRoot (F : Inputs) (u : List Bool) (x : Root F u) : NamedRationalParents.Root F.parent u :=
  ⟨RationalParentChildParents.retained (generic F) u x.val, x.property.2⟩

noncomputable def word (F : Inputs) (u : List Bool) (x : Root F u) : List Bool :=
  pair (RationalParentChildHashChoice.descriptor (generic F) u (childRoot F u x))
    (F.parent.descriptor u (parentRoot F u x))

theorem word_injective (F : Inputs) (u : List Bool) : Function.Injective (word F u) := by
  intro x y h
  have H := congrArg pairFst h
  simp only [word, pairFst_pair] at H
  have he := RationalParentChildHashChoice.descriptor_injective (generic F) u H
  apply Subtype.ext
  exact congrArg (fun z : RationalParentChildRecordSpan.Root (generic F) u => z.val) he

noncomputable def width (F : Inputs) (u : List Bool) : ℕ :=
  2 * RationalParentChildHashChoice.descriptorWidth (generic F) u + 2 + F.parent.width u

theorem word_length (F : Inputs) (u : List Bool) (x : Root F u) : (word F u x).length ≤ width F u := by
  rw [word, pair_length]
  have hc := RationalParentChildHashChoice.descriptor_length_le (generic F) u (childRoot F u x)
  have hp := F.parent.descriptor_length u (parentRoot F u x)
  unfold width
  omega

noncomputable def derivativeValue (F : Inputs) : List Bool → List Bool :=
  RationalParentChildDerivativeSigns.currentValue (generic F) ∘ NamedParentChildSelection.childQuery

noncomputable def next (F : Inputs) : NamedRationalParents.Source where
  equation := RationalParentChildParents.parameter (generic F)
  coordinates := RationalParentChildParents.ambient (generic F)
  roots u := {theta | Actual F u theta}
  root_zero u theta ht := ((RationalParentChildQueries.mem_roots (generic F) u theta).mp ht.1).1
  defined u theta ht := RationalParentChildParents.ambient_defined (generic F) u theta
    (((RationalParentChildQueries.mem_roots (generic F) u theta).mp ht.1).1)
      (F.parent.defined u _ ht.2)
  descriptor := word F
  descriptor_injective := word_injective F
  width := width F
  descriptor_length := word_length F
  derivativeValue := derivativeValue F
  derivative_packet u x k := by
    simpa only [derivativeValue, Function.comp_apply, NamedParentChildSelection.childQuery,
      NamedParentChildSelection.childLabel, NamedParentChildSelection.source, NamedParentChildSelection.childWord,
      word, childRoot, pairFst_pair, pairSnd_pair] using
        RationalParentChildDerivativeSigns.current_packet (generic F) u (childRoot F u x) k

theorem language_eq_selection (F : Inputs) : NamedRationalParents.language (next F) = NamedParentChildSelection.language F := by
  ext q
  rw [NamedParentChildSelection.language_iff]
  change (∃ x : Root F (NamedParentChildSelection.source q), word F _ x = pairSnd q) ↔ _
  constructor
  · rintro ⟨x, hx⟩
    have hc : RationalParentChildHashChoice.descriptor (generic F) (NamedParentChildSelection.source q)
        (childRoot F _ x) = NamedParentChildSelection.childWord q := by
      simpa only [word, pairFst_pair, NamedParentChildSelection.childWord] using congrArg pairFst hx
    have hp : F.parent.descriptor (NamedParentChildSelection.source q) (parentRoot F _ x) =
        NamedParentChildSelection.parentWord q := by
      simpa only [word, pairSnd_pair, NamedParentChildSelection.parentWord] using congrArg pairSnd hx
    refine ⟨?_, parentRoot F _ x, childRoot F _ x, hp, hc, ?_⟩
    · unfold NamedParentChildSelection.Paired
      rw [← hc, ← hp]
      exact hx
    · rfl
  · rintro ⟨hq, p, x, hp, hc, he⟩
    have hm : RationalParentChildParents.retained (generic F) (NamedParentChildSelection.source q) x.val ∈
        F.parent.roots (NamedParentChildSelection.source q) := by
      change RationalParentChildParameters.decode (generic F) (NamedParentChildSelection.source q) x.val
        (RationalParentChildParentThom.first (generic F) (NamedParentChildSelection.source q)) ∈ _
      rw [he]
      exact p.property
    let y : Root F (NamedParentChildSelection.source q) := ⟨x.val, x.property, hm⟩
    have hcy : childRoot F _ y = x := Subtype.ext rfl
    have hpy : parentRoot F _ y = p := Subtype.ext he
    refine ⟨y, ?_⟩
    rw [word, hcy, hpy, hc, hp]
    exact hq

theorem access {F : Inputs} (h : F.Access) : NamedRationalParents.Access (next F) := by
  refine ⟨RationalParentChildParents.parameter_access (generic_access h),
    RationalParentChildParents.ambient_access (generic_access h), ?_, ?_, ?_⟩
  · exact (((UnaryFn.const 2).mul (RationalParentChildHashChoice.descriptorWidth_unary (generic_access h))).add
      (UnaryFn.const 2)).add h.parent.width
  · rw [language_eq_selection]
    exact NamedParentChildSelection.decider h
  · exact (RationalParentChildDerivativeSigns.current_evaluator (generic_access h)).precompose
      NamedParentChildSelection.childQuery NamedParentChildSelection.childQuery_FP

end LeanCanny.Encoding.NamedParentChildNext
