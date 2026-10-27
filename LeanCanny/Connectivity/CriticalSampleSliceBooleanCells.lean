/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.CriticalSampleSliceBooleanAtoms

/-! # Native selection of cells by Boolean sign circuits

Circuit gates and atom indices come from the original source. Native atom
decisions supply their truth values on each cell, without storing the factor
sign vector. Selection is exactly nonemptiness of the restricted cell in the
actual circuit-defined real solution set.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CriticalSampleSliceBooleanCells
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice CriticalSampleSliceCellCover CriticalSampleSliceBooleanAtoms
open scoped Classical

def source (c : List Bool) : List Bool := context (pairFst c)
theorem source_FP : source ∈ FP := mem_FP_comp pairFst_mem_FP context_FP

def truth (S : Source) (c : List Bool) {n : ℕ} (σ : Fin n → SignType) : Prop :=
  BooleanCircuitSpace.value S.circuit (semanticAtom S σ) c = true

noncomputable def value (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) : List Bool → Bool :=
  BooleanCircuitSpace.value (S.circuit.comp source) (atom P Q S)

theorem evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (B : Access S) :
    SpaceFunction (fun c => [value P Q S c]) := by
  have E := BooleanCircuitSpace.evaluator (S.circuit.comp source) (B.circuit.comp source source_FP)
    (atom P Q S) (CriticalSampleSliceBooleanAtoms.decider h A ha S B).flagEvaluator
  exact E

theorem value_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) (hu : u ∈ valid P)
    (c : Index P Q u) (y : ℝ) (hy : y ∈ piece P Q u c) :
    value P Q S (pair u (CriticalSampleSliceCellLabels.label P Q u c)) =
      BooleanCircuitSpace.value S.circuit (semanticAtom S (signVector P Q u y)) (context u) := by
  unfold value
  have H := BooleanCircuitSpace.value_comp S.circuit source (atom P Q S) (semanticAtom S (signVector P Q u y))
    (pair u (CriticalSampleSliceCellLabels.label P Q u c)) (fun k _ => by
      simpa only [source, pairFst_pair] using CriticalSampleSliceBooleanAtoms.packet P Q S u hu c k y hy)
  simpa only [source, pairFst_pair] using H

noncomputable def restrictedPiece (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) :=
  CriticalSampleSliceCellCover.restrictedPiece P Q u (truth S (context u))

theorem accessible (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) (hu : u ∈ valid P)
    (c : Index P Q u) : FrontierCover.Accessible (restrictedPiece P Q S u c) :=
  CriticalSampleSliceCellCover.accessible P Q u hu (truth S (context u)) c

theorem nonempty_iff (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) (hu : u ∈ valid P)
    (c : Index P Q u) :
    (restrictedPiece P Q S u c).Nonempty ↔ value P Q S (pair u (CriticalSampleSliceCellLabels.label P Q u c)) = true := by
  constructor
  · rintro ⟨x, hx⟩
    rw [value_packet P Q S u hu c x.val hx]
    exact x.property
  · intro H
    obtain ⟨x, hx⟩ := Geometry.OrderedRealCells.piece_nonempty (roots P Q u) c
    have hs : x ∈ solutionSet P Q u (truth S (context u)) := by
      change BooleanCircuitSpace.value S.circuit (semanticAtom S (signVector P Q u x)) (context u) = true
      rw [← value_packet P Q S u hu c x hx]
      exact H
    exact ⟨⟨x, hs⟩, hx⟩

noncomputable def language (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) : Language := {c |
  c ∈ CriticalSampleSliceCellLabels.language P Q ∧ value P Q S c = true}

private def both (z : List Bool) : Bool := decide (pairFst z = [true] ∧ pairSnd z = [true])
private theorem both_FP : (fun z => [both z]) ∈ FP :=
  ((Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).and
    (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true]))).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (B : Access S) :
    SpaceDecider (language P Q S) := by
  have L := (CriticalSampleSliceCellLabels.decider h A ha).flagEvaluator
  have E := evaluator h A ha S B
  apply (L.pairOutputs E).decider both both_FP
  intro c
  simp only [language, Set.mem_ofPred_eq, both, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool) (hu : u ∈ valid P)
    (c : Index P Q u) :
    pair u (CriticalSampleSliceCellLabels.label P Q u c) ∈ language P Q S ↔ (restrictedPiece P Q S u c).Nonempty := by
  change _ ∧ _ ↔ _
  rw [and_iff_right (CriticalSampleSliceCellLabels.label_valid P Q u hu c), nonempty_iff P Q S u hu c]

theorem invalid_base (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u c : List Bool) (hu : u ∉ valid P) :
    pair u c ∉ language P Q S := fun H => CriticalSampleSliceCellLabels.invalid_base P Q u c hu H.1

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (B : Access S) :
    language P Q S ∈ PSPACE := (decider h A ha S B).mem_PSPACE

end LeanCanny.Connectivity.CriticalSampleSliceBooleanCells
