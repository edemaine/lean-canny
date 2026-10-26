/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.BoundedEndpointQuery
public import LeanCanny.Encoding.BoundedIntersectionQuery

/-! # Native graph tests for witness-defined bounded-source pieces

Validity, marking and intersection use actual shared-source queries. The two
pieces in an intersection have independent existential assignments and agree
on the entire source point. No adjacency or marking routine is assumed.
-/

@[expose] public section
namespace LeanCanny.Connectivity.BoundedPieceQueries
open ETR Geometry Computation Encoding Encoding.BoundedFullWriter Encoding.BoundedOriginalQuery
open BoundedEndpointQuery Encoding.BoundedIntersectionQuery Set
open scoped Classical

noncomputable def Source (P : Readers) (c : List Bool) :=
  BoundedRegularSource.Zeros (original P c) (size P c) (size P c) (P.radius c)

def piece (P : Readers) (c : List Bool) (p : Formula) : Set (Source P c) :=
  {z | witnessPiece p z.val}

noncomputable def marked (P : Readers) (c : List Bool) : Set (Source P c) :=
  BoundedRegularSource.Marked (original P c) (size P c) (size P c) (P.radius c)

theorem nonempty_correct (P : Readers) (c : List Bool) (p : Formula) :
    (∃ x : ℕ → ℝ, SourcePoint P c (fun i => x i.val) ∧ p.Holds x) ↔ (piece P c p).Nonempty := by
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨⟨fun i => x i.val, hx⟩, x, fun _ => rfl, hp⟩
  · rintro ⟨z, x, hx, hp⟩
    refine ⟨x, ?_, hp⟩
    rw [funext hx]
    exact z.property

theorem marked_nonempty_correct (P : Readers) (c : List Bool) (p : Formula) :
    (∃ x : ℕ → ℝ, MarkedPoint P c (fun i => x i.val) ∧ p.Holds x) ↔
      (piece P c p ∩ marked P c).Nonempty := by
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨⟨fun i => x i.val, hx.1⟩, ⟨x, fun _ => rfl, hp⟩, hx.2⟩
  · rintro ⟨z, ⟨x, hx, hp⟩, hz⟩
    refine ⟨x, ?_, hp⟩
    rw [funext hx]
    exact ⟨z.property, hz⟩

theorem intersection_correct (P : Readers) (c : List Bool) (p q : Formula) :
    SourceIntersection P c p q ↔ (piece P c p ∩ piece P c q).Nonempty := by
  constructor
  · rintro ⟨a, b, ha, he, hp, hq⟩
    refine ⟨⟨fun i => a i.val, ha⟩, ⟨a, fun _ => rfl, hp⟩, b, ?_, hq⟩
    intro i
    exact (he i.val i.isLt).symm
  · rintro ⟨z, ⟨a, ha, hp⟩, ⟨b, hb, hq⟩⟩
    refine ⟨a, b, ?_, ?_, hp, hq⟩
    · rw [funext ha]
      exact z.property
    · intro i hi
      exact (ha ⟨i, hi⟩).trans (hb ⟨i, hi⟩).symm

theorem marked_intersection_correct (P : Readers) (c : List Bool) (p q : Formula) :
    MarkedIntersection P c p q ↔ (piece P c p ∩ piece P c q ∩ marked P c).Nonempty := by
  constructor
  · rintro ⟨a, b, ha, he, hp, hq⟩
    refine ⟨⟨fun i => a i.val, ha.1⟩, ⟨⟨a, fun _ => rfl, hp⟩, b, ?_, hq⟩, ha.2⟩
    intro i
    exact (he i.val i.isLt).symm
  · rintro ⟨z, ⟨⟨a, ha, hp⟩, ⟨b, hb, hq⟩⟩, hz⟩
    refine ⟨a, b, ?_, ?_, hp, hq⟩
    · rw [funext ha]
      exact ⟨z.property, hz⟩
    · intro i hi
      exact (ha ⟨i, hi⟩).trans (hb ⟨i, hi⟩).symm

attribute [local irreducible] SourcePoint MarkedPoint SourceIntersection MarkedIntersection

theorem validity_evaluator {P : Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (hp : (fun c => (p c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide ((piece P c (p c)).Nonempty)]) := by
  apply (Encoding.BoundedOriginalQuery.source_evaluator h ht hp).congr
  funext c
  rw [nonempty_correct]

theorem marking_evaluator {P : Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (hp : (fun c => (p c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide ((piece P c (p c) ∩ marked P c).Nonempty)]) := by
  apply (Encoding.BoundedOriginalQuery.marked_evaluator h ht hp).congr
  funext c
  rw [marked_nonempty_correct]

theorem adjacency_evaluator {P : Readers} {p q : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hp : (fun c => (p c).encode) ∈ FP) (hq : (fun c => (q c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide ((piece P c (p c) ∩ piece P c (q c)).Nonempty)]) := by
  apply (Encoding.BoundedIntersectionQuery.source_evaluator h ht hp hq).congr
  funext c
  rw [intersection_correct]

theorem marked_adjacency_evaluator {P : Readers} {p q : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hp : (fun c => (p c).encode) ∈ FP) (hq : (fun c => (q c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide ((piece P c (p c) ∩ piece P c (q c) ∩ marked P c).Nonempty)]) := by
  apply (Encoding.BoundedIntersectionQuery.marked_evaluator h ht hp hq).congr
  funext c
  rw [marked_intersection_correct]

end LeanCanny.Connectivity.BoundedPieceQueries
