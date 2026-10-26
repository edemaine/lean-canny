/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedOriginalQuery
public import LeanCanny.ETR.ComplexDuplicatedPorts

/-! # Native intersections with independent formula assignments

The two formulas share the full finite source point and keep independent
witness coordinates. Duplicate input links identify the shared coordinates;
the actual source circuit is serialized only once.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedIntersectionQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation
open BoundedFullWriter BoundedOriginalQuery BoundedRealQuery RealQuery.Interleaved
open scoped Classical

def SourceIntersection (P : Readers) (c : List Bool) (p q : Formula) : Prop :=
  ∃ a b : ℕ → ℝ, BoundedOriginalQuery.SourcePoint P c (fun i => a i.val) ∧
    (∀ i < P.dim c + 4, a i = b i) ∧ p.Holds a ∧ q.Holds b

def MarkedIntersection (P : Readers) (c : List Bool) (p q : Formula) : Prop :=
  ∃ a b : ℕ → ℝ, BoundedOriginalQuery.MarkedPoint P c (fun i => a i.val) ∧
    (∀ i < P.dim c + 4, a i = b i) ∧ p.Holds a ∧ q.Holds b

theorem source_correct (P : Readers) (c : List Bool) (p q : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    PortSatisfiable (2 * (P.dim c + 4)) (start P c) (Duplicated.port (BoundedOriginalQuery.port (P.dim c)))
      (sourceGates P c) (Duplicated.combine p q) ↔ SourceIntersection P c p q := by
  rw [Duplicated.satisfiable_iff]
  apply exists_congr
  intro a
  apply exists_congr
  intro b
  exact and_congr (source_realizes P c a ht) Iff.rfl

theorem marked_correct (P : Readers) (c : List Bool) (p q : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    PortSatisfiable (2 * (P.dim c + 4)) (start P c) (Duplicated.port (BoundedOriginalQuery.port (P.dim c)))
      (markedGates P c) (Duplicated.combine p q) ↔ MarkedIntersection P c p q := by
  rw [Duplicated.satisfiable_iff]
  apply exists_congr
  intro a
  apply exists_congr
  intro b
  exact and_congr (marked_realizes P c a ht) Iff.rfl

theorem source_evaluator {P : Readers} {p q : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hp : (fun c => (p c).encode) ∈ FP) (hq : (fun c => (q c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide (SourceIntersection P c (p c) (q c))]) := by
  apply (Duplicated.evaluator (h.dim.add (UnaryFn.const 4)) (start_unary h)
    ((start_unary h).add (length_unary h))
    (BoundedOriginalQuery.port_unary (h.dim.comp pairFst_mem_FP) (UnaryFn.length pairSnd_mem_FP))
    (source_encode_mem_FP h) hp hq
    (fun _ i hi => (BoundedOriginalQuery.port_bound _ i hi).trans_le (Nat.le_max_right ..))
    (fun _ => Nat.le_add_right ..) (source_arity P)).congr
  funext c
  rw [source_correct P c (p c) (q c) (ht c)]

theorem marked_evaluator {P : Readers} {p q : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hp : (fun c => (p c).encode) ∈ FP) (hq : (fun c => (q c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide (MarkedIntersection P c (p c) (q c))]) := by
  apply (Duplicated.evaluator (h.dim.add (UnaryFn.const 4)) (start_unary h)
    ((start_unary h).add (length_unary h))
    (BoundedOriginalQuery.port_unary (h.dim.comp pairFst_mem_FP) (UnaryFn.length pairSnd_mem_FP))
    (marked_encode_mem_FP h) hp hq
    (fun _ i hi => (BoundedOriginalQuery.port_bound _ i hi).trans_le (Nat.le_max_right ..))
    (fun _ => Nat.le_add_right ..) (marked_arity P)).congr
  funext c
  rw [marked_correct P c (p c) (q c) (ht c)]

end LeanCanny.Encoding.BoundedIntersectionQuery
