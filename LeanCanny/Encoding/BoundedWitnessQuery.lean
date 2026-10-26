/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedRealQuery
public import LeanCanny.ETR.ComplexInterleavedPolynomial

/-! # Native bounded-source tests with independent existential witnesses

Only the first `dimension + 4` logical variables are source coordinates. All
further formula variables are independent real witnesses. Interleaving the
actual source program and the formula supplies native tests without a bound
on formula arity relative to the circuit's initial wire count.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedWitnessQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation MvPolynomial
open BoundedRealQuery RealQuery.Interleaved
open scoped Classical

noncomputable def sourceModels (P : BoundedFullWriter.Readers) (c : List Bool) :
    List (ℕ × MvPolynomial (Fin (P.dim c + 4)) ℤ) :=
  [(BoundedFullWriter.output P c, BoundedFullGeometry.polynomial (BoundedFullWriter.original P c)
    (BoundedFullWriter.size P c) (BoundedFullWriter.size P c) (P.radius c))]

noncomputable def markedModels (P : BoundedFullWriter.Readers) (c : List Bool) :
    List (ℕ × MvPolynomial (Fin (P.dim c + 4)) ℤ) :=
  sourceModels P c ++ [(BoundedFullWriter.markOutput P c,
    BoundedFullGeometry.markPolynomial (BoundedFullWriter.original P c) (P.radius c))]

private theorem source_bound (P : BoundedFullWriter.Readers) (c : List Bool) :
    ∀ z ∈ sourceModels P c, z.1 < BoundedFullWriter.start P c + (BoundedFullWriter.program P c).length := by
  intro z hz
  obtain rfl := List.mem_singleton.mp hz
  exact BoundedFullWriter.output_lt P c

private theorem marked_bound (P : BoundedFullWriter.Readers) (c : List Bool) :
    ∀ z ∈ markedModels P c, z.1 < BoundedFullWriter.start P c + (BoundedFullWriter.program P c).length := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact source_bound P c z hz
  · obtain rfl := List.mem_singleton.mp hz
    exact BoundedFullWriter.markOutput_lt P c

private theorem source_models (P : BoundedFullWriter.Readers) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    ∀ z ∈ sourceModels P c, Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ))
      (BoundedFullWriter.start P c) (BoundedFullWriter.program P c) z.1 = rename Fin.val z.2 := by
  intro z hz
  obtain rfl := List.mem_singleton.mp hz
  exact BoundedFullGeometry.source_identity P c ht

private theorem marked_models (P : BoundedFullWriter.Readers) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    ∀ z ∈ markedModels P c, Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ))
      (BoundedFullWriter.start P c) (BoundedFullWriter.program P c) z.1 = rename Fin.val z.2 := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact source_models P c ht z hz
  · obtain rfl := List.mem_singleton.mp hz
    exact BoundedFullGeometry.mark_identity P c ht

theorem source_correct (P : BoundedFullWriter.Readers) (c : List Bool) (p : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    InputSatisfiable (P.dim c + 4) (BoundedFullWriter.start P c) (sourceGates P c) p ↔
      ∃ x : ℕ → ℝ, SourcePoint P c (fun i => x i.val) ∧ p.Holds x := by
  simpa [sourceModels, zeroGates, sourceGates, SourcePoint]
    using finite_correct (BoundedFullWriter.start P c) (BoundedFullWriter.program P c) (sourceModels P c) p
      (Nat.le_max_right ..) (BoundedFullWriter.wellFormed P c) (source_bound P c) (source_models P c ht)

theorem marked_correct (P : BoundedFullWriter.Readers) (c : List Bool) (p : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    InputSatisfiable (P.dim c + 4) (BoundedFullWriter.start P c) (markedGates P c) p ↔
      ∃ x : ℕ → ℝ, MarkedPoint P c (fun i => x i.val) ∧ p.Holds x := by
  simpa [markedModels, sourceModels, zeroGates, markedGates, MarkedPoint, SourcePoint]
    using finite_correct (BoundedFullWriter.start P c) (BoundedFullWriter.program P c) (markedModels P c) p
      (Nat.le_max_right ..) (BoundedFullWriter.wellFormed P c) (marked_bound P c) (marked_models P c ht)

theorem source_evaluator {P : BoundedFullWriter.Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (hp : (fun c => (p c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ, SourcePoint P c (fun i => x i.val) ∧ (p c).Holds x)]) := by
  have ha := fun c => zeroGates_arity (BoundedFullWriter.start P c) (BoundedFullWriter.program P c)
    (sourceModels P c) (BoundedFullWriter.wellFormed P c) (source_bound P c)
  apply (evaluator (h.dim.add (UnaryFn.const 4)) (BoundedFullWriter.start_unary h)
    ((BoundedFullWriter.start_unary h).add (BoundedFullWriter.length_unary h))
    (source_encode_mem_FP h) hp (fun _ => Nat.le_max_right ..) (fun _ => Nat.le_add_right ..) ha).congr
  funext c
  rw [source_correct P c (p c) (ht c)]

theorem marked_evaluator {P : BoundedFullWriter.Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (hp : (fun c => (p c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ, MarkedPoint P c (fun i => x i.val) ∧ (p c).Holds x)]) := by
  have ha := fun c => zeroGates_arity (BoundedFullWriter.start P c) (BoundedFullWriter.program P c)
    (markedModels P c) (BoundedFullWriter.wellFormed P c) (marked_bound P c)
  apply (evaluator (h.dim.add (UnaryFn.const 4)) (BoundedFullWriter.start_unary h)
    ((BoundedFullWriter.start_unary h).add (BoundedFullWriter.length_unary h))
    (marked_encode_mem_FP h) hp (fun _ => Nat.le_max_right ..) (fun _ => Nat.le_add_right ..) ha).congr
  funext c
  rw [marked_correct P c (p c) (ht c)]

end LeanCanny.Encoding.BoundedWitnessQuery
