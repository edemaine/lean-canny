/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedWitnessQuery

/-! # Source queries in the original coordinate order

Input-link gates undo the full source writer's swept-coordinate permutation.
The original coordinates come first, followed by the four added coordinates
and then arbitrary formula witnesses. Endpoint formulas retain their original
variable names. Both source and marking tests have native space certificates.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedOriginalQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation MvPolynomial
open LeanCanny.Geometry BoundedRealQuery RealQuery.Interleaved
open scoped Classical

def port (dim i : ℕ) : ℕ := if i = 0 then dim + 3 else i - 1

theorem port_unary {dim i : List Bool → ℕ} (hd : UnaryFn dim) (hi : UnaryFn i) :
    UnaryFn (fun c => port (dim c) (i c)) :=
  (UnaryFn.ite (FPPred.eq hi (UnaryFn.const 0)) (hd.add (UnaryFn.const 3))
    (hi.sub (UnaryFn.const 1))).of_eq (fun _ => rfl)

theorem port_fin (dim : ℕ) (i : Fin (dim + 4)) :
    port dim i.val = (BoundedFullGeometry.inputEquiv (dim + 3) i).val := by
  refine Fin.cases ?_ (fun i => ?_) i <;> simp [port, BoundedFullGeometry.inputEquiv, BoundedFullGeometry.inputIndex]

theorem port_bound (dim i : ℕ) (hi : i < dim + 4) : port dim i < dim + 4 := by
  rw [port_fin dim ⟨i, hi⟩]
  exact (BoundedFullGeometry.inputEquiv (dim + 3) ⟨i, hi⟩).isLt

noncomputable def sourceModels (P : BoundedFullWriter.Readers) (c : List Bool) :
    List (ℕ × MvPolynomial (Fin (P.dim c + 4)) ℤ) :=
  [(BoundedFullWriter.output P c, BoundedRegularSource.polynomial (BoundedFullWriter.original P c)
    (BoundedFullWriter.size P c) (BoundedFullWriter.size P c) (P.radius c))]

noncomputable def markedModels (P : BoundedFullWriter.Readers) (c : List Bool) :
    List (ℕ × MvPolynomial (Fin (P.dim c + 4)) ℤ) :=
  sourceModels P c ++ [(BoundedFullWriter.markOutput P c,
    BoundedRegularSource.markPolynomial (BoundedFullWriter.original P c) (P.radius c))]

noncomputable def SourcePoint (P : BoundedFullWriter.Readers) (c : List Bool)
    (x : Fin (P.dim c + 4) → ℝ) : Prop :=
  (BoundedRegularSource.polynomial (BoundedFullWriter.original P c) (BoundedFullWriter.size P c)
    (BoundedFullWriter.size P c) (P.radius c)).eval₂ (Int.castRingHom ℝ) x = 0

noncomputable def MarkedPoint (P : BoundedFullWriter.Readers) (c : List Bool)
    (x : Fin (P.dim c + 4) → ℝ) : Prop :=
  SourcePoint P c x ∧ (BoundedRegularSource.markPolynomial (BoundedFullWriter.original P c)
    (P.radius c)).eval₂ (Int.castRingHom ℝ) x = 0

theorem sourcePoint_comp (P : BoundedFullWriter.Readers) (f : List Bool → List Bool) (c : List Bool)
    (x : Fin (P.dim (f c) + 4) → ℝ) : SourcePoint (P.comp f) c x ↔ SourcePoint P (f c) x := by
  simp only [SourcePoint, BoundedFullWriter.original_comp, BoundedFullWriter.size_comp]
  rfl

theorem markedPoint_comp (P : BoundedFullWriter.Readers) (f : List Bool → List Bool) (c : List Bool)
    (x : Fin (P.dim (f c) + 4) → ℝ) : MarkedPoint (P.comp f) c x ↔ MarkedPoint P (f c) x := by
  simp only [MarkedPoint, sourcePoint_comp, BoundedFullWriter.original_comp]
  rfl

def MarkedAssignment (P : BoundedFullWriter.Readers) (c : List Bool) (x : ℕ → ℝ) : Prop :=
  MarkedPoint P c (fun i => x i.val)

theorem markedAssignment_comp (P : BoundedFullWriter.Readers) (f : List Bool → List Bool) (c : List Bool)
    (x : ℕ → ℝ) : MarkedAssignment (P.comp f) c x ↔ MarkedAssignment P (f c) x :=
  markedPoint_comp P f c _

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
      (BoundedFullWriter.start P c) (BoundedFullWriter.program P c) z.1 =
        rename Fin.val (rename (BoundedFullGeometry.inputEquiv (P.dim c + 3)) z.2) := by
  intro z hz
  obtain rfl := List.mem_singleton.mp hz
  exact BoundedFullGeometry.source_identity P c ht

private theorem marked_models (P : BoundedFullWriter.Readers) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    ∀ z ∈ markedModels P c, Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ))
      (BoundedFullWriter.start P c) (BoundedFullWriter.program P c) z.1 =
        rename Fin.val (rename (BoundedFullGeometry.inputEquiv (P.dim c + 3)) z.2) := by
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact source_models P c ht z hz
  · obtain rfl := List.mem_singleton.mp hz
    exact BoundedFullGeometry.mark_identity P c ht

theorem source_correct (P : BoundedFullWriter.Readers) (c : List Bool) (p : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    PortSatisfiable (P.dim c + 4) (BoundedFullWriter.start P c) (port (P.dim c)) (sourceGates P c) p ↔
      ∃ x : ℕ → ℝ, SourcePoint P c (fun i => x i.val) ∧ p.Holds x := by
  simpa [sourceModels, zeroGates, sourceGates, SourcePoint]
    using port_finite_correct (BoundedFullWriter.start P c) (BoundedFullWriter.program P c) (sourceModels P c) p
      (port (P.dim c)) (BoundedFullGeometry.inputEquiv (P.dim c + 3)) (Nat.le_max_right ..) (port_fin _)
      (BoundedFullWriter.wellFormed P c) (source_bound P c) (source_models P c ht)

theorem marked_correct (P : BoundedFullWriter.Readers) (c : List Bool) (p : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    PortSatisfiable (P.dim c + 4) (BoundedFullWriter.start P c) (port (P.dim c)) (markedGates P c) p ↔
      ∃ x : ℕ → ℝ, MarkedPoint P c (fun i => x i.val) ∧ p.Holds x := by
  simpa [markedModels, sourceModels, zeroGates, markedGates, MarkedPoint, SourcePoint]
    using port_finite_correct (BoundedFullWriter.start P c) (BoundedFullWriter.program P c) (markedModels P c) p
      (port (P.dim c)) (BoundedFullGeometry.inputEquiv (P.dim c + 3)) (Nat.le_max_right ..) (port_fin _)
      (BoundedFullWriter.wellFormed P c) (marked_bound P c) (marked_models P c ht)

theorem source_evaluator {P : BoundedFullWriter.Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (hp : (fun c => (p c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ, SourcePoint P c (fun i => x i.val) ∧ (p c).Holds x)]) := by
  have ha := fun c => zeroGates_arity (BoundedFullWriter.start P c) (BoundedFullWriter.program P c)
    (sourceModels P c) (BoundedFullWriter.wellFormed P c) (source_bound P c)
  apply (port_evaluator (h.dim.add (UnaryFn.const 4)) (BoundedFullWriter.start_unary h)
    ((BoundedFullWriter.start_unary h).add (BoundedFullWriter.length_unary h))
    (port_unary (h.dim.comp pairFst_mem_FP) (UnaryFn.length pairSnd_mem_FP)) (source_encode_mem_FP h) hp
    (fun _ => Nat.le_max_right ..) (fun _ => Nat.le_add_right ..)
    (fun c i hi => (port_bound _ _ hi).trans_le ((Nat.le_max_right ..).trans (Nat.le_add_right ..))) ha).congr
  funext c
  rw [source_correct P c (p c) (ht c)]

theorem marked_evaluator {P : BoundedFullWriter.Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (hp : (fun c => (p c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ, MarkedPoint P c (fun i => x i.val) ∧ (p c).Holds x)]) := by
  have ha := fun c => zeroGates_arity (BoundedFullWriter.start P c) (BoundedFullWriter.program P c)
    (markedModels P c) (BoundedFullWriter.wellFormed P c) (marked_bound P c)
  apply (port_evaluator (h.dim.add (UnaryFn.const 4)) (BoundedFullWriter.start_unary h)
    ((BoundedFullWriter.start_unary h).add (BoundedFullWriter.length_unary h))
    (port_unary (h.dim.comp pairFst_mem_FP) (UnaryFn.length pairSnd_mem_FP)) (marked_encode_mem_FP h) hp
    (fun _ => Nat.le_max_right ..) (fun _ => Nat.le_add_right ..)
    (fun c i hi => (port_bound _ _ hi).trans_le ((Nat.le_max_right ..).trans (Nat.le_add_right ..))) ha).congr
  funext c
  rw [marked_correct P c (p c) (ht c)]

end LeanCanny.Encoding.BoundedOriginalQuery
