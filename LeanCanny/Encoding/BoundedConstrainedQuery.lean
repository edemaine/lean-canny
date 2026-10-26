/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedRealQuery
public import LeanCanny.ETR.ComplexRealConstraints

/-! # Formula-constrained queries on the generated regular source

Source membership, marking and a Boolean coordinate formula share one real
assignment. These native tests can constrain source pieces, intersections and
endpoint descriptions while retaining the shared source circuit.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedConstrainedQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation MvPolynomial
open BoundedRealQuery
open scoped Classical

private theorem holds_restrict {n : ℕ} (p : Formula) (hp : p.arity ≤ n) (x : ℕ → ℝ) :
    p.Holds x ↔ p.Holds (Formula.extend (fun i : Fin n => x i.val)) := by
  apply p.holds_congr
  intro i hi
  simp [Formula.extend, hi.trans_le hp]

private theorem eval_extend {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (x : Fin n → ℝ) :
    (rename Fin.val p).eval₂ (Int.castRingHom ℝ) (Formula.extend x) = p.eval₂ (Int.castRingHom ℝ) x := by
  rw [eval₂_rename]
  apply congrArg (p.eval₂ (Int.castRingHom ℝ))
  funext i
  simp [Formula.extend, i.isLt]

theorem source_correct (P : BoundedFullWriter.Readers) (c : List Bool) (p : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) (hp : p.arity ≤ P.dim c + 4) :
    RealQuery.WithConstraints (BoundedFullWriter.start P c) (sourceGates P c) p ↔
      ∃ x : Fin (P.dim c + 4) → ℝ, SourcePoint P c x ∧ p.Holds (Formula.extend x) := by
  have hb : ∀ out ∈ [BoundedFullWriter.output P c],
      out < BoundedFullWriter.start P c + (BoundedFullWriter.program P c).length := by
    intro out hout
    obtain rfl := List.mem_singleton.mp hout
    exact BoundedFullWriter.output_lt P c
  rw [sourceGates, show [Gate.zero (BoundedFullWriter.output P c)] =
    [BoundedFullWriter.output P c].map Gate.zero from rfl,
    RealQuery.zero_constraints_with_iff _ _ _ _ (BoundedFullWriter.wellFormed P c) hb
      (hp.trans (Nat.le_max_right ..))]
  constructor
  · rintro ⟨x, hx, hpred⟩
    refine ⟨fun i => x i.val, ?_, (holds_restrict p hp x).mp hpred⟩
    simpa only [SourcePoint, BoundedFullGeometry.source_identity P c ht, eval₂_rename, Function.comp_def]
      using hx _ (List.mem_singleton_self _)
  · rintro ⟨x, hx, hpred⟩
    refine ⟨Formula.extend x, ?_, hpred⟩
    intro out hout
    obtain rfl := List.mem_singleton.mp hout
    simpa only [SourcePoint, BoundedFullGeometry.source_identity P c ht, eval_extend] using hx

theorem marked_correct (P : BoundedFullWriter.Readers) (c : List Bool) (p : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) (hp : p.arity ≤ P.dim c + 4) :
    RealQuery.WithConstraints (BoundedFullWriter.start P c) (markedGates P c) p ↔
      ∃ x : Fin (P.dim c + 4) → ℝ, MarkedPoint P c x ∧ p.Holds (Formula.extend x) := by
  have hb : ∀ out ∈ [BoundedFullWriter.output P c, BoundedFullWriter.markOutput P c],
      out < BoundedFullWriter.start P c + (BoundedFullWriter.program P c).length := by
    intro out hout
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
    rcases hout with rfl | rfl
    · exact BoundedFullWriter.output_lt P c
    · exact BoundedFullWriter.markOutput_lt P c
  rw [markedGates, show [Gate.zero (BoundedFullWriter.output P c), Gate.zero (BoundedFullWriter.markOutput P c)] =
    [BoundedFullWriter.output P c, BoundedFullWriter.markOutput P c].map Gate.zero from rfl,
    RealQuery.zero_constraints_with_iff _ _ _ _ (BoundedFullWriter.wellFormed P c) hb
      (hp.trans (Nat.le_max_right ..))]
  constructor
  · rintro ⟨x, hx, hpred⟩
    refine ⟨fun i => x i.val, ⟨?_, ?_⟩, (holds_restrict p hp x).mp hpred⟩
    · simpa only [SourcePoint, BoundedFullGeometry.source_identity P c ht, eval₂_rename, Function.comp_def]
        using hx (BoundedFullWriter.output P c) (by simp)
    · simpa only [BoundedFullGeometry.mark_identity P c ht, eval₂_rename, Function.comp_def]
        using hx (BoundedFullWriter.markOutput P c) (by simp)
  · rintro ⟨x, ⟨hs, hm⟩, hpred⟩
    refine ⟨Formula.extend x, ?_, hpred⟩
    intro out hout
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
    rcases hout with rfl | rfl
    · simpa only [SourcePoint, BoundedFullGeometry.source_identity P c ht, eval_extend] using hs
    · simpa only [BoundedFullGeometry.mark_identity P c ht, eval_extend] using hm

theorem source_evaluator {P : BoundedFullWriter.Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (hp : (fun c => (p c).encode) ∈ FP)
    (ha : ∀ c, (p c).arity ≤ P.dim c + 4) :
    SpaceFunction (fun c => [decide (∃ x, SourcePoint P c x ∧ (p c).Holds (Formula.extend x))]) := by
  apply (RealQuery.constraint_evaluator (BoundedFullWriter.start_unary h) (source_encode_mem_FP h) hp).congr
  funext c
  rw [source_correct P c (p c) (ht c) (ha c)]

theorem marked_evaluator {P : BoundedFullWriter.Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (hp : (fun c => (p c).encode) ∈ FP)
    (ha : ∀ c, (p c).arity ≤ P.dim c + 4) :
    SpaceFunction (fun c => [decide (∃ x, MarkedPoint P c x ∧ (p c).Holds (Formula.extend x))]) := by
  apply (RealQuery.constraint_evaluator (BoundedFullWriter.start_unary h) (marked_encode_mem_FP h) hp).congr
  funext c
  rw [marked_correct P c (p c) (ht c) (ha c)]

end LeanCanny.Encoding.BoundedConstrainedQuery
