/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullGeometry
public import LeanCanny.ETR.ComplexRealEvaluation

/-! # Native real feasibility tests for the full bounded regular source

The source and mark wires are tested over real input coordinates. Their
auxiliary circuit wires retain sharing, and the encoders use only the original
term, unary dimension and binary radius readers. The tests characterize actual
finite-dimensional real source points and marked source points.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedRealQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation MvPolynomial
open LeanCanny.Encoding.Brackets
open scoped Classical

private theorem appendZero_encode_mem_FP {gates : List Bool → List Gate} {out : List Bool → ℕ}
    (hg : (fun c => encode (gates c)) ∈ FP) (ho : UnaryFn out) :
    (fun c => encode (gates c ++ [.zero (out c)])) ∈ FP := by
  have h := mem_FP_comp (appendFn_mem_FP (mem_FP_comp hg contents_mem_FP)
    (zeroGateBits_mem_FP ho)) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, contents_encode, zeroGateBits_encode]
  simp only [encode_eq_wrap, forest_append, forest_cons, forest_nil, List.append_nil]

noncomputable def sourceGates (P : BoundedFullWriter.Readers) (c : List Bool) : List Gate :=
  StraightLine.gates (BoundedFullWriter.start P c) (BoundedFullWriter.program P c) ++
    [.zero (BoundedFullWriter.output P c)]

noncomputable def markedGates (P : BoundedFullWriter.Readers) (c : List Bool) : List Gate :=
  StraightLine.gates (BoundedFullWriter.start P c) (BoundedFullWriter.program P c) ++
    [.zero (BoundedFullWriter.output P c), .zero (BoundedFullWriter.markOutput P c)]

theorem source_encode_mem_FP {P : BoundedFullWriter.Readers} (h : P.PolyTime) :
    (fun c => encode (sourceGates P c)) ∈ FP :=
  appendZero_encode_mem_FP (BoundedFullWriter.encode_mem_FP h) (BoundedFullWriter.output_unary h)

theorem marked_encode_mem_FP {P : BoundedFullWriter.Readers} (h : P.PolyTime) :
    (fun c => encode (markedGates P c)) ∈ FP := by
  apply mem_FP_of_eq (appendZero_encode_mem_FP (source_encode_mem_FP h) (BoundedFullWriter.markOutput_unary h))
  intro c
  simp only [sourceGates, markedGates, List.append_assoc, List.cons_append, List.nil_append]

noncomputable def SourcePoint (P : BoundedFullWriter.Readers) (c : List Bool)
    (x : Fin (P.dim c + 4) → ℝ) : Prop :=
  (BoundedFullGeometry.polynomial (BoundedFullWriter.original P c) (BoundedFullWriter.size P c)
    (BoundedFullWriter.size P c) (P.radius c)).eval₂ (Int.castRingHom ℝ) x = 0

noncomputable def MarkedPoint (P : BoundedFullWriter.Readers) (c : List Bool)
    (x : Fin (P.dim c + 4) → ℝ) : Prop :=
  SourcePoint P c x ∧ (BoundedFullGeometry.markPolynomial (BoundedFullWriter.original P c)
    (P.radius c)).eval₂ (Int.castRingHom ℝ) x = 0

private theorem eval_extend {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (x : Fin n → ℝ) :
    (rename Fin.val p).eval₂ (Int.castRingHom ℝ) (Formula.extend x) = p.eval₂ (Int.castRingHom ℝ) x := by
  rw [eval₂_rename]
  apply congrArg (p.eval₂ (Int.castRingHom ℝ))
  funext i
  simp [Formula.extend, i.isLt]

theorem source_correct (P : BoundedFullWriter.Readers) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    RealQuery.Satisfiable (BoundedFullWriter.start P c) (sourceGates P c) ↔
      ∃ x : Fin (P.dim c + 4) → ℝ, SourcePoint P c x := by
  rw [sourceGates, show [Gate.zero (BoundedFullWriter.output P c)] =
    [BoundedFullWriter.output P c].map Gate.zero from rfl,
    RealQuery.zero_constraints_iff _ _ _ (BoundedFullWriter.wellFormed P c)
      (by simpa only [List.mem_singleton] using fun out (he : out = BoundedFullWriter.output P c) =>
        he ▸ BoundedFullWriter.output_lt P c)]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun i => x i.val, ?_⟩
    simpa only [SourcePoint, BoundedFullGeometry.source_identity P c ht, eval₂_rename, Function.comp_def]
      using hx _ (List.mem_singleton_self _)
  · rintro ⟨x, hx⟩
    refine ⟨Formula.extend x, ?_⟩
    intro out hout
    obtain rfl := List.mem_singleton.mp hout
    simpa only [SourcePoint, BoundedFullGeometry.source_identity P c ht, eval_extend] using hx

theorem marked_correct (P : BoundedFullWriter.Readers) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    RealQuery.Satisfiable (BoundedFullWriter.start P c) (markedGates P c) ↔
      ∃ x : Fin (P.dim c + 4) → ℝ, MarkedPoint P c x := by
  have hb : ∀ out ∈ [BoundedFullWriter.output P c, BoundedFullWriter.markOutput P c],
      out < BoundedFullWriter.start P c + (BoundedFullWriter.program P c).length := by
    intro out hout
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
    rcases hout with rfl | rfl
    · exact BoundedFullWriter.output_lt P c
    · exact BoundedFullWriter.markOutput_lt P c
  rw [markedGates, show [Gate.zero (BoundedFullWriter.output P c), Gate.zero (BoundedFullWriter.markOutput P c)] =
    [BoundedFullWriter.output P c, BoundedFullWriter.markOutput P c].map Gate.zero from rfl,
    RealQuery.zero_constraints_iff _ _ _ (BoundedFullWriter.wellFormed P c) hb]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun i => x i.val, ?_, ?_⟩
    · simpa only [SourcePoint, BoundedFullGeometry.source_identity P c ht, eval₂_rename, Function.comp_def]
        using hx (BoundedFullWriter.output P c) (by simp)
    · simpa only [BoundedFullGeometry.mark_identity P c ht, eval₂_rename, Function.comp_def]
        using hx (BoundedFullWriter.markOutput P c) (by simp)
  · rintro ⟨x, hs, hm⟩
    refine ⟨Formula.extend x, ?_⟩
    intro out hout
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hout
    rcases hout with rfl | rfl
    · simpa only [SourcePoint, BoundedFullGeometry.source_identity P c ht, eval_extend] using hs
    · simpa only [BoundedFullGeometry.mark_identity P c ht, eval_extend] using hm

theorem source_evaluator {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ x, SourcePoint P c x)]) := by
  apply (RealQuery.feasible_generated (BoundedFullWriter.start_unary h) (source_encode_mem_FP h)).congr
  funext c
  rw [source_correct P c (ht c)]

theorem marked_evaluator {P : BoundedFullWriter.Readers} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ x, MarkedPoint P c x)]) := by
  apply (RealQuery.feasible_generated (BoundedFullWriter.start_unary h) (marked_encode_mem_FP h)).congr
  funext c
  rw [marked_correct P c (ht c)]

end LeanCanny.Encoding.BoundedRealQuery
