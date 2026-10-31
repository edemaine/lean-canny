/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceChildSteps

/-! # Polynomial frame and vertex bounds in the original source size

A native reader for the single trace family has one polynomial bound over
all valid histories. This includes complete sample widths; successive child
choices do not introduce a new polynomial degree at each recursion depth.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

theorem frame_length_polynomial {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    (initial : List Bool → ℕ) :
    ∃ p : Polynomial ℕ, ∀ u trace, Valid P initial (frame u trace) → (frame u trace).length ≤ p.eval u.length := by
  obtain ⟨s, hs⟩ := output_length_poly_of_mem_FP hP.dim.mem_FP
  refine ⟨2 * Polynomial.X + 5 + s, ?_⟩
  intro u trace hv
  have H := frame_length_bound P initial u trace hv
  have HD : P.dim u ≤ s.eval u.length := by simpa only [List.length_replicate] using hs u
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  omega

theorem unary_frame_polynomial {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    (initial : List Bool → ℕ) {f : List Bool → ℕ} (hf : UnaryFn f) :
    ∃ p : Polynomial ℕ, ∀ u trace, Valid P initial (frame u trace) → f (frame u trace) ≤ p.eval u.length := by
  obtain ⟨r, hr⟩ := frame_length_polynomial hP initial
  obtain ⟨s, hs⟩ := output_length_poly_of_mem_FP hf.mem_FP
  refine ⟨s.comp r, ?_⟩
  intro u trace hv
  have H : f (frame u trace) ≤ s.eval (frame u trace).length := by
    simpa only [List.length_replicate] using hs (frame u trace)
  simpa only [Polynomial.eval_comp] using H.trans (s.eval_mono (hr u trace hv))

theorem width_frame_polynomial {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    ∃ p : Polynomial ℕ, ∀ u trace, Valid P (seedCoordinate d old) (frame u trace) →
      FlatAffineCompleteVertices.width (inputs P d old level) (cone P d old level) (frame u trace) ≤ p.eval u.length :=
  unary_frame_polynomial hP (seedCoordinate d old)
    (FlatAffineCompleteVertices.width_unary (access hP hd ho hl hA) (cone P d old level))

theorem vertex_frame_polynomial {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    ∃ p : Polynomial ℕ, ∀ u trace w, Valid P (seedCoordinate d old) (frame u trace) →
      FlatAffineCompleteVertices.Valid (inputs P d old level) (cone P d old level) (frame u trace) w →
        w.length ≤ p.eval u.length := by
  obtain ⟨p, hp⟩ := width_frame_polynomial hP hd ho hl hA
  refine ⟨p, ?_⟩
  intro u trace w hv hw
  rw [FlatAffineCompleteVertices.word_length (inputs P d old level) (cone P d old level) (frame u trace) w hw]
  exact hp u trace hv

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
