/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexFrozenParentConstraint
public import LeanCanny.Encoding.BoundedCriticalSampleQuery

/-! # Generated constraints for blocks over actual parent samples

The selected parent circuit is serialized in native space. Its real-input
guards and links to the frozen block coordinates are constructed, rather
than supplied as an oracle. Every satisfying assignment has an actual parent;
every actual parent and arbitrary free tuple admit independent witnesses.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockConstraint
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation BoundedFullWriter
open FrozenParentConstraint RealQuery.Interleaved
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def formula (P : Readers) (record : List Bool → List Bool) (free inputs base : List Bool → ℕ)
    (c : List Bool) : Formula :=
  FrozenParentConstraint.formula (P.dim c + 4) (BoundedCriticalSampleQuery.frame P c)
    (free c) (inputs c) (base c) (BoundedCriticalSampleQuery.query P record c)

theorem formula_FP {P : Readers} {record : List Bool → List Bool} (h : P.PolyTime) (hr : record ∈ FP)
    {free inputs base : List Bool → ℕ} (hd : UnaryFn free) (hi : UnaryFn inputs) (hb : UnaryFn base) :
    (fun c => (formula P record free inputs base c).encode) ∈ FP :=
  FrozenParentConstraint.formula_FP (h.dim.add (UnaryFn.const 4)) (BoundedCriticalSampleQuery.frame_unary h)
    hd hi hb (BoundedCriticalSampleQuery.query_encode_mem_FP h hr)

noncomputable def selected (P : Readers) (free inputs base : List Bool → ℕ) : List Bool → Formula :=
  formula P (BoundedFullDirectionChoice.record P) free inputs base

theorem selected_evaluator {P : Readers} (h : P.PolyTime)
    {free inputs base : List Bool → ℕ} (hd : UnaryFn free) (hi : UnaryFn inputs) (hb : UnaryFn base)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => (selected P free inputs base c).encode) := by
  have E := BoundedCriticalSampleQuery.selected_encode_evaluator h ht
  have hn := (h.dim.add (UnaryFn.const 4)).comp pairFst_mem_FP
  have hf := (BoundedCriticalSampleQuery.frame_unary h).comp pairFst_mem_FP
  have H := E.withInput.postcompose
    (fun q => FrozenParentConstraint.bits (P.dim (pairFst q) + 4) (BoundedCriticalSampleQuery.frame P (pairFst q))
      (free (pairFst q)) (inputs (pairFst q)) (base (pairFst q)) (pairSnd q))
    (FrozenParentConstraint.bits_FP hn hf (hd.comp pairFst_mem_FP) (hi.comp pairFst_mem_FP)
      (hb.comp pairFst_mem_FP) pairSnd_mem_FP)
  apply H.congr
  funext c
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, FrozenParentConstraint.bits_encode]
  rfl

theorem selected_sound (P : Readers) (free inputs base : List Bool → ℕ) (c : List Bool) (x : ℕ → ℝ)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c)
    (hx : (selected P free inputs base c).Holds x) :
    ∃ p : BoundedFullCriticalSamples.Samples P c,
      ∀ i < inputs c, x (free c + i) = Formula.extend p.val i := by
  obtain ⟨hg, hr, hl⟩ := (FrozenParentConstraint.holds_iff _ _ _ _ _ _ _).mp hx
  let y := FrozenParentConstraint.point (P.dim c + 4) (base c) x
  have hrealizes : PortRealizes (P.dim c + 4) (BoundedCriticalSampleQuery.frame P c) id
      (BoundedCriticalSampleQuery.query P (BoundedFullDirectionChoice.record P) c) (Formula.extend y) := by
    refine ⟨parentEnv (base c) x, hg, hr, ?_⟩
    intro i hi
    apply Complex.ext
    · simp only [parentEnv, complexEnv, Formula.extend, hi, dite_true, y, point, id_eq, Complex.ofReal_re]
    · simp only [Complex.ofReal_im]
      apply hr i
      unfold BoundedCriticalSampleQuery.frame CriticalKernel.zeroWire
      omega
  have hc := (BoundedCriticalSampleQuery.realizes_correct P (BoundedFullDirectionChoice.record P) c
    (Formula.extend y) ht).mp hrealizes
  have he : (fun i : Fin (P.dim c + 4) => Formula.extend y i.val) = y := by
    funext i
    simp only [Formula.extend, i.isLt, dite_true, Fin.eta]
  have hy := (BoundedCriticalSampleQuery.selected_condition P c (Formula.extend y)).mp hc
  rw [he] at hy
  exact ⟨⟨y, hy⟩, hl⟩

theorem selected_complete (P : Readers) (free inputs base : List Bool → ℕ) (c : List Bool)
    (p : BoundedFullCriticalSamples.Samples P c) (y : Fin (free c) → ℝ)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) (hb : free c + inputs c ≤ base c) :
    ∃ x : ℕ → ℝ, (selected P free inputs base c).Holds x ∧
      (∀ i : Fin (free c), x i.val = y i) ∧ ∀ i < inputs c, x (free c + i) = Formula.extend p.val i := by
  have he : (fun i : Fin (P.dim c + 4) => Formula.extend p.val i.val) = p.val := by
    funext i
    simp only [Formula.extend, i.isLt, dite_true, Fin.eta]
  have hc : BoundedCriticalSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (Formula.extend p.val) := by
    rw [BoundedCriticalSampleQuery.selected_condition, he]
    exact p.property
  obtain ⟨env, hg, hr, hp⟩ := (BoundedCriticalSampleQuery.realizes_correct P
    (BoundedFullDirectionChoice.record P) c (Formula.extend p.val) ht).mpr hc
  have hparent : ∀ i : Fin (P.dim c + 4), (env i.val).re = p.val i := by
    intro i
    have H := congrArg Complex.re (hp i.val i.isLt)
    simpa only [id_eq, Complex.ofReal_re, Formula.extend, i.isLt, dite_true, Fin.eta] using H
  refine ⟨FrozenParentConstraint.assignment (base c) y p.val env, ?_, ?_, ?_⟩
  · exact FrozenParentConstraint.assignment_holds (base c) (BoundedCriticalSampleQuery.frame P c) (inputs c)
      y p.val env (BoundedCriticalSampleQuery.query P (BoundedFullDirectionChoice.record P) c) hb hg hr hparent
  · exact FrozenParentConstraint.assignment_free (base c) y p.val env
  · exact FrozenParentConstraint.assignment_frozen (base c) (inputs c) y p.val env hb

end LeanCanny.Encoding.BoundedCriticalSampleBlockConstraint
