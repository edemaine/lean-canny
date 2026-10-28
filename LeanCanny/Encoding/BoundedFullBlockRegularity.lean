/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullBlockKernel
public import LeanCanny.Encoding.BoundedCriticalSampleBlockConstraint
public import LeanCanny.ETR.FormulaView
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Native regularity of full-source blocks over actual parent samples

Generated parent constraints bind the frozen inputs of the constructed
shared regular-source program. Acceptance is exactly regularity of every
critical root over every actual parent. The generated condition replaces
the input condition. Neither source-term expansion nor parent labels are used.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullBlockRegularity
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR LeanCanny.ETR.ComplexCircuit
open BoundedFullWriter MvPolynomial
open BoundedFullBlockKernel (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair pairFst pairSnd BoundedFullBlockKernel.slice

noncomputable def condition (P : Readers) (F : Inputs) : List Bool → Formula :=
  BoundedCriticalSampleBlockConstraint.selected P (BoundedFullBlockKernel.dim F)
    (BoundedFullWriter.start F.source) (BoundedFullBlockKernel.start F)

noncomputable def packet (F : Inputs) : SharedKernel.Inputs :=
  { (BoundedFullBlockKernel.native F).comp pairFst with condition := fun q => FormulaView.formula (pairSnd q) }

theorem packet_polyTime {F : Inputs} (h : F.PolyTime) : (packet F).PolyTime := by
  have H := (BoundedFullBlockKernel.native_polyTime h).comp pairFst_mem_FP
  refine ⟨H.start, H.free, H.length, H.output, H.gates, H.direction, ?_⟩
  exact mem_FP_of_eq (mem_FP_comp pairSnd_mem_FP FormulaView.normalize_mem_FP)
    (fun q => FormulaView.normalize_eq_formula (pairSnd q))

theorem packet_valid (F : Inputs) : (packet F).Valid :=
  ⟨fun q => (BoundedFullBlockKernel.native_valid F).wellFormed (pairFst q),
    fun q => (BoundedFullBlockKernel.native_valid F).output_lt (pairFst q)⟩

noncomputable def prepare (P : Readers) (F : Inputs) (c : List Bool) : List Bool :=
  pair c (condition P F c).encode

theorem prepare_evaluator {P : Readers} {F : Inputs} (hP : P.PolyTime) (hF : F.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (prepare P F) :=
  (BoundedCriticalSampleBlockConstraint.selected_evaluator hP (BoundedFullBlockKernel.dim_unary hF)
    (BoundedFullWriter.start_unary hF.source) (BoundedFullBlockKernel.start_unary hF) ht).withInput

noncomputable def originalRows (P : Readers) (F : Inputs) (c : List Bool)
    (p : BoundedFullCriticalSamples.Samples P c) :=
  CriticalKernel.finiteRows (BoundedFullBlockKernel.slice F c (Formula.extend p.val))
    (fun i => (F.direction c i.val : ℝ))

def Good (P : Readers) (F : Inputs) (c : List Bool) : Prop :=
  ∀ p : BoundedFullCriticalSamples.Samples P c, ∀ y : Fin (BoundedFullBlockKernel.dim F c) → ℝ,
    (∀ i, (originalRows P F c p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (originalRows P F c p i).eval z) y).IsInvertible

private def regularData (start free : ℕ) (program : List Operation) (output : ℕ)
    (direction : ℕ → ℤ) (guard : Formula) : Prop :=
  SharedKernel.Regular ⟨fun _ => start, fun _ => free, fun _ => program, fun _ => output,
    fun _ => direction, fun _ => guard⟩ []

private theorem regularData_eq (F : SharedKernel.Inputs) (c : List Bool) :
    SharedKernel.Regular F c = regularData (F.start c) (F.free c) (F.program c) (F.output c)
      (F.direction c) (F.condition c) := rfl

theorem native_regular_iff (P : Readers) (F : Inputs) (c : List Bool) :
    SharedKernel.Regular (packet F) (prepare P F c) ↔
      ∀ x : ℕ → ℝ, (condition P F c).Holds x →
        (∀ i, (SharedKernel.rows (BoundedFullBlockKernel.native F) c x i).eval (fun j => x j.val) = 0) →
          (fderiv ℝ (fun z => fun i => (SharedKernel.rows (BoundedFullBlockKernel.native F) c x i).eval z)
            (fun j => x j.val)).IsInvertible := by
  change SharedKernel.Regular (packet F) (prepare P F c) ↔
    SharedKernel.Regular {BoundedFullBlockKernel.native F with condition := condition P F} c
  rw [regularData_eq, regularData_eq]
  simp only [packet, prepare, SharedKernel.Inputs.comp, Function.comp_apply, pairFst_pair, pairSnd_pair,
    FormulaView.formula_encode]

theorem regular_iff (P : Readers) (F : Inputs) (c : List Bool)
    (hP : (TermView.term (P.source c)).arity ≤ P.dim c)
    (hF : (TermView.term (F.source.source c)).arity ≤ F.source.dim c) :
    SharedKernel.Regular (packet F) (prepare P F c) ↔ Good P F c := by
  rw [native_regular_iff]
  constructor
  · intro h p y hz
    obtain ⟨x, hx, hy, hp⟩ := BoundedCriticalSampleBlockConstraint.selected_complete P
      (BoundedFullBlockKernel.dim F) (BoundedFullWriter.start F.source) (BoundedFullBlockKernel.start F)
      c p y hP (by unfold BoundedFullBlockKernel.start; omega)
    have he : (fun i : Fin (F.free c + 1) => x i.val) = y := funext hy
    have hrows : SharedKernel.rows (BoundedFullBlockKernel.native F) c x = originalRows P F c p := by
      unfold SharedKernel.rows originalRows
      rw [BoundedFullBlockKernel.native_slice_parent F c x p.val hF hp]
      rfl
    have H := h x hx
    rw [hrows] at H
    change (∀ i : Fin (F.free c + 1), (originalRows P F c p i).eval (fun j : Fin (F.free c + 1) => x j.val) = 0) →
      (fderiv ℝ (fun z : Fin (F.free c + 1) → ℝ => fun i : Fin (F.free c + 1) =>
        (originalRows P F c p i).eval z) (fun j : Fin (F.free c + 1) => x j.val)).IsInvertible at H
    rw [he] at H
    exact H hz
  · intro h x hx hz
    obtain ⟨p, hp⟩ := BoundedCriticalSampleBlockConstraint.selected_sound P
      (BoundedFullBlockKernel.dim F) (BoundedFullWriter.start F.source) (BoundedFullBlockKernel.start F) c x hP hx
    have hrows : SharedKernel.rows (BoundedFullBlockKernel.native F) c x = originalRows P F c p := by
      unfold SharedKernel.rows originalRows
      rw [BoundedFullBlockKernel.native_slice_parent F c x p.val hF hp]
      rfl
    have H := h p (fun i : Fin (BoundedFullBlockKernel.dim F c) => x i.val)
    rw [← hrows] at H
    exact H hz

theorem evaluator {P : Readers} {F : Inputs} (hP : P.PolyTime) (hF : F.PolyTime)
    (htP : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (htF : ∀ c, (TermView.term (F.source.source c)).arity ≤ F.source.dim c) :
    SpaceFunction (fun c => [decide (Good P F c)]) := by
  have E := (prepare_evaluator hP hF htP).chain (SharedKernel.evaluator (packet_polyTime hF) (packet_valid F))
  apply E.congr
  funext c
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, regular_iff P F c (htP c) (htF c)]

def language (P : Readers) (F : Inputs) : Language := {c | Good P F c}

theorem decider {P : Readers} {F : Inputs} (hP : P.PolyTime) (hF : F.PolyTime)
    (htP : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (htF : ∀ c, (TermView.term (F.source.source c)).arity ≤ F.source.dim c) : SpaceDecider (language P F) :=
  (evaluator hP hF htP htF).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
    (fun c => by simp only [language, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq])

theorem mem_PSPACE {P : Readers} {F : Inputs} (hP : P.PolyTime) (hF : F.PolyTime)
    (htP : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (htF : ∀ c, (TermView.term (F.source.source c)).arity ≤ F.source.dim c) : language P F ∈ PSPACE :=
  (decider hP hF htP htF).mem_PSPACE

end LeanCanny.Encoding.BoundedFullBlockRegularity
