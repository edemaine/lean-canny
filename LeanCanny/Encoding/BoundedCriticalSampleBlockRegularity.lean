/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockConstraint
public import LeanCanny.ETR.ComplexBlockKernelGeometry
public import LeanCanny.ETR.FormulaView
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Native critical regularity over every actual parent sample

The parent constraint is generated in native space and passed to the native
block kernel validator as encoded input. Its formula replaces the input
family's condition. Acceptance is exactly regularity of every critical root
of every actual-parent slice of the original term, including zero extension.
No parent labels, singularity oracle, or finite-critical-set promise is used.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockRegularity
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR LeanCanny.ETR.ComplexCircuit
open BoundedFullWriter MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleBlockScaling.original

noncomputable def condition (P : Readers) (F : BlockKernel.Inputs) : List Bool → Formula :=
  BoundedCriticalSampleBlockConstraint.selected P (BlockKernel.dim F) (BlockKernel.inputs F) (BlockKernel.start F)

noncomputable def packet (F : BlockKernel.Inputs) : BlockKernel.Inputs :=
  { F.comp pairFst with condition := fun q => FormulaView.formula (pairSnd q) }

theorem packet_polyTime {F : BlockKernel.Inputs} (h : F.PolyTime) : (packet F).PolyTime := by
  have H := h.comp pairFst_mem_FP
  refine ⟨H.source, H.offset, H.free, H.direction, ?_⟩
  exact mem_FP_of_eq (mem_FP_comp pairSnd_mem_FP FormulaView.normalize_mem_FP)
    (fun q => FormulaView.normalize_eq_formula (pairSnd q))

noncomputable def prepare (P : Readers) (F : BlockKernel.Inputs) (c : List Bool) : List Bool :=
  pair c (condition P F c).encode

theorem prepare_evaluator {P : Readers} {F : BlockKernel.Inputs} (hP : P.PolyTime) (hF : F.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (prepare P F) :=
  (BoundedCriticalSampleBlockConstraint.selected_evaluator hP (BlockKernel.dim_unary hF)
    (BlockKernel.inputs_unary hF) (BlockKernel.start_unary hF) ht).withInput

noncomputable def originalRows (P : Readers) (F : BlockKernel.Inputs) (c : List Bool)
    (p : BoundedFullCriticalSamples.Samples P c) :=
  CriticalKernel.finiteRows
    (BoundedCriticalSampleBlockScaling.original (BlockKernel.term F c) p.val (F.offset c) (BlockKernel.dim F c))
    (fun i => (F.direction c i.val : ℝ))

def Good (P : Readers) (F : BlockKernel.Inputs) (c : List Bool) : Prop :=
  ∀ p : BoundedFullCriticalSamples.Samples P c, ∀ y : Fin (BlockKernel.dim F c) → ℝ,
    (∀ i, (originalRows P F c p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (originalRows P F c p i).eval z) y).IsInvertible

private def regularData (source : List Bool) (offset free : ℕ) (direction : ℕ → ℤ) (guard : Formula) : Prop :=
  BlockKernel.Regular ⟨fun _ => source, fun _ => offset, fun _ => free, fun _ => direction, fun _ => guard⟩ []

private theorem regularData_eq (F : BlockKernel.Inputs) (c : List Bool) :
    BlockKernel.Regular F c = regularData (F.source c) (F.offset c) (F.free c) (F.direction c) (F.condition c) := rfl

theorem native_regular_iff (P : Readers) (F : BlockKernel.Inputs) (c : List Bool) :
    BlockKernel.Regular (packet F) (prepare P F c) ↔
      ∀ x : ℕ → ℝ, (condition P F c).Holds x →
        (∀ i, (BlockKernel.rows F c x i).eval (fun j => x j.val) = 0) →
          (fderiv ℝ (fun z => fun i => (BlockKernel.rows F c x i).eval z) (fun j => x j.val)).IsInvertible := by
  change BlockKernel.Regular (packet F) (prepare P F c) ↔
    BlockKernel.Regular {F with condition := condition P F} c
  rw [regularData_eq, regularData_eq]
  simp only [packet, prepare, BlockKernel.Inputs.comp, Function.comp_apply,
    pairFst_pair, pairSnd_pair, FormulaView.formula_encode]

theorem regular_iff (P : Readers) (F : BlockKernel.Inputs) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    BlockKernel.Regular (packet F) (prepare P F c) ↔ Good P F c := by
  rw [native_regular_iff]
  constructor
  · intro h p y hz
    obtain ⟨x, hx, hy, hp⟩ := BoundedCriticalSampleBlockConstraint.selected_complete P
      (BlockKernel.dim F) (BlockKernel.inputs F) (BlockKernel.start F) c p y ht
        (by unfold BlockKernel.start; omega)
    have hs := BlockKernel.slice_eq_original_bounded F c x p.val
      (fun i hi => hp i (hi.trans_le (Term.arity_le_dataSize _)))
    have he : (fun i : Fin (F.free c + 1) => x i.val) = y := funext hy
    have hrows : BlockKernel.rows F c x = originalRows P F c p := by
      unfold BlockKernel.rows originalRows
      rw [hs]
    have H := h x hx
    rw [hrows, he] at H
    exact H hz
  · intro h x hx hz
    obtain ⟨p, hp⟩ := BoundedCriticalSampleBlockConstraint.selected_sound P
      (BlockKernel.dim F) (BlockKernel.inputs F) (BlockKernel.start F) c x ht hx
    have hs := BlockKernel.slice_eq_original_bounded F c x p.val
      (fun i hi => hp i (hi.trans_le (Term.arity_le_dataSize _)))
    have hrows : BlockKernel.rows F c x = originalRows P F c p := by
      unfold BlockKernel.rows originalRows
      rw [hs]
    have H := h p (fun i : Fin (BlockKernel.dim F c) => x i.val)
    rw [← hrows] at H
    exact H hz

theorem evaluator {P : Readers} {F : BlockKernel.Inputs} (hP : P.PolyTime) (hF : F.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (Good P F c)]) := by
  have E := (prepare_evaluator hP hF ht).chain (BlockKernel.evaluator (packet_polyTime hF))
  apply E.congr
  funext c
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, regular_iff P F c (ht c)]

def language (P : Readers) (F : BlockKernel.Inputs) : Language := {c | Good P F c}

theorem decider {P : Readers} {F : BlockKernel.Inputs} (hP : P.PolyTime) (hF : F.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P F) :=
  (evaluator hP hF ht).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
    (fun c => by simp only [language, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq])

theorem mem_PSPACE {P : Readers} {F : BlockKernel.Inputs} (hP : P.PolyTime) (hF : F.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : language P F ∈ PSPACE := (decider hP hF ht).mem_PSPACE

end LeanCanny.Encoding.BoundedCriticalSampleBlockRegularity
