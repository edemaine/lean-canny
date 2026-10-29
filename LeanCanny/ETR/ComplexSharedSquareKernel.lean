/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexSquareKernelEncoding
public import LeanCanny.ETR.ComplexSquareKernelRegular
public import LeanCanny.Computation.SpaceFunctionQuantifiers

/-! # Native regularity tests for constrained square systems

Every normalized kernel chart is checked over arbitrary complex child
coordinates. A real input prefix and additional polynomial guards select
parent data at the same assignment. The test detects every bad root without
a root enumeration, isolation premise, or regular-root annihilator.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.SharedSquareKernel
open LeanCanny.Computation LeanCanny.Encoding.Brackets MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Inputs where
  start : List Bool → ℕ
  count : List Bool → ℕ
  offset : List Bool → ℕ
  program : List Bool → List Operation
  outputs : List Bool → ℕ → ℕ
  guardCount : List Bool → ℕ
  guardOutputs : List Bool → ℕ → ℕ
  realInputs : List Bool → ℕ
  condition : List Bool → Formula

structure Inputs.PolyTime (F : Inputs) : Prop where
  start : UnaryFn F.start
  count : UnaryFn F.count
  offset : UnaryFn F.offset
  length : UnaryFn (fun c => (F.program c).length)
  gates : (fun c => encode (StraightLine.gates (F.start c) (F.program c))) ∈ FP
  outputs : UnaryFn (fun q => F.outputs (pairFst q) (pairSnd q).length)
  guardCount : UnaryFn F.guardCount
  guardOutputs : UnaryFn (fun q => F.guardOutputs (pairFst q) (pairSnd q).length)
  realInputs : UnaryFn F.realInputs
  condition : (fun c => (F.condition c).encode) ∈ FP

structure Inputs.Valid (F : Inputs) : Prop where
  wellFormed : ∀ c, StraightLine.WellFormed (F.start c) (F.program c)
  block : ∀ c, F.offset c + F.count c ≤ F.start c
  outputs : ∀ c j, j < F.count c → F.outputs c j < F.start c + (F.program c).length
  guardOutputs : ∀ c j, j < F.guardCount c → F.guardOutputs c j < F.start c + (F.program c).length
  realInputs : ∀ c, F.realInputs c ≤ F.start c
  condition : ∀ c, (F.condition c).arity ≤ F.start c

def Inputs.comp (F : Inputs) (f : List Bool → List Bool) : Inputs :=
  ⟨F.start ∘ f, F.count ∘ f, F.offset ∘ f, F.program ∘ f, F.outputs ∘ f,
    F.guardCount ∘ f, F.guardOutputs ∘ f, F.realInputs ∘ f, F.condition ∘ f⟩

theorem Inputs.PolyTime.comp {F : Inputs} (h : F.PolyTime) {f : List Bool → List Bool} (hf : f ∈ FP) :
    (F.comp f).PolyTime := by
  have hp := mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP
  refine ⟨h.start.comp hf, h.count.comp hf, h.offset.comp hf, h.length.comp hf,
    mem_FP_comp hf h.gates, ?_, h.guardCount.comp hf, ?_, h.realInputs.comp hf, mem_FP_comp hf h.condition⟩
  · exact (h.outputs.comp hp).of_eq (fun _ => by simp only [Inputs.comp, Function.comp_apply, pairFst_pair, pairSnd_pair])
  · exact (h.guardOutputs.comp hp).of_eq (fun _ => by simp only [Inputs.comp, Function.comp_apply, pairFst_pair, pairSnd_pair])

theorem Inputs.Valid.comp {F : Inputs} (h : F.Valid) (f : List Bool → List Bool) : (F.comp f).Valid :=
  ⟨fun c => h.wellFormed (f c), fun c => h.block (f c), fun c => h.outputs (f c),
    fun c => h.guardOutputs (f c), fun c => h.realInputs (f c), fun c => h.condition (f c)⟩

noncomputable def wire (F : Inputs) (c : List Bool) : ℕ → MvPolynomial ℕ ℤ :=
  Differential.symbolicRun (fun i => X i) (F.start c) (F.program c)

def Regular (F : Inputs) (c : List Bool) : Prop :=
  SquareKernel.Regular (wire F c) (F.count c) (F.offset c) (F.outputs c) (F.guardCount c)
    (F.guardOutputs c) (F.realInputs c) (F.condition c)

def query (F : Inputs) (c : List Bool) (chart : ℕ) : List Gate :=
  SquareKernel.query (F.start c) (F.count c) (F.offset c) (F.program c) (F.outputs c)
    (F.guardCount c) (F.guardOutputs c) chart

noncomputable def chartFlag (F : Inputs) (chart : List Bool → ℕ) (c : List Bool) : List Bool :=
  [decide (RealQuery.WithConstraints (F.realInputs c) (query F c (chart c)) (F.condition c))]

theorem chart_evaluator {F : Inputs} (h : F.PolyTime) {chart : List Bool → ℕ} (hi : UnaryFn chart) :
    SpaceFunction (chartFlag F chart) :=
  RealQuery.constraint_evaluator h.realInputs
    (SquareKernel.query_encode_mem_FP h.start h.count h.offset h.guardCount hi h.length h.gates h.outputs h.guardOutputs)
    h.condition

theorem chart_correct (F : Inputs) (hv : F.Valid) (c : List Bool) (i : ℕ) (hi : i < F.count c) :
    RealQuery.WithConstraints (F.realInputs c) (query F c i) (F.condition c) ↔
      ∃ x u : ℕ → ℂ, SquareKernel.At (wire F c) (F.count c) (F.offset c) (F.outputs c)
        (F.guardCount c) (F.guardOutputs c) i x u ∧
        (∀ j < F.realInputs c, (x j).im = 0) ∧ (F.condition c).Holds (fun j => (x j).re) :=
  SquareKernel.query_withConstraints (wire F c) (F.start c) (F.count c) (F.offset c) (F.program c)
    (F.outputs c) (F.guardCount c) (F.guardOutputs c) i hi (hv.wellFormed c)
    (Differential.symbolicRun_realizes _ _ _ (hv.wellFormed c))
    (fun j hj => Differential.symbolicRun_preserves_before _ _ _ j hj)
    (hv.outputs c) (hv.guardOutputs c) (F.realInputs c) (hv.realInputs c) (F.condition c) (hv.condition c)

noncomputable def test (F : Inputs) (q : List Bool) : List Bool :=
  [decide (¬ RealQuery.WithConstraints (F.realInputs (pairFst q)) (query F (pairFst q) (pairSnd q).length)
    (F.condition (pairFst q)))]

theorem test_evaluator {F : Inputs} (h : F.PolyTime) : SpaceFunction (test F) := by
  have H := chart_evaluator (h.comp pairFst_mem_FP) (UnaryFn.length pairSnd_mem_FP)
  have hn := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  apply (H.postcompose (fun z => [decide (z ≠ [true])]) hn).congr
  funext q
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, chartFlag, Inputs.comp, query,
    decide_eq_true_eq, ne_eq, List.cons.injEq, and_true]

theorem scanned_iff_regular (F : Inputs) (hv : F.Valid) (c : List Bool) :
    (∀ i < F.count c, test F (pair c (List.replicate i true)) = [true]) ↔ Regular F c := by
  have ht (i : ℕ) (hi : i < F.count c) : test F (pair c (List.replicate i true)) = [true] ↔
      ¬ ∃ x u : ℕ → ℂ, SquareKernel.At (wire F c) (F.count c) (F.offset c) (F.outputs c)
        (F.guardCount c) (F.guardOutputs c) i x u ∧
        (∀ j < F.realInputs c, (x j).im = 0) ∧ (F.condition c).Holds (fun j => (x j).re) := by
    simp only [test, pairFst_pair, pairSnd_pair, List.length_replicate, List.cons.injEq, and_true,
      decide_eq_true_eq, chart_correct F hv c i hi]
  change _ ↔ SquareKernel.Regular _ _ _ _ _ _ _ _
  rw [SquareKernel.regular_iff_no_charts]
  constructor
  · intro h i
    exact (ht i.val i.isLt).mp (h i.val i.isLt)
  · intro h i hi
    exact (ht i hi).mpr (h ⟨i, hi⟩)

theorem evaluator {F : Inputs} (h : F.PolyTime) (hv : F.Valid) :
    SpaceFunction (fun c => [decide (Regular F c)]) :=
  ((test_evaluator h).forall_unary h.count).congr (funext fun c => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, scanned_iff_regular F hv])

def language (F : Inputs) : Language := {c | Regular F c}

theorem decider {F : Inputs} (h : F.PolyTime) (hv : F.Valid) : SpaceDecider (language F) :=
  (evaluator h hv).decider (fun z => decide (z = [true]))
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
    (fun c => by simp only [language, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq])

theorem mem_PSPACE {F : Inputs} (h : F.PolyTime) (hv : F.Valid) : language F ∈ PSPACE :=
  (decider h hv).mem_PSPACE

end LeanCanny.ETR.ComplexCircuit.SharedSquareKernel
