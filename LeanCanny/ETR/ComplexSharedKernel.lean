/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCriticalKernelSpecialization
public import LeanCanny.Computation.SpaceFunctionQuantifiers

/-! # Critical regularity of a shared circuit at constrained real inputs

The first `free + 1` inputs are differentiated; later inputs are frozen.
Every normalized kernel chart is checked. Native bounds refer to the shared
program and its encoded gates, so binary powers need no expression expansion.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.SharedKernel
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Inputs where
  start : List Bool → ℕ
  free : List Bool → ℕ
  program : List Bool → List Operation
  output : List Bool → ℕ
  direction : List Bool → ℕ → ℤ
  condition : List Bool → Formula

structure Inputs.PolyTime (F : Inputs) : Prop where
  start : UnaryFn F.start
  free : UnaryFn F.free
  length : UnaryFn (fun c => (F.program c).length)
  output : UnaryFn F.output
  gates : (fun c => encode (StraightLine.gates (F.start c) (F.program c))) ∈ FP
  direction : (fun q => (Term.const (-F.direction (pairFst q) (pairSnd q).length)).toData.toBits) ∈ FP
  condition : (fun c => (F.condition c).encode) ∈ FP

structure Inputs.Valid (F : Inputs) : Prop where
  wellFormed : ∀ c, StraightLine.WellFormed (F.start c) (F.program c)
  output_lt : ∀ c, F.output c < F.start c + (F.program c).length

def Inputs.comp (F : Inputs) (f : List Bool → List Bool) : Inputs :=
  ⟨F.start ∘ f, F.free ∘ f, F.program ∘ f, F.output ∘ f, F.direction ∘ f, F.condition ∘ f⟩

theorem Inputs.PolyTime.comp {F : Inputs} (h : F.PolyTime) {f : List Bool → List Bool} (hf : f ∈ FP) :
    (F.comp f).PolyTime := by
  refine ⟨h.start.comp hf, h.free.comp hf, h.length.comp hf, h.output.comp hf,
    mem_FP_comp (f := f) (g := fun c => encode (StraightLine.gates (F.start c) (F.program c))) hf h.gates,
    ?_, mem_FP_comp (f := f) (g := fun c => (F.condition c).encode) hf h.condition⟩
  exact mem_FP_of_eq (mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP) h.direction)
    (fun q => by simp only [Inputs.comp, Function.comp_apply, pairFst_pair, pairSnd_pair])

theorem Inputs.Valid.comp {F : Inputs} (h : F.Valid) (f : List Bool → List Bool) : (F.comp f).Valid :=
  ⟨fun c => h.wellFormed (f c), fun c => h.output_lt (f c)⟩

def dim (F : Inputs) (c : List Bool) : ℕ := F.free c + 1

noncomputable def polynomial (F : Inputs) (c : List Bool) : MvPolynomial ℕ ℤ :=
  Differential.symbolicRun (fun i => X i) (F.start c) (F.program c) (F.output c)

noncomputable def slice (F : Inputs) (c : List Bool) (x : ℕ → ℝ) :=
  CriticalKernel.realSlice (n := F.free c) (polynomial F c) x

noncomputable def rows (F : Inputs) (c : List Bool) (x : ℕ → ℝ) :=
  CriticalKernel.finiteRows (slice F c x) (fun i => (F.direction c i.val : ℝ))

def Regular (F : Inputs) (c : List Bool) : Prop :=
  ∀ x : ℕ → ℝ, (F.condition c).Holds x →
    (∀ i, (rows F c x i).eval (fun j => x j.val) = 0) →
      (fderiv ℝ (fun y => fun i => (rows F c x i).eval y) (fun j => x j.val)).IsInvertible

noncomputable def query (F : Inputs) (c : List Bool) (chart : ℕ) :=
  CriticalKernel.query (F.start c) (dim F c) (F.program c) (F.output c) (F.direction c) chart

noncomputable def chartFlag (F : Inputs) (chart : List Bool → ℕ) (c : List Bool) : List Bool :=
  [decide (RealQuery.Interleaved.InputSatisfiable (F.start c) (F.start c) (query F c (chart c)) (F.condition c))]

theorem dim_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (dim F) := h.free.add (UnaryFn.const 1)

theorem chart_evaluator {F : Inputs} (h : F.PolyTime) (hv : F.Valid)
    {chart : List Bool → ℕ} (hi : UnaryFn chart) : SpaceFunction (chartFlag F chart) :=
  CriticalKernel.constrained_evaluator h.start (dim_unary h) h.output hi h.length h.gates h.direction h.condition
    hv.wellFormed hv.output_lt

theorem chart_correct (F : Inputs) (hv : F.Valid) (c : List Bool) (i : ℕ) (hi : i < dim F c) :
    RealQuery.Interleaved.InputSatisfiable (F.start c) (F.start c) (query F c i) (F.condition c) ↔
      ∃ x : ℕ → ℝ, CriticalKernel.At (polynomial F c) (dim F c) (F.direction c) i (fun j => (x j : ℂ)) ∧
        (F.condition c).Holds x :=
  CriticalKernel.input_correct _ _ _ _ _ _ _ hi (hv.wellFormed c)
    (Differential.symbolicRun_realizes _ _ _ (hv.wellFormed c))
    (fun j hj => Differential.symbolicRun_preserves_before _ _ _ j hj) (hv.output_lt c) (F.condition c)

noncomputable def test (F : Inputs) (q : List Bool) : List Bool :=
  [decide (¬ RealQuery.Interleaved.InputSatisfiable (F.start (pairFst q)) (F.start (pairFst q))
    (query F (pairFst q) (pairSnd q).length) (F.condition (pairFst q)))]

theorem test_evaluator {F : Inputs} (h : F.PolyTime) (hv : F.Valid) : SpaceFunction (test F) := by
  have H := chart_evaluator (h.comp pairFst_mem_FP) (hv.comp pairFst) (UnaryFn.length pairSnd_mem_FP)
  have hn := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  apply (H.postcompose (fun z => [decide (z ≠ [true])]) hn).congr
  funext q
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, chartFlag, Inputs.comp, query, dim,
    decide_eq_true_eq, ne_eq, List.cons.injEq, and_true]

theorem scanned_iff_regular (F : Inputs) (hv : F.Valid) (c : List Bool) :
    (∀ i < dim F c, test F (pair c (List.replicate i true)) = [true]) ↔ Regular F c := by
  have ht (i : ℕ) (hi : i < dim F c) :
      test F (pair c (List.replicate i true)) = [true] ↔
        ¬ ∃ x : ℕ → ℝ, CriticalKernel.At (polynomial F c) (dim F c) (F.direction c) i (fun j => (x j : ℂ)) ∧
          (F.condition c).Holds x := by
    simp only [test, pairFst_pair, pairSnd_pair, List.length_replicate, List.cons.injEq, and_true,
      decide_eq_true_eq, chart_correct F hv c i hi]
  constructor
  · intro hs x hx hz
    by_contra hn
    obtain ⟨i, hi⟩ := (CriticalKernel.exists_chart_iff_singular (polynomial F c) (F.direction c) x).mpr ⟨hz, hn⟩
    exact (ht i.val i.isLt).mp (hs i.val i.isLt) ⟨x, hi, hx⟩
  · intro hr i hi
    apply (ht i hi).mpr
    rintro ⟨x, hAt, hx⟩
    have H := (CriticalKernel.exists_chart_iff_singular (n := F.free c) (polynomial F c) (F.direction c) x).mp
      ⟨⟨i, hi⟩, hAt⟩
    exact H.2 (hr x hx H.1)

theorem evaluator {F : Inputs} (h : F.PolyTime) (hv : F.Valid) :
    SpaceFunction (fun c => [decide (Regular F c)]) :=
  ((test_evaluator h hv).forall_unary (dim_unary h)).congr (funext fun c => by
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

end LeanCanny.ETR.ComplexCircuit.SharedKernel
