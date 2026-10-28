/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitBlock
public import LeanCanny.ETR.ComplexCriticalKernelSpecialization
public import LeanCanny.Computation.SpaceFunctionQuantifiers

/-! # Native regularity validation for original-term coordinate blocks

The source term and the actual free block generate the shared derivative
circuits. A real formula filters the free and frozen inputs and may use
independent existential witnesses. All normalized kernel charts are checked.
The validator covers every critical root, without a finite-root promise or
any supplied coefficient, derivative, or singularity-testing procedure.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.BlockKernel
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Inputs where
  source : List Bool → List Bool
  offset : List Bool → ℕ
  free : List Bool → ℕ
  direction : List Bool → ℕ → ℤ
  condition : List Bool → Formula

structure Inputs.PolyTime (F : Inputs) : Prop where
  source : F.source ∈ FP
  offset : BinaryFn F.offset
  free : UnaryFn F.free
  direction : (fun q => (Term.const (-F.direction (pairFst q) (pairSnd q).length)).toData.toBits) ∈ FP
  condition : (fun c => (F.condition c).encode) ∈ FP

def Inputs.comp (F : Inputs) (f : List Bool → List Bool) : Inputs :=
  ⟨F.source ∘ f, F.offset ∘ f, F.free ∘ f, F.direction ∘ f, F.condition ∘ f⟩

theorem Inputs.PolyTime.comp {F : Inputs} (h : F.PolyTime) {f : List Bool → List Bool} (hf : f ∈ FP) :
    (F.comp f).PolyTime := by
  refine ⟨?_, h.offset.comp hf, h.free.comp hf, ?_, ?_⟩
  · exact mem_FP_comp (f := f) (g := F.source) hf h.source
  · exact mem_FP_of_eq (mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP) h.direction)
      (fun q => by simp only [Inputs.comp, Function.comp_apply, pairFst_pair, pairSnd_pair])
  · exact mem_FP_comp (f := f) (g := fun c => (F.condition c).encode) hf h.condition

noncomputable def term (F : Inputs) (c : List Bool) := TermView.term (F.source c)
def dim (F : Inputs) (c : List Bool) := F.free c + 1
noncomputable def inputs (F : Inputs) (c : List Bool) := (term F c).toData.size
noncomputable def start (F : Inputs) (c : List Bool) := inputs F c + dim F c
noncomputable def ops (F : Inputs) (c : List Bool) :=
  CircuitBlock.program (inputs F c) (F.offset c) (dim F c) (start F c)
    (Source.program (inputs F c) (term F c))
noncomputable def output (F : Inputs) (c : List Bool) :=
  CircuitBlock.output (inputs F c) (F.offset c) (dim F c) (start F c)
    (Source.output (inputs F c) (term F c))
noncomputable def polynomial (F : Inputs) (c : List Bool) :=
  CircuitBlock.substitution (F.offset c) (dim F c) (term F c).toPolynomial
noncomputable def slice (F : Inputs) (c : List Bool) (x : ℕ → ℝ) :=
  CriticalKernel.realSlice (n := F.free c) (polynomial F c) x
noncomputable def rows (F : Inputs) (c : List Bool) (x : ℕ → ℝ) :=
  CriticalKernel.finiteRows (slice F c x) (fun i => (F.direction c i.val : ℝ))

def Regular (F : Inputs) (c : List Bool) : Prop :=
  ∀ x : ℕ → ℝ, (F.condition c).Holds x →
    (∀ j, (rows F c x j).eval (fun i => x i.val) = 0) →
      (fderiv ℝ (fun y => fun j => (rows F c x j).eval y) (fun i => x i.val)).IsInvertible

noncomputable def query (F : Inputs) (c : List Bool) (chart : ℕ) :=
  CriticalKernel.query (start F c) (dim F c) (ops F c) (output F c) (F.direction c) chart

noncomputable def chartFlag (F : Inputs) (chart : List Bool → ℕ) (c : List Bool) : List Bool :=
  [decide (RealQuery.Interleaved.InputSatisfiable (start F c) (start F c) (query F c (chart c)) (F.condition c))]

theorem inputs_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (inputs F) :=
  (UnaryFn.length (mem_FP_comp h.source TermView.normalize_mem_FP)).of_eq
    (fun c => by simp only [Function.comp_apply, TermView.normalize_eq_term, Data.length_toBits]; rfl)
theorem dim_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (dim F) := h.free.add (UnaryFn.const 1)
theorem start_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (start F) := (inputs_unary h).add (dim_unary h)

theorem source_length_unary {F : Inputs} (h : F.PolyTime) :
    UnaryFn (fun c => (Source.program (inputs F c) (term F c)).length) := by
  have hn := Source.Machine.nextIndex_unary.comp h.source
  exact (hn.sub (inputs_unary h)).of_eq (fun c => by
    simp only [Source.Machine.nextIndex_eq, Source.program_length, inputs, term, Nat.add_sub_cancel_left])

theorem length_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (fun c => (ops F c).length) :=
  (source_length_unary h).of_eq (fun c =>
    (CircuitBlock.program_length (inputs F c) (F.offset c) (dim F c) (start F c) _).symm)

theorem output_unary {F : Inputs} (h : F.PolyTime) : UnaryFn (output F) := by
  have ho := (Source.Machine.outputIndex_unary.comp h.source).of_eq
    (fun c => Source.Machine.outputIndex_eq (F.source c))
  exact CircuitBlock.output_unary (inputs_unary h) h.offset (dim_unary h) (start_unary h) ho

theorem encode_mem_FP {F : Inputs} (h : F.PolyTime) :
    (fun c => encode (StraightLine.gates (start F c) (ops F c))) ∈ FP :=
  CircuitBlock.encode_mem_FP (inputs_unary h) h.offset (dim_unary h) (start_unary h)
    (mem_FP_of_eq (Source.encoded_gates_mem_FP h.source) (fun c => by rw [Source.gates_eq]; rfl))

theorem wellFormed (F : Inputs) (c : List Bool) : StraightLine.WellFormed (start F c) (ops F c) :=
  CircuitBlock.wellFormed _ _ _ _ _ (Source.wellFormed _ _ (Term.arity_le_dataSize _)) le_rfl

theorem output_lt (F : Inputs) (c : List Bool) : output F c < start F c + (ops F c).length :=
  CircuitBlock.output_lt _ _ _ _ _ _ le_rfl (by
    simpa only [Source.program_length] using Source.output_lt (inputs F c) (term F c) (Term.arity_le_dataSize _))

theorem symbolic_output (F : Inputs) (c : List Bool) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (start F c) (ops F c) (output F c) = polynomial F c := by
  rw [ops, output, CircuitBlock.symbolic_output (inputs F c) (F.offset c) (dim F c) (start F c)
    (Source.output (inputs F c) (term F c)) (Source.program (inputs F c) (term F c))
    (Source.wellFormed _ _ (Term.arity_le_dataSize _)) le_rfl (by
      simpa only [Source.program_length] using Source.output_lt (inputs F c) (term F c) (Term.arity_le_dataSize _)),
    Source.symbolicRun_output (inputs F c) (term F c) (Term.arity_le_dataSize _)]
  rfl

theorem chart_evaluator {F : Inputs} (h : F.PolyTime) {chart : List Bool → ℕ} (hi : UnaryFn chart) :
    SpaceFunction (chartFlag F chart) :=
  CriticalKernel.constrained_evaluator (start_unary h) (dim_unary h) (output_unary h) hi (length_unary h)
    (encode_mem_FP h) h.direction h.condition (wellFormed F) (output_lt F)

theorem chart_correct (F : Inputs) (c : List Bool) (i : ℕ) (hi : i < dim F c) :
    RealQuery.Interleaved.InputSatisfiable (start F c) (start F c) (query F c i) (F.condition c) ↔
      ∃ x : ℕ → ℝ, CriticalKernel.At (polynomial F c) (dim F c) (F.direction c) i (fun j => (x j : ℂ)) ∧
        (F.condition c).Holds x := by
  let W := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (start F c) (ops F c)
  have H := CriticalKernel.input_correct W (start F c) (dim F c) (ops F c) (output F c) (F.direction c) i hi
    (wellFormed F c) (Differential.symbolicRun_realizes _ _ _ (wellFormed F c))
    (fun j hj => Differential.symbolicRun_preserves_before _ _ _ j hj) (output_lt F c) (F.condition c)
  simpa only [W, symbolic_output, query] using H

noncomputable def test (F : Inputs) (q : List Bool) : List Bool :=
  [decide (¬ RealQuery.Interleaved.InputSatisfiable (start F (pairFst q)) (start F (pairFst q))
    (query F (pairFst q) (pairSnd q).length) (F.condition (pairFst q)))]

theorem test_evaluator {F : Inputs} (h : F.PolyTime) : SpaceFunction (test F) := by
  have H := chart_evaluator (h.comp pairFst_mem_FP) (UnaryFn.length pairSnd_mem_FP)
  have hn := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  apply (H.postcompose (fun z => [decide (z ≠ [true])]) hn).congr
  funext q
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, chartFlag, Inputs.comp, query, start, inputs, dim, ops, output, term]
  simp only [decide_eq_true_eq, ne_eq, List.cons.injEq, and_true]

theorem scanned_iff_regular (F : Inputs) (c : List Bool) :
    (∀ i < dim F c, test F (pair c (List.replicate i true)) = [true]) ↔ Regular F c := by
  have ht (i : ℕ) (hi : i < dim F c) :
      test F (pair c (List.replicate i true)) = [true] ↔
        ¬ ∃ x : ℕ → ℝ, CriticalKernel.At (polynomial F c) (dim F c) (F.direction c) i (fun j => (x j : ℂ)) ∧
          (F.condition c).Holds x := by
    simp only [test, pairFst_pair, pairSnd_pair, List.length_replicate, List.cons.injEq, and_true,
      decide_eq_true_eq, chart_correct F c i hi]
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

theorem evaluator {F : Inputs} (h : F.PolyTime) : SpaceFunction (fun c => [decide (Regular F c)]) :=
  ((test_evaluator h).forall_unary (dim_unary h)).congr (funext fun c => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, scanned_iff_regular])

def language (F : Inputs) : Language := {c | Regular F c}

theorem decider {F : Inputs} (h : F.PolyTime) : SpaceDecider (language F) :=
  (evaluator h).decider (fun z => decide (z = [true]))
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
    (fun c => by simp only [language, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq])

theorem mem_PSPACE {F : Inputs} (h : F.PolyTime) : language F ∈ PSPACE := (decider h).mem_PSPACE

end LeanCanny.ETR.ComplexCircuit.BlockKernel
