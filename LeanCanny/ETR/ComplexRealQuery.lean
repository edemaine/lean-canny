/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitPSPACE
public import LeanCanny.Computation.PolyTimeRange

/-! # Real-input queries for shared arithmetic circuits

The usual complex-gate equations are conjoined with zero imaginary parts for
the designated input wires. The native equation writer and PSPACE test charge
the input count and the actual encoded gate reader. Complex feasibility alone
is insufficient for the real source and marking predicates.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.RealQuery
open LeanCanny.Computation LeanCanny.Encoding.Brackets
open scoped Classical

def inputEquations (inputs : ℕ) : List Term := (List.range inputs).map imagWire
def inputBits (inputs : ℕ) : List Bool := SumSquares.listBits (inputEquations inputs)

private theorem listBits_wrap (ts : List Term) : SumSquares.listBits ts = wrap (SumSquares.forest ts) := by
  simp only [SumSquares.listBits, SumSquares.forest, Data.toBits_l, List.map_map, Function.comp_def]
  rfl

theorem inputBits_mem_FP {inputs : List Bool → ℕ} (hi : UnaryFn inputs) : (fun c => inputBits (inputs c)) ∈ FP := by
  have hb := imagBits_mem_FP (UnaryFn.length pairSnd_mem_FP)
  have hf := flatMap_range_mem_FP hb hi.mem_FP
  apply mem_FP_of_eq (mem_FP_comp hf wrap_mem_FP)
  intro c
  simp only [Function.comp_apply, List.length_replicate, pairSnd_pair, imagBits, Term.variableBits_eq,
    inputBits, listBits_wrap, SumSquares.forest, inputEquations, List.map_map, List.flatten_eq_flatMap]
  simp only [List.flatMap_map, Function.comp_def, imagWire, id_eq]

def queryBits (inputs : ℕ) (gates : List Bool) : List Bool :=
  wrap (contents (ComplexCircuit.compile gates) ++ contents (inputBits inputs))

theorem queryBits_mem_FP {inputs : List Bool → ℕ} {gates : List Bool → List Bool}
    (hi : UnaryFn inputs) (hg : gates ∈ FP) : (fun c => queryBits (inputs c) (gates c)) ∈ FP :=
  mem_FP_comp (appendFn_mem_FP (mem_FP_comp (mem_FP_comp hg ComplexCircuit.compile_mem_FP) contents_mem_FP)
    (mem_FP_comp (inputBits_mem_FP hi) contents_mem_FP)) wrap_mem_FP

theorem queryBits_encode (inputs : ℕ) (gates : List Gate) :
    queryBits inputs (encode gates) = SumSquares.listBits (equations gates ++ inputEquations inputs) := by
  rw [queryBits, ComplexCircuit.compile_encode, SumSquares.contents_listBits, inputBits,
    SumSquares.contents_listBits, listBits_wrap, real_forest_append]

def Satisfiable (inputs : ℕ) (gates : List Gate) : Prop :=
  ∃ env : ℕ → ℂ, (∀ g ∈ gates, g.Holds env) ∧ ∀ i < inputs, (env i).im = 0

theorem real_equations_iff (inputs : ℕ) (gates : List Gate) :
    (∃ env : ℕ → ℝ, ∀ t ∈ equations gates ++ inputEquations inputs, t.eval env = 0) ↔ Satisfiable inputs gates := by
  constructor
  · rintro ⟨env, h⟩
    refine ⟨complexEnv env, (equations_iff gates env).mp (fun t ht => h t (List.mem_append_left _ ht)), ?_⟩
    intro i hi
    have ht := h (imagWire i) (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    exact ht
  · rintro ⟨env, hg, hr⟩
    refine ⟨realEnv env, ?_⟩
    intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · apply (equations_iff gates (realEnv env)).mpr ?_ t ht
      simpa only [complexEnv_realEnv] using hg
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
      simpa only [imagWire, Term.eval, realEnv_odd] using hr i (List.mem_range.mp hi)

theorem queryBits_correct (inputs : ℕ) (gates : List Gate) :
    queryBits inputs (encode gates) ∈ EquationList.language ↔ Satisfiable inputs gates := by
  have hinj : Function.Injective SumSquares.listBits := by
    intro a b h
    exact (List.map_injective_iff.mpr Term.toData_injective) (Data.l.inj (Data.toBits_injective h))
  rw [queryBits_encode]
  change (∃ ts : List Term, SumSquares.listBits (equations gates ++ inputEquations inputs) = SumSquares.listBits ts ∧
    ∃ env : ℕ → ℝ, ∀ t ∈ ts, t.eval env = 0) ↔ _
  constructor
  · rintro ⟨ts, he, h⟩
    have ht := hinj he
    subst ts
    exact (real_equations_iff inputs gates).mp h
  · intro h
    exact ⟨_, rfl, (real_equations_iff inputs gates).mpr h⟩

noncomputable def feasible (inputs : ℕ) (bits : List Bool) : List Bool :=
  [decide (queryBits inputs bits ∈ EquationList.language)]
noncomputable def empty (inputs : ℕ) (bits : List Bool) : List Bool :=
  [decide (queryBits inputs bits ∉ EquationList.language)]

theorem feasible_evaluator {inputs : List Bool → ℕ} {gates : List Bool → List Bool}
    (hi : UnaryFn inputs) (hg : gates ∈ FP) : SpaceFunction (fun c => feasible (inputs c) (gates c)) := by
  have hEq : EquationList.language ∈ PSPACE := ETR.existsReal_subset_PSPACE EquationList.mem_existsReal
  exact (SpaceDecider.ofPSPACE hEq).flagEvaluator.precompose _ (queryBits_mem_FP hi hg)

theorem empty_evaluator {inputs : List Bool → ℕ} {gates : List Bool → List Bool}
    (hi : UnaryFn inputs) (hg : gates ∈ FP) : SpaceFunction (fun c => empty (inputs c) (gates c)) := by
  let negate := fun bits : List Bool => [decide (bits ≠ [true])]
  have hn : negate ∈ FP := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  have he := (feasible_evaluator hi hg).postcompose negate hn
  apply he.congr
  funext c
  by_cases h : queryBits (inputs c) (gates c) ∈ EquationList.language <;>
    simp [Function.comp_apply, feasible, empty, negate, h]

theorem feasible_generated {inputs : List Bool → ℕ} {gates : List Bool → List Gate}
    (hi : UnaryFn inputs) (hg : (fun c => encode (gates c)) ∈ FP) :
    SpaceFunction (fun c => [decide (Satisfiable (inputs c) (gates c))]) := by
  apply (feasible_evaluator hi hg).congr
  funext c
  simp only [feasible, queryBits_correct]

theorem empty_generated {inputs : List Bool → ℕ} {gates : List Bool → List Gate}
    (hi : UnaryFn inputs) (hg : (fun c => encode (gates c)) ∈ FP) :
    SpaceFunction (fun c => [decide (¬ Satisfiable (inputs c) (gates c))]) := by
  apply (empty_evaluator hi hg).congr
  funext c
  simp only [empty, queryBits_correct]

end LeanCanny.ETR.ComplexCircuit.RealQuery
