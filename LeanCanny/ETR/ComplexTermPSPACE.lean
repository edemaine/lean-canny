/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexTermEncoding
public import LeanCanny.ETR.ComplexDyadicPSPACE

/-! # Native tests for denominator-cleared source terms

The source circuit and its fresh-wire metadata are generated from the original
validated syntax. Appending the binary-power circuit therefore yields a native
PSPACE test of the actual source equation, with no supplied source oracle.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Source
open LeanCanny.Computation
open scoped Classical

theorem scaled_satisfiable (start : ℕ) (t : Term) (ht : t.arity ≤ start) (bits : List Bool) :
    Satisfiable (Dyadic.zeroQuery (gates start t) (output start t) (start + count t) bits) ↔
      ∃ env : ℕ → ℂ, (2 : ℂ) ^ Nat.fromBitsLE bits * t.eval env - 1 = 0 := by
  rw [Dyadic.zeroQuery_satisfiable _ _ _ _ (output_lt start t ht) (gate_arity_le start t ht)]
  constructor
  · rintro ⟨env, hg, hz⟩
    exact ⟨env, by simpa only [sound start t env hg] using hz⟩
  · rintro ⟨env, hz⟩
    obtain ⟨out, _, hg, hv⟩ := exists_completion start t ht env
    exact ⟨out, hg, by simpa only [hv] using hz⟩

theorem encoded_gates_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) :
    (fun c => encode (gates (TermView.term (source c)).toData.size (TermView.term (source c)))) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp hs Machine.compile_mem_FP) (fun c => Machine.compile_eq (source c))

theorem scaledTerm_evaluator {source exponent : List Bool → List Bool}
    (hs : source ∈ FP) (he : exponent ∈ FP) :
    SpaceFunction (fun c => [decide (∃ env : ℕ → ℂ,
      (2 : ℂ) ^ Nat.fromBitsLE (exponent c) * (TermView.term (source c)).eval env - 1 = 0)]) := by
  have hp := UnaryFn.comp (f := Machine.outputIndex) (g := source) Machine.outputIndex_unary hs
  have hn := UnaryFn.comp (f := Machine.nextIndex) (g := source) Machine.nextIndex_unary hs
  have hq := Dyadic.zeroQuery_encode_mem_FP (encoded_gates_mem_FP hs) hp hn he
  have h := feasible_generated hq
  apply h.congr
  funext c
  simp only [Machine.outputIndex_eq, Machine.nextIndex_eq,
    scaled_satisfiable _ _ (Term.arity_le_dataSize _)]

end LeanCanny.ETR.ComplexCircuit.Source
