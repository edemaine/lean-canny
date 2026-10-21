/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationCompilerStepEncoding
public import LeanCanny.ETR.NNFComplexity
public import LeanCanny.ETR.EquationListComplexity

/-!
# Polynomial-time compilation of arbitrary ETR formulas to equations

Normalize the input, reserve its normalized bit length as the first fresh
index, and run the verified stack compiler for twice that length. The complete
encoded state has a cubic bound throughout. Malformed input normalizes to
falsum and therefore produces an unsatisfiable equation system.
-/

@[expose] public section

namespace LeanCanny.ETR
open Complexity
open LeanCanny.Encoding

theorem SumSquares.listBits_injective : Function.Injective SumSquares.listBits := by
  intro ts us h
  have hd := Data.toBits_injective h
  have hl := Data.l.inj hd
  exact (List.map_injective_iff.mpr Term.toData_injective) hl

@[simp] theorem EquationList.listBits_mem_language (ts : List Term) :
    SumSquares.listBits ts ∈ EquationList.language ↔ ∃ env : ℕ → ℝ, ∀ t ∈ ts, t.eval env = 0 := by
  simp [EquationList.language, SumSquares.listBits_injective.eq_iff]

namespace EquationCompiler

def initBits (bits : List Bool) : List Bool :=
  let normalized := NNF.normalize bits
  pair (pair (false :: normalized) []) (pair [] (Codec.unary normalized.length).toBits)

def ruler (bits : List Bool) : List Bool := NNF.normalize bits ++ NNF.normalize bits

theorem initBits_mem_FP : initBits ∈ FP := by
  have hn := NNF.normalize_mem_FP
  have hu := Codec.unary_toBits_mem_FP (UnaryFn.length hn)
  polytime [initBits]

theorem ruler_mem_FP : ruler ∈ FP :=
  Cobham.appendFn_mem_FP NNF.normalize_mem_FP NNF.normalize_mem_FP

theorem initBits_of_normalize (bits : List Bool) (p : Formula)
    (hp : NNF.normalize bits = p.encode) (hn : p.IsNNF = true) :
    initBits bits = (State.mk [.visit (p.toSigned true)] [] p.encode.length).encode := by
  have he : (p.toSigned true).toFormula = p := p.nnf_eq_self_of_isNNF hn
  simp [initBits, hp, State.encode, DynamicTreeFold.stackBits, Instruction.encode, he]

def runBits (bits : List Bool) : List Bool := stepBits^[(ruler bits).length] (initBits bits)

theorem runBits_mem_FP : runBits ∈ FP := by
  have hsemi : Function.Semiconj State.encode step stepBits := fun s => (stepBits_encode s).symm
  have hbound := (PolyBound.const 10000).mul
    ((((PolyBound.const 20).mul PolyBound.id).add (PolyBound.const 5)).pow 3)
  refine iterate_mem_FP_of_polyBound stepBits_mem_FP initBits_mem_FP ruler_mem_FP hbound ?_
  intro bits k hk
  obtain ⟨p, hp, hn⟩ := NNF.normalize_shape bits
  rw [initBits_of_normalize bits p hp hn, ← hsemi.iterate_right k]
  have hk' : k ≤ 2 * p.encode.length := by
    simpa only [ruler, hp, List.length_append, ← two_mul] using hk
  have hs := formula_run_encode_length_le p k hk'
  have hnlen := NNF.normalize_length_le bits
  rw [hp] at hnlen
  change (run (p.toSigned true) p.encode.length k).encode.length ≤ 10000 * (20 * bits.length + 5) ^ 3
  apply hs.trans
  exact Nat.mul_le_mul_left 10000
    (Nat.pow_le_pow_left (by omega : p.encode.length + 1 ≤ 20 * bits.length + 5) 3)

theorem runBits_of_normalize (bits : List Bool) (p : Formula)
    (hp : NNF.normalize bits = p.encode) (hn : p.IsNNF = true) :
    runBits bits = (State.mk [] [(p.toSigned true).equations p.encode.length]
      ((p.toSigned true).equations p.encode.length).next).encode := by
  have hsemi : Function.Semiconj State.encode step stepBits := fun s => (stepBits_encode s).symm
  rw [runBits, initBits_of_normalize bits p hp hn, ← hsemi.iterate_right]
  have hr : (ruler bits).length = 2 * p.encode.length := by
    simp only [ruler, hp, List.length_append, two_mul]
  rw [hr, formula_run_steps]

def compileTerms (bits : List Bool) : List Bool := pairSnd (pairFst (valuesBits (runBits bits)))

theorem compileTerms_mem_FP : compileTerms ∈ FP := by
  have hr := runBits_mem_FP
  polytime [compileTerms, valuesBits]

theorem compileTerms_of_normalize (bits : List Bool) (p : Formula)
    (hp : NNF.normalize bits = p.encode) (hn : p.IsNNF = true) :
    compileTerms bits = SumSquares.listBits ((p.toSigned true).equations p.encode.length).terms := by
  rw [compileTerms, runBits_of_normalize bits p hp hn]
  simp [valuesBits, State.encode, DynamicTreeFold.stackBits, EquationSystem.encode]

theorem compileTerms_encode (p : Formula) :
    compileTerms p.encode =
      SumSquares.listBits ((p.toSigned true).equations (p.nnf true).encode.length).terms := by
  simpa only [Formula.nnf_toSigned] using
    compileTerms_of_normalize p.encode (p.nnf true) (NNF.normalize_encode p) (p.nnf_isNNF true)

theorem compileTerms_shape (bits : List Bool) :
    ∃ ts : List Term, compileTerms bits = SumSquares.listBits ts := by
  obtain ⟨p, hp, hn⟩ := NNF.normalize_shape bits
  exact ⟨_, compileTerms_of_normalize bits p hp hn⟩

theorem compileTerms_malformed (bits : List Bool) (hr : Grammar.recognizeFormula bits ≠ true) :
    compileTerms bits = SumSquares.listBits [.const 1] := by
  have hp : NNF.normalize bits = Formula.falsum.encode := by
    rw [NNF.normalize, ite_eq_right hr]
    rfl
  simpa only [Formula.toSigned, ite_true, SignedFormula.equations] using
    compileTerms_of_normalize bits .falsum hp rfl

/-- Correct on all binary strings, with one shared existential assignment for the equations. -/
theorem compileTerms_correct (bits : List Bool) : bits ∈ ETR.language ↔ compileTerms bits ∈ EquationList.language := by
  obtain ⟨p, hp, hn⟩ := NNF.normalize_shape bits
  have he : bits ∈ ETR.language ↔ p.Satisfiable := by
    simpa only [hp, NNF.encode_mem_language, hn, true_and] using NNF.normalize_correct bits
  rw [he, compileTerms_of_normalize bits p hp hn, EquationList.listBits_mem_language]
  have ha : (p.toSigned true).arity ≤ p.encode.length := by
    simpa only [Formula.toSigned_arity, Formula.encode, Data.length_toBits] using p.arity_le_dataSize
  constructor
  · rintro ⟨env, h⟩
    obtain ⟨env', _, heq⟩ := (p.toSigned true).equations_complete p.encode.length ha env
      ((p.holds_toSigned true env).mpr h)
    exact ⟨env', heq⟩
  · rintro ⟨env, h⟩
    exact ⟨env, (p.holds_toSigned true env).mp ((p.toSigned true).equations_sound _ env h)⟩

theorem etr_reduces_to_equationList : PolyTimeReduces ETR.language EquationList.language :=
  ⟨compileTerms, Computation.TidyFP.of_mem_FP compileTerms_mem_FP, compileTerms_correct⟩

def toSingleEquation (bits : List Bool) : List Bool := EquationList.toSingleEquation (compileTerms bits)

theorem toSingleEquation_mem_FP : toSingleEquation ∈ FP := by
  have hc := compileTerms_mem_FP
  have hw := EquationList.toSingleEquation_mem_FP
  polytime [toSingleEquation]

theorem toSingleEquation_correct (bits : List Bool) :
    bits ∈ ETR.language ↔ toSingleEquation bits ∈ SingleEquation.language :=
  (compileTerms_correct bits).trans (EquationList.toSingleEquation_correct (compileTerms bits))

theorem etr_reduces_to_singleEquation : PolyTimeReduces ETR.language SingleEquation.language :=
  ⟨toSingleEquation, Computation.TidyFP.of_mem_FP toSingleEquation_mem_FP, toSingleEquation_correct⟩

end EquationCompiler

theorem EquationList.existsRealComplete : LeanCanny.ExistsRealComplete EquationList.language :=
  ⟨EquationList.mem_existsReal,
    (LeanCanny.existsRealHard_iff _).mpr EquationCompiler.etr_reduces_to_equationList⟩

theorem SingleEquation.existsRealComplete : LeanCanny.ExistsRealComplete SingleEquation.language :=
  ⟨SingleEquation.mem_existsReal,
    (LeanCanny.existsRealHard_iff _).mpr EquationCompiler.etr_reduces_to_singleEquation⟩

end LeanCanny.ETR
