/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitPSPACE

/-! # Native Boolean constraints on both parts of complex circuit wires

Logical indices `2*i` and `2*i+1` refer to the real and imaginary parts of
wire `i`. The compiler retains that complete assignment while conjoining the
real circuit equations with an arbitrary Boolean formula. No real-input
restriction is imposed on the original network.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.RealifiedQuery
open LeanCanny.Computation LeanCanny.Encoding
open scoped Classical

theorem realEnv_complexEnv (x : ℕ → ℝ) : realEnv (complexEnv x) = x := by
  funext i
  unfold realEnv complexEnv
  by_cases hi : i % 2 = 0
  · simp only [hi, ite_true]
    congr 1
    omega
  · simp only [hi, ite_false]
    congr 1
    omega

def WithConstraints (gates : List Gate) (p : Formula) : Prop :=
  ∃ env : ℕ → ℂ, (∀ g ∈ gates, g.Holds env) ∧ p.Holds (realEnv env)

def formula (gates : List Gate) (p : Formula) : Formula :=
  .and (.eqZero (SumSquares.accumulate (equations gates) (.const 0))) p

def bits (gates p : List Bool) : List Bool :=
  Codec.taggedTwo 4 (EquationList.toSingleEquation (compile gates)) p

theorem bits_FP {gates p : List Bool → List Bool} (hg : gates ∈ FP) (hp : p ∈ FP) :
    (fun c => bits (gates c) (p c)) ∈ FP :=
  Codec.taggedTwo_mem_FP 4 (mem_FP_comp (mem_FP_comp hg compile_mem_FP) EquationList.toSingleEquation_mem_FP) hp

theorem bits_encode (gates : List Gate) (p : Formula) : bits (encode gates) p.encode = (formula gates p).encode := by
  rw [bits, compile_encode, EquationList.toSingleEquation_listBits]
  simp only [formula, Formula.encode, Formula.toData, Codec.taggedTwo_toBits]

theorem correct (gates : List Gate) (p : Formula) : (formula gates p).Satisfiable ↔ WithConstraints gates p := by
  constructor
  · rintro ⟨x, he, hp⟩
    have hg := (equations_iff gates x).mp ((SumSquares.accumulate_zero_iff _ _).mp he)
    exact ⟨complexEnv x, hg, by simpa only [realEnv_complexEnv] using hp⟩
  · rintro ⟨env, hg, hp⟩
    refine ⟨realEnv env, (SumSquares.accumulate_zero_iff _ _).mpr ?_, hp⟩
    apply (equations_iff gates _).mpr
    simpa only [complexEnv_realEnv] using hg

theorem evaluator {gates : List Bool → List Gate} {p : List Bool → Formula}
    (hg : (fun c => encode (gates c)) ∈ FP) (hp : (fun c => (p c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide (WithConstraints (gates c) (p c))]) := by
  have E := (SpaceDecider.ofPSPACE etr_mem_PSPACE).flagEvaluator.precompose _ (bits_FP hg hp)
  apply E.congr
  funext c
  simp only [Function.comp_apply, bits_encode, encode_mem_language, correct]

end LeanCanny.ETR.ComplexCircuit.RealifiedQuery
