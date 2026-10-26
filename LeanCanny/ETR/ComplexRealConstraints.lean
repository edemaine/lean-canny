/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexRealEvaluation
public import LeanCanny.ETR.InterleaveFP

/-! # Boolean constraints on real circuit coordinates

An arbitrary real formula can constrain the circuit wires in the same
existential query. The compiler keeps those coordinates aligned with the real
parts of the shared network. Input-only constraints characterize precisely the
polynomial model on real inputs, including strict inequalities and irrational
singleton descriptions.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.RealQuery
open LeanCanny.Computation LeanCanny.Encoding MvPolynomial
open scoped Classical

def WithConstraints (inputs : ℕ) (gates : List Gate) (p : Formula) : Prop :=
  ∃ env : ℕ → ℂ, (∀ g ∈ gates, g.Holds env) ∧ (∀ i < inputs, (env i).im = 0) ∧
    p.Holds (fun i => (env i).re)

def constraintFormula (inputs : ℕ) (gates : List Gate) (p : Formula) : Formula :=
  .and (.eqZero (SumSquares.accumulate (equations gates ++ inputEquations inputs) (.const 0)))
    (p.rename (Interleave.index false))

def constraintBits (inputs : ℕ) (gates p : List Bool) : List Bool :=
  Codec.taggedTwo 4 (EquationList.toSingleEquation (queryBits inputs gates)) (Interleave.renameBits false p)

theorem constraintBits_mem_FP {inputs : List Bool → ℕ} {gates p : List Bool → List Bool}
    (hi : UnaryFn inputs) (hg : gates ∈ FP) (hp : p ∈ FP) :
    (fun c => constraintBits (inputs c) (gates c) (p c)) ∈ FP :=
  Codec.taggedTwo_mem_FP 4 (mem_FP_comp (queryBits_mem_FP hi hg) EquationList.toSingleEquation_mem_FP)
    (mem_FP_comp hp (Interleave.renameBits_mem_FP false))

theorem constraintBits_encode (inputs : ℕ) (gates : List Gate) (p : Formula) :
    constraintBits inputs (encode gates) p.encode = (constraintFormula inputs gates p).encode := by
  rw [constraintBits, queryBits_encode, EquationList.toSingleEquation_listBits, Interleave.renameBits_encode]
  simp only [constraintFormula, Formula.encode, Formula.toData, Codec.taggedTwo_toBits]

theorem constraintFormula_correct (inputs : ℕ) (gates : List Gate) (p : Formula) :
    (constraintFormula inputs gates p).Satisfiable ↔ WithConstraints inputs gates p := by
  constructor
  · rintro ⟨env, he, hp⟩
    have h := (SumSquares.accumulate_zero_iff _ env).mp he
    refine ⟨complexEnv env, (equations_iff gates env).mp (fun t ht => h t (List.mem_append_left _ ht)), ?_, ?_⟩
    · intro i hi
      exact h (imagWire i) (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    · simpa only [Formula.holds_rename, Function.comp_def, Interleave.index, Bool.toNat_false, Nat.add_zero,
        complexEnv] using hp
  · rintro ⟨env, hg, hr, hp⟩
    refine ⟨realEnv env, (SumSquares.accumulate_zero_iff _ _).mpr ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · apply (equations_iff gates (realEnv env)).mpr ?_ t ht
        simpa only [complexEnv_realEnv] using hg
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
        simpa only [imagWire, Term.eval, realEnv_odd] using hr i (List.mem_range.mp hi)
    · simpa only [Formula.holds_rename, Function.comp_def, Interleave.index, Bool.toNat_false, Nat.add_zero,
        realEnv_even] using hp

theorem constraint_evaluator {inputs : List Bool → ℕ} {gates : List Bool → List Gate} {p : List Bool → Formula}
    (hi : UnaryFn inputs) (hg : (fun c => encode (gates c)) ∈ FP) (hp : (fun c => (p c).encode) ∈ FP) :
    SpaceFunction (fun c => [decide (WithConstraints (inputs c) (gates c) (p c))]) := by
  have he := (SpaceDecider.ofPSPACE etr_mem_PSPACE).flagEvaluator.precompose _ (constraintBits_mem_FP hi hg hp)
  apply he.congr
  funext c
  simp only [Function.comp_apply, constraintBits_encode, encode_mem_language, constraintFormula_correct]

theorem zero_constraints_with_iff (start : ℕ) (ops : List Operation) (outputs : List ℕ) (p : Formula)
    (hw : StraightLine.WellFormed start ops) (ho : ∀ out ∈ outputs, out < start + ops.length)
    (hp : p.arity ≤ start) :
    WithConstraints start (StraightLine.gates start ops ++ outputs.map Gate.zero) p ↔
      ∃ x : ℕ → ℝ, (∀ out ∈ outputs,
        (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops out).eval₂ (Int.castRingHom ℝ) x = 0) ∧
        p.Holds x := by
  constructor
  · rintro ⟨env, hg, hr, hpred⟩
    -- Use this assignment itself so the Boolean constraints retain their witnesses.
    let x : ℕ → ℝ := fun i => (env i).re
    have hprogram : ∀ g ∈ StraightLine.gates start ops, g.Holds env :=
      fun g h => hg g (List.mem_append_left _ h)
    have hin : ∀ i < start, env i = (x i : ℂ) := by
      intro i hi
      apply Complex.ext
      · rfl
      · exact hr i hi
    refine ⟨x, ?_, hpred⟩
    intro out hout
    have hv := StraightLine.symbolic_value env start ops hw hprogram (fun i => (x i : ℂ)) hin out (ho out hout)
    have hz : env out = 0 := hg (.zero out) (List.mem_append_right _ (List.mem_map.mpr ⟨out, hout, rfl⟩))
    rw [polynomial_eval_ofReal] at hv
    have he : Complex.ofReal ((Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start ops out).eval₂
        (Int.castRingHom ℝ) x) = 0 := hv.symm.trans hz
    exact_mod_cast he
  · rintro ⟨x, hx, hpred⟩
    let env : ℕ → ℂ := StraightLine.run (fun i => (x i : ℂ)) start ops
    have hprogram : ∀ g ∈ StraightLine.gates start ops, g.Holds env := StraightLine.run_satisfies _ _ _ hw
    have hin : ∀ i < start, env i = (x i : ℂ) :=
      fun i hi => StraightLine.run_preserves_before _ _ _ i hi
    refine ⟨env, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hprogram g hg
      · obtain ⟨out, hout, rfl⟩ := List.mem_map.mp hg
        change env out = 0
        rw [StraightLine.symbolic_value env start ops hw hprogram (fun i => (x i : ℂ)) hin out (ho out hout),
          polynomial_eval_ofReal, hx out hout, Complex.ofReal_zero]
    · intro i hi
      rw [hin i hi]
      exact Complex.ofReal_im _
    · apply (p.holds_congr x (fun i => (env i).re) ?_).mp hpred
      intro i hi
      rw [hin i (hi.trans_le hp)]
      exact (Complex.ofReal_re _).symm

end LeanCanny.ETR.ComplexCircuit.RealQuery
