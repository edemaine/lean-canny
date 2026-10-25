/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexTermDifferential
public import LeanCanny.ETR.ComplexDifferentialSymbolic

/-! # Hessians of the original compiled source term

Two derivative passes compute the source value, both selected first partials,
and their mixed second partial. The seed polynomials depend only on the input
coordinates, rather than on a supplied interpretation of intermediate wires.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Source
open MvPolynomial
open scoped Classical

noncomputable def hessianInputPolynomials (j : ℕ) : ℕ → MvPolynomial ℕ ℤ :=
  Differential.polynomialInputs (fun i => X i) j

noncomputable def hessianInputs (j k : ℕ) (x : ℕ → ℂ) (q : ℕ) : ℂ :=
  (Differential.polynomialInputs (hessianInputPolynomials j) k q).eval₂ (Int.castRingHom ℂ) x

theorem hessianInputs_agrees (j k : ℕ) (x : ℕ → ℂ) (q : ℕ) :
    Differential.Agrees (hessianInputPolynomials j) k x (hessianInputs j k x) q := by
  constructor
  · exact congrArg (fun p : MvPolynomial ℕ ℤ => p.eval₂ (Int.castRingHom ℂ) x)
      (Differential.polynomialInputs_value _ k q)
  · exact congrArg (fun p : MvPolynomial ℕ ℤ => p.eval₂ (Int.castRingHom ℂ) x)
      (Differential.polynomialInputs_derivative _ k q)

theorem sourceJet_before (start : ℕ) (t : Term) (j q : ℕ) (hq : q < Differential.valueWire start) :
    Differential.polynomialInputs
      (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start (program start t)) j q =
        hessianInputPolynomials j q := by
  have hd : q / 4 < start := by unfold Differential.valueWire at hq; omega
  simp only [Differential.polynomialInputs, hessianInputPolynomials,
    Differential.symbolicRun_preserves_before _ start (program start t) (q / 4) hd]

theorem hessian_sound (start : ℕ) (t : Term) (ht : t.arity ≤ start) (j k : ℕ) (x env : ℕ → ℂ)
    (hi : ∀ q < Differential.valueWire start, Differential.Agrees (hessianInputPolynomials j) k x env q)
    (hg : ∀ g ∈ StraightLine.gates (Differential.valueWire (Differential.valueWire start))
      (Differential.secondProgram start (program start t)), g.Holds env) :
    env (Differential.valueWire (Differential.valueWire (output start t))) = t.eval x ∧
      env (Differential.derivativeWire (Differential.valueWire (output start t))) =
        (pderiv k t.toPolynomial).eval₂ (Int.castRingHom ℂ) x ∧
      env (Differential.valueWire (Differential.derivativeWire (output start t))) =
        (pderiv j t.toPolynomial).eval₂ (Int.castRingHom ℂ) x ∧
      env (Differential.derivativeWire (Differential.derivativeWire (output start t))) =
        (pderiv k (pderiv j t.toPolynomial)).eval₂ (Int.castRingHom ℂ) x := by
  have hr := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) start
    (program start t) (wellFormed start t ht)
  have hin : ∀ q < Differential.valueWire start, Differential.Agrees
      (Differential.polynomialInputs
        (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start (program start t)) j) k x env q := by
    intro q hq
    simpa only [Differential.Agrees, sourceJet_before start t j q hq] using hi q hq
  have h := Differential.second_sound _ j k x start (program start t) (wellFormed start t ht) hr env hin hg
    (output start t) (by simpa only [program_length] using output_lt start t ht)
  simpa only [Differential.SecondAgrees, symbolicRun_output start t ht, Term.eval₂_toPolynomial] using h

theorem exists_hessian_completion (start : ℕ) (t : Term) (ht : t.arity ≤ start) (j k : ℕ) (x : ℕ → ℂ) :
    ∃ env : ℕ → ℂ,
      (∀ g ∈ StraightLine.gates (Differential.valueWire (Differential.valueWire start))
        (Differential.secondProgram start (program start t)), g.Holds env) ∧
      (∀ q < Differential.valueWire start, Differential.Agrees (hessianInputPolynomials j) k x env q) ∧
      env (Differential.valueWire (Differential.valueWire (output start t))) = t.eval x ∧
      env (Differential.derivativeWire (Differential.valueWire (output start t))) =
        (pderiv k t.toPolynomial).eval₂ (Int.castRingHom ℂ) x ∧
      env (Differential.valueWire (Differential.derivativeWire (output start t))) =
        (pderiv j t.toPolynomial).eval₂ (Int.castRingHom ℂ) x ∧
      env (Differential.derivativeWire (Differential.derivativeWire (output start t))) =
        (pderiv k (pderiv j t.toPolynomial)).eval₂ (Int.castRingHom ℂ) x := by
  obtain ⟨out, hp, hg⟩ := StraightLine.exists_completion (hessianInputs j k x)
    (Differential.valueWire (Differential.valueWire start))
    (Differential.secondProgram start (program start t))
    (Differential.second_wellFormed start (program start t) (wellFormed start t ht))
  have hin : ∀ q < Differential.valueWire start, Differential.Agrees (hessianInputPolynomials j) k x out q := by
    intro q hq
    have hv : Differential.valueWire q < Differential.valueWire (Differential.valueWire start) := by
      unfold Differential.valueWire at *; omega
    have hd : Differential.derivativeWire q < Differential.valueWire (Differential.valueWire start) := by
      unfold Differential.valueWire Differential.derivativeWire at *; omega
    exact ⟨(hp _ hv).trans (hessianInputs_agrees j k x q).1, (hp _ hd).trans (hessianInputs_agrees j k x q).2⟩
  exact ⟨out, hg, hin, hessian_sound start t ht j k x out hin hg⟩

theorem encoded_hessian_gates_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) :
    (fun c => encode (StraightLine.gates
      (Differential.valueWire (Differential.valueWire (TermView.term (source c)).toData.size))
      (Differential.secondProgram (TermView.term (source c)).toData.size
        (program (TermView.term (source c)).toData.size (TermView.term (source c)))))) ∈ FP := by
  have hq : (fun c => encode (StraightLine.gates (TermView.term (source c)).toData.size
      (program (TermView.term (source c)).toData.size (TermView.term (source c))))) ∈ FP := by
    simpa only [gates_eq] using encoded_gates_mem_FP hs
  exact Differential.second_encode_mem_FP hq

end LeanCanny.ETR.ComplexCircuit.Source
