/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexTermPSPACE
public import LeanCanny.ETR.ComplexDifferentialEncoding

/-! # Exact derivatives of compiled source terms

The source compiler supplies its own polynomial interpretation. Initializing
the input derivative wires to a coordinate vector makes the transformed
network compute the formal partial derivative of the original source term.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open MvPolynomial
open scoped Classical

namespace Differential

theorem realizes_append {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (start : ℕ) (a b : List Operation) :
    Realizes wire start (a ++ b) ↔ Realizes wire start a ∧ Realizes wire (start + a.length) b := by
  induction a generalizing start with
  | nil => simp [Realizes]
  | cons op ops ih =>
    simp only [List.cons_append, Realizes, List.length_cons, ih]
    rw [show start + 1 + ops.length = start + (ops.length + 1) by omega]
    tauto

end Differential
namespace Source

theorem symbolic_sound {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (start : ℕ) (t : Term)
    (h : Differential.Realizes wire start (program start t)) : wire (output start t) = t.eval wire := by
  induction t generalizing start with
  | const z => exact h.1.trans (by simp [Differential.polynomial, Term.eval])
  | var i => rfl
  | add a b ha hb =>
    rw [program, Differential.realizes_append, Differential.realizes_append] at h
    simp only [program_length, List.length_append] at h
    have hc := h.2.1.trans (congrArg₂ (· + ·) (ha start h.1.1) (hb _ h.1.2))
    simpa only [output, Term.eval, Nat.add_assoc] using hc
  | mul a b ha hb =>
    rw [program, Differential.realizes_append, Differential.realizes_append] at h
    simp only [program_length, List.length_append] at h
    have hc := h.2.1.trans (congrArg₂ (· * ·) (ha start h.1.1) (hb _ h.1.2))
    simpa only [output, Term.eval, Nat.add_assoc] using hc

theorem eval_variables (t : Term) : t.eval (fun i => (X i : MvPolynomial ℕ ℤ)) = t.toPolynomial := by
  induction t <;> simp_all [Term.eval, Term.toPolynomial]

theorem symbolicRun_output (start : ℕ) (t : Term) (ht : t.arity ≤ start) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start (program start t) (output start t) =
      t.toPolynomial := by
  let wire := Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start (program start t)
  have hr := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) start
    (program start t) (wellFormed start t ht)
  calc
    wire (output start t) = t.eval wire := symbolic_sound _ _ _ hr
    _ = t.eval (fun i => (X i : MvPolynomial ℕ ℤ)) :=
      t.eval_congr _ _ (fun i hi => Differential.symbolicRun_preserves_before _ _ _ _ (hi.trans_le ht))
    _ = t.toPolynomial := eval_variables t

theorem input_agrees_iff (start : ℕ) (t : Term) (j : ℕ) (x env : ℕ → ℂ) (i : ℕ) (hi : i < start) :
    Differential.Agrees (Differential.symbolicRun (fun k => (X k : MvPolynomial ℕ ℤ))
      start (program start t)) j x env i ↔
      env (Differential.valueWire i) = x i ∧ env (Differential.derivativeWire i) = if i = j then 1 else 0 := by
  simp only [Differential.Agrees, Differential.symbolicRun_preserves_before _ _ _ _ hi, eval₂_X]
  by_cases hij : i = j
  · subst i
    simp
  · simp [hij, pderiv_X_of_ne hij]

theorem derivative_sound (start : ℕ) (t : Term) (ht : t.arity ≤ start) (j : ℕ) (x env : ℕ → ℂ)
    (hi : ∀ i < start, env (Differential.valueWire i) = x i ∧
      env (Differential.derivativeWire i) = if i = j then 1 else 0)
    (hg : ∀ g ∈ StraightLine.gates (Differential.valueWire start)
      (Differential.program start (program start t)), g.Holds env) :
    env (Differential.valueWire (output start t)) = t.eval x ∧
      env (Differential.derivativeWire (output start t)) =
        (pderiv j t.toPolynomial).eval₂ (Int.castRingHom ℂ) x := by
  have hr := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) start
    (program start t) (wellFormed start t ht)
  have h := Differential.sound _ j x start (program start t) (wellFormed start t ht) hr env
    (fun i h => (input_agrees_iff start t j x env i h).mpr (hi i h)) hg
  have ho := h (output start t) (by simpa only [program_length] using output_lt start t ht)
  simpa only [Differential.Agrees, symbolicRun_output start t ht, Term.eval₂_toPolynomial] using ho

noncomputable def derivativeInputs (x : ℕ → ℂ) (j : ℕ) (wire : ℕ) : ℂ :=
  if wire % 4 = 0 then x (wire / 4) else if wire / 4 = j then 1 else 0

theorem derivativeInputs_agrees (x : ℕ → ℂ) (j i : ℕ) :
    derivativeInputs x j (Differential.valueWire i) = x i ∧
      derivativeInputs x j (Differential.derivativeWire i) = if i = j then 1 else 0 := by
  have h0 : (4 * i) % 4 = 0 := by omega
  have hd0 : (4 * i) / 4 = i := by omega
  have h3 : (4 * i + 3) % 4 ≠ 0 := by omega
  have hd3 : (4 * i + 3) / 4 = i := by omega
  simp only [derivativeInputs, Differential.valueWire, Differential.derivativeWire, h0, hd0, h3, hd3,
    ite_true, ite_false]
  exact ⟨trivial, trivial⟩

theorem exists_derivative_completion (start : ℕ) (t : Term) (ht : t.arity ≤ start) (j : ℕ) (x : ℕ → ℂ) :
    ∃ env : ℕ → ℂ,
      (∀ g ∈ StraightLine.gates (Differential.valueWire start)
        (Differential.program start (program start t)), g.Holds env) ∧
      (∀ i < start, env (Differential.valueWire i) = x i ∧
        env (Differential.derivativeWire i) = if i = j then 1 else 0) ∧
      env (Differential.derivativeWire (output start t)) =
        (pderiv j t.toPolynomial).eval₂ (Int.castRingHom ℂ) x := by
  have hr := Differential.symbolicRun_realizes (fun i => (X i : MvPolynomial ℕ ℤ)) start
    (program start t) (wellFormed start t ht)
  obtain ⟨out, hp, hg, ha⟩ := Differential.exists_completion _ j x start (program start t)
    (wellFormed start t ht) hr (derivativeInputs x j)
    (fun i hi => (input_agrees_iff start t j x _ i hi).mpr (derivativeInputs_agrees x j i))
  refine ⟨out, hg, ?_, ?_⟩
  · intro i hi
    have h := ha i (by rw [program_length]; omega)
    exact (input_agrees_iff start t j x out i hi).mp h
  · have h := ha (output start t) (by simpa only [program_length] using output_lt start t ht)
    simpa only [Differential.Agrees, symbolicRun_output start t ht] using h.2

theorem encoded_derivative_gates_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) :
    (fun c => encode (StraightLine.gates (Differential.valueWire (TermView.term (source c)).toData.size)
      (Differential.program (TermView.term (source c)).toData.size
        (program (TermView.term (source c)).toData.size (TermView.term (source c)))))) ∈ FP := by
  have hq : (fun c => encode (StraightLine.gates (TermView.term (source c)).toData.size
      (program (TermView.term (source c)).toData.size (TermView.term (source c))))) ∈ FP := by
    simpa only [gates_eq] using encoded_gates_mem_FP hs
  exact Differential.program_encode_mem_FP hq

end Source
end LeanCanny.ETR.ComplexCircuit
