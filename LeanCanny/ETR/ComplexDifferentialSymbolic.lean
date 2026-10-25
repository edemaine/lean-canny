/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexDifferentialEncoding
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.CharZero.Infinite

/-! # Polynomial interpretations of shared derivative circuits

The symbolic execution of a derivative program computes the source value and
its exact formal derivative as polynomials. The proof evaluates the program
over C and uses polynomial extensionality; it never expands the source wires
in the generated circuit. This interpretation permits repeated differentiation.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Differential
open MvPolynomial
open scoped Classical

theorem realizes_gates_eval {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ)
    (start : ℕ) (ops : List Operation) (hr : Realizes wire start ops) (x : σ → ℂ) :
    ∀ g ∈ StraightLine.gates start ops, g.Holds (fun i => (wire i).eval₂ (Int.castRingHom ℂ) x) := by
  induction ops generalizing start with
  | nil => simp [StraightLine.gates]
  | cons op ops ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · apply (Operation.gate_holds_iff op start _).mpr
      exact (congrArg (fun p : MvPolynomial σ ℤ => p.eval₂ (Int.castRingHom ℂ) x) hr.1).trans
        (polynomial_eval wire op x)
    · exact ih (start + 1) hr.2 g hg

theorem eq_of_eval_complex {σ : Type*} (p q : MvPolynomial σ ℤ)
    (h : ∀ x : σ → ℂ, p.eval₂ (Int.castRingHom ℂ) x = q.eval₂ (Int.castRingHom ℂ) x) : p = q := by
  apply MvPolynomial.map_injective (Int.castRingHom ℂ) (show Function.Injective (Int.castRingHom ℂ) from Int.cast_injective)
  apply MvPolynomial.funext
  intro x
  simpa only [eval_map] using h x

noncomputable def polynomialInputs {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j : σ) (i : ℕ) :
    MvPolynomial σ ℤ :=
  if i % 4 = 0 then wire (i / 4) else if i % 4 = 3 then pderiv j (wire (i / 4)) else 0

theorem polynomialInputs_value {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j : σ) (i : ℕ) :
    polynomialInputs wire j (valueWire i) = wire i := by
  have hm : 4 * i % 4 = 0 := by omega
  have hd : 4 * i / 4 = i := by omega
  unfold polynomialInputs valueWire
  rw [ite_eq_left hm, hd]

theorem polynomialInputs_derivative {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j : σ) (i : ℕ) :
    polynomialInputs wire j (derivativeWire i) = pderiv j (wire i) := by
  have hm0 : (4 * i + 3) % 4 ≠ 0 := by omega
  have hm3 : (4 * i + 3) % 4 = 3 := by omega
  have hd : (4 * i + 3) / 4 = i := by omega
  unfold polynomialInputs derivativeWire
  rw [ite_eq_right hm0, ite_eq_left hm3, hd]

noncomputable def liftModel {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j : σ)
    (start : ℕ) (ops : List Operation) : ℕ → MvPolynomial σ ℤ :=
  symbolicRun (polynomialInputs wire j) (valueWire start) (program start ops)

theorem liftModel_realizes {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j : σ)
    (start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed start ops) :
    Realizes (liftModel wire j start ops) (valueWire start) (program start ops) :=
  symbolicRun_realizes _ _ _ (wellFormed start ops hw)

theorem liftModel_before {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j : σ)
    (start : ℕ) (ops : List Operation) (i : ℕ) (hi : i < valueWire start) :
    liftModel wire j start ops i = polynomialInputs wire j i :=
  symbolicRun_preserves_before _ _ _ _ hi

theorem liftModel_correct {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j : σ)
    (start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed start ops)
    (hr : Realizes wire start ops) (i : ℕ) (hi : i < start + ops.length) :
    liftModel wire j start ops (valueWire i) = wire i ∧
      liftModel wire j start ops (derivativeWire i) = pderiv j (wire i) := by
  have heval (x : σ → ℂ) : Agrees wire j x
      (fun k => (liftModel wire j start ops k).eval₂ (Int.castRingHom ℂ) x) i := by
    apply sound wire j x start ops hw hr _ ?_ (realizes_gates_eval _ _ _ (liftModel_realizes wire j start ops hw) x) i hi
    intro k hk
    have hv : valueWire k < valueWire start := by unfold valueWire; omega
    have hd : derivativeWire k < valueWire start := by unfold valueWire derivativeWire; omega
    constructor
    · dsimp only
      rw [liftModel_before wire j start ops _ hv, polynomialInputs_value]
    · dsimp only
      rw [liftModel_before wire j start ops _ hd, polynomialInputs_derivative]
  exact ⟨eq_of_eval_complex _ _ (fun x => (heval x).1), eq_of_eval_complex _ _ (fun x => (heval x).2)⟩

def secondProgram (start : ℕ) (ops : List Operation) : List Operation :=
  program (valueWire start) (program start ops)

theorem secondProgram_length (start : ℕ) (ops : List Operation) :
    (secondProgram start ops).length = 16 * ops.length := by
  simp only [secondProgram, program_length]
  omega

theorem second_wellFormed (start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed start ops) :
    StraightLine.WellFormed (valueWire (valueWire start)) (secondProgram start ops) :=
  wellFormed _ _ (wellFormed start ops hw)

def SecondAgrees {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j k : σ) (x : σ → ℂ) (env : ℕ → ℂ)
    (i : ℕ) : Prop :=
  env (valueWire (valueWire i)) = (wire i).eval₂ (Int.castRingHom ℂ) x ∧
  env (derivativeWire (valueWire i)) = (pderiv k (wire i)).eval₂ (Int.castRingHom ℂ) x ∧
  env (valueWire (derivativeWire i)) = (pderiv j (wire i)).eval₂ (Int.castRingHom ℂ) x ∧
  env (derivativeWire (derivativeWire i)) = (pderiv k (pderiv j (wire i))).eval₂ (Int.castRingHom ℂ) x

theorem second_sound {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j k : σ) (x : σ → ℂ)
    (start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed start ops) (hr : Realizes wire start ops)
    (env : ℕ → ℂ) (hi : ∀ q < valueWire start, Agrees (polynomialInputs wire j) k x env q)
    (hg : ∀ g ∈ StraightLine.gates (valueWire (valueWire start)) (secondProgram start ops), g.Holds env) :
    ∀ i < start + ops.length, SecondAgrees wire j k x env i := by
  have hin : ∀ q < valueWire start, Agrees (liftModel wire j start ops) k x env q := by
    intro q hq
    simpa only [Agrees, liftModel_before wire j start ops q hq] using hi q hq
  have hout := sound (liftModel wire j start ops) k x (valueWire start) (program start ops)
    (wellFormed start ops hw) (liftModel_realizes wire j start ops hw) env hin hg
  intro i hbound
  have hv : valueWire i < valueWire start + (program start ops).length := by
    rw [program_length]; unfold valueWire; omega
  have hd : derivativeWire i < valueWire start + (program start ops).length := by
    rw [program_length]; unfold valueWire derivativeWire; omega
  have hcorrect := liftModel_correct wire j start ops hw hr i hbound
  have hvalue := hout (valueWire i) hv
  have hderivative := hout (derivativeWire i) hd
  simp only [Agrees, hcorrect.1] at hvalue
  simp only [Agrees, hcorrect.2] at hderivative
  exact ⟨hvalue.1, hvalue.2, hderivative.1, hderivative.2⟩

theorem second_exists_completion {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j k : σ) (x : σ → ℂ)
    (start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed start ops) (hr : Realizes wire start ops)
    (env : ℕ → ℂ) (hi : ∀ q < valueWire start, Agrees (polynomialInputs wire j) k x env q) :
    ∃ out : ℕ → ℂ, (∀ q < valueWire (valueWire start), out q = env q) ∧
      (∀ g ∈ StraightLine.gates (valueWire (valueWire start)) (secondProgram start ops), g.Holds out) ∧
      ∀ i < start + ops.length, SecondAgrees wire j k x out i := by
  obtain ⟨out, hp, hg⟩ := StraightLine.exists_completion env (valueWire (valueWire start))
    (secondProgram start ops) (second_wellFormed start ops hw)
  refine ⟨out, hp, hg, second_sound wire j k x start ops hw hr out ?_ hg⟩
  intro q hq
  have hv : valueWire q < valueWire (valueWire start) := by unfold valueWire at *; omega
  have hd : derivativeWire q < valueWire (valueWire start) := by unfold valueWire derivativeWire at *; omega
  exact ⟨(hp _ hv).trans (hi q hq).1, (hp _ hd).trans (hi q hq).2⟩

theorem second_encode_mem_FP {start : List Bool → ℕ} {ops : List Bool → List Operation}
    (hq : (fun c => encode (StraightLine.gates (start c) (ops c))) ∈ FP) :
    (fun c => encode (StraightLine.gates (valueWire (valueWire (start c)))
      (secondProgram (start c) (ops c)))) ∈ FP :=
  program_encode_mem_FP (program_encode_mem_FP hq)

end LeanCanny.ETR.ComplexCircuit.Differential
