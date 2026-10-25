/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexStraightLine
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Shared first-derivative networks

Each source operation allocates four wires: its value, two product-rule
intermediates, and its derivative. Constants and additions pad the two unused
intermediates with zero. The transformed program remains acyclic, and its
constraints force the exact formal partial derivatives of every source wire.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Differential
open MvPolynomial
open scoped Classical

def valueWire (i : ℕ) : ℕ := 4 * i
def derivativeWire (i : ℕ) : ℕ := 4 * i + 3

def operation (out : ℕ) : Operation → List Operation
  | .constant z => [.constant z, .constant 0, .constant 0, .constant 0]
  | .add left right => [.add (valueWire left) (valueWire right), .constant 0, .constant 0,
      .add (derivativeWire left) (derivativeWire right)]
  | .mul left right => [.mul (valueWire left) (valueWire right),
      .mul (derivativeWire left) (valueWire right), .mul (valueWire left) (derivativeWire right),
      .add (valueWire out + 1) (valueWire out + 2)]

noncomputable def tangent (value derivative : ℕ → ℂ) : Operation → ℂ
  | .constant _ => 0
  | .add left right => derivative left + derivative right
  | .mul left right => derivative left * value right + value left * derivative right

noncomputable def polynomial {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) : Operation → MvPolynomial σ ℤ
  | .constant z => C z
  | .add left right => wire left + wire right
  | .mul left right => wire left * wire right

theorem operation_length (out : ℕ) (op : Operation) : (operation out op).length = 4 := by cases op <;> rfl

theorem operation_wellFormed (out : ℕ) (op : Operation) (hop : op.InputsBelow out) :
    StraightLine.WellFormed (valueWire out) (operation out op) := by
  cases op <;> simp only [operation, StraightLine.WellFormed, Operation.InputsBelow,
    valueWire, derivativeWire] at *
  · exact ⟨trivial, trivial, trivial, trivial, trivial⟩
  · exact ⟨⟨by omega, by omega⟩, trivial, trivial, ⟨by omega, by omega⟩, trivial⟩
  · exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
      ⟨by omega, by omega⟩, trivial⟩

theorem operation_sound (out : ℕ) (op : Operation) (env : ℕ → ℂ)
    (h : ∀ g ∈ StraightLine.gates (valueWire out) (operation out op), g.Holds env) :
    env (valueWire out) = op.eval (fun i => env (valueWire i)) ∧
      env (derivativeWire out) = tangent (fun i => env (valueWire i))
        (fun i => env (derivativeWire i)) op := by
  cases op <;> simp only [operation, StraightLine.gates, Operation.gate,
    List.forall_mem_cons, Gate.Holds, Int.cast_zero] at h
  · exact ⟨h.1, h.2.2.2.1⟩
  · exact ⟨h.1, h.2.2.2.1⟩
  · exact ⟨h.1, h.2.2.2.1.trans (congrArg₂ (· + ·) h.2.1 h.2.2.1)⟩

theorem polynomial_eval {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (op : Operation) (x : σ → ℂ) :
    (polynomial wire op).eval₂ (Int.castRingHom ℂ) x =
      op.eval (fun i => (wire i).eval₂ (Int.castRingHom ℂ) x) := by
  cases op <;> simp only [polynomial, Operation.eval, eval₂_C, eval₂_add, eval₂_mul, Int.coe_castRingHom]

theorem polynomial_derivative_eval {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ)
    (op : Operation) (j : σ) (x : σ → ℂ) :
    (pderiv j (polynomial wire op)).eval₂ (Int.castRingHom ℂ) x =
      tangent (fun i => (wire i).eval₂ (Int.castRingHom ℂ) x)
        (fun i => (pderiv j (wire i)).eval₂ (Int.castRingHom ℂ) x) op := by
  cases op <;> simp only [polynomial, tangent, pderiv_C, map_add, pderiv_mul, eval₂_zero,
    eval₂_add, eval₂_mul]

def program : ℕ → List Operation → List Operation
  | _, [] => []
  | start, op :: ops => operation start op ++ program (start + 1) ops

theorem program_length (start : ℕ) (ops : List Operation) : (program start ops).length = 4 * ops.length := by
  induction ops generalizing start with
  | nil => rfl
  | cons op ops ih => simp only [program, List.length_append, operation_length, ih, List.length_cons]; omega

theorem wellFormed (start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed start ops) :
    StraightLine.WellFormed (valueWire start) (program start ops) := by
  induction ops generalizing start with
  | nil => trivial
  | cons op ops ih =>
    rw [program, StraightLine.wellFormed_append, operation_length]
    refine ⟨operation_wellFormed start op hw.1, ?_⟩
    rw [show valueWire start + 4 = valueWire (start + 1) by unfold valueWire; omega]
    exact ih (start + 1) hw.2

def Realizes {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) : ℕ → List Operation → Prop
  | _, [] => True
  | start, op :: ops => wire start = polynomial wire op ∧ Realizes wire (start + 1) ops

def Agrees {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j : σ) (x : σ → ℂ) (env : ℕ → ℂ) (i : ℕ) : Prop :=
  env (valueWire i) = (wire i).eval₂ (Int.castRingHom ℂ) x ∧
    env (derivativeWire i) = (pderiv j (wire i)).eval₂ (Int.castRingHom ℂ) x

noncomputable def symbolicRun {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) :
    ℕ → List Operation → ℕ → MvPolynomial σ ℤ
  | _, [] => wire
  | start, op :: ops => symbolicRun (Function.update wire start (polynomial wire op)) (start + 1) ops

theorem symbolicRun_preserves_before {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ)
    (start : ℕ) (ops : List Operation) (i : ℕ) (hi : i < start) :
    symbolicRun wire start ops i = wire i := by
  induction ops generalizing wire start with
  | nil => rfl
  | cons op ops ih =>
    rw [symbolicRun, ih _ _ (by omega)]
    exact Function.update_of_ne (show i ≠ start by omega) _ _

theorem polynomial_congr {σ : Type*} (wire wire' : ℕ → MvPolynomial σ ℤ)
    (start : ℕ) (op : Operation) (hop : op.InputsBelow start)
    (h : ∀ i < start, wire i = wire' i) : polynomial wire op = polynomial wire' op := by
  cases op with
  | constant z => rfl
  | add left right => simp only [polynomial, h left hop.1, h right hop.2]
  | mul left right => simp only [polynomial, h left hop.1, h right hop.2]

theorem symbolicRun_realizes {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ)
    (start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed start ops) :
    Realizes (symbolicRun wire start ops) start ops := by
  induction ops generalizing wire start with
  | nil => trivial
  | cons op ops ih =>
    refine ⟨?_, ih _ _ hw.2⟩
    have ho : symbolicRun wire start (op :: ops) start = polynomial wire op := by
      rw [symbolicRun, symbolicRun_preserves_before _ (start + 1) ops start (by omega), Function.update_self]
    have hp : ∀ i < start, symbolicRun wire start (op :: ops) i = wire i :=
      fun i hi => symbolicRun_preserves_before wire start (op :: ops) i hi
    exact ho.trans (polynomial_congr _ wire start op hw.1 hp).symm

theorem sound {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j : σ) (x : σ → ℂ)
    (start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed start ops)
    (hp : Realizes wire start ops) (env : ℕ → ℂ)
    (hi : ∀ i < start, Agrees wire j x env i)
    (hg : ∀ g ∈ StraightLine.gates (valueWire start) (program start ops), g.Holds env) :
    ∀ i < start + ops.length, Agrees wire j x env i := by
  induction ops generalizing start with
  | nil => simpa only [List.length_nil, Nat.add_zero] using hi
  | cons op ops ih =>
    have hstep : ∀ g ∈ StraightLine.gates (valueWire start) (operation start op), g.Holds env := by
      intro g h
      apply hg g
      rw [program, StraightLine.gates_append]
      exact List.mem_append_left _ h
    have hout := operation_sound start op env hstep
    have hv : op.eval (fun i => env (valueWire i)) =
        op.eval (fun i => (wire i).eval₂ (Int.castRingHom ℂ) x) :=
      Operation.eval_congr op start _ _ hw.1 (fun i h => (hi i h).1)
    have hd : tangent (fun i => env (valueWire i)) (fun i => env (derivativeWire i)) op =
        tangent (fun i => (wire i).eval₂ (Int.castRingHom ℂ) x)
          (fun i => (pderiv j (wire i)).eval₂ (Int.castRingHom ℂ) x) op := by
      cases op with
      | constant z => rfl
      | add l r => simp only [tangent, (hi l hw.1.1).2, (hi r hw.1.2).2]
      | mul l r => simp only [tangent, (hi l hw.1.1).1, (hi r hw.1.2).1, (hi l hw.1.1).2, (hi r hw.1.2).2]
    have hs : Agrees wire j x env start := by
      constructor
      · rw [hp.1, polynomial_eval]
        exact hout.1.trans hv
      · rw [hp.1, polynomial_derivative_eval]
        exact hout.2.trans hd
    have hnext : ∀ i < start + 1, Agrees wire j x env i := by
      intro i h
      by_cases hlt : i < start
      · exact hi i hlt
      · have he : i = start := by omega
        simpa only [he] using hs
    have htail : ∀ g ∈ StraightLine.gates (valueWire (start + 1)) (program (start + 1) ops), g.Holds env := by
      intro g h
      apply hg g
      rw [program, StraightLine.gates_append, operation_length,
        show valueWire start + 4 = valueWire (start + 1) by unfold valueWire; omega]
      exact List.mem_append_right _ h
    have h := ih (start + 1) hw.2 hp.2 hnext htail
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using h

theorem exists_completion {σ : Type*} (wire : ℕ → MvPolynomial σ ℤ) (j : σ) (x : σ → ℂ)
    (start : ℕ) (ops : List Operation) (hw : StraightLine.WellFormed start ops)
    (hp : Realizes wire start ops) (env : ℕ → ℂ) (hi : ∀ i < start, Agrees wire j x env i) :
    ∃ out : ℕ → ℂ, (∀ i < valueWire start, out i = env i) ∧
      (∀ g ∈ StraightLine.gates (valueWire start) (program start ops), g.Holds out) ∧
      ∀ i < start + ops.length, Agrees wire j x out i := by
  obtain ⟨out, he, hg⟩ := StraightLine.exists_completion env (valueWire start) (program start ops)
    (wellFormed start ops hw)
  refine ⟨out, he, hg, sound wire j x start ops hw hp out ?_ hg⟩
  intro i h
  have hv : valueWire i < valueWire start := by unfold valueWire; omega
  have hd : derivativeWire i < valueWire start := by unfold derivativeWire valueWire; omega
  exact ⟨(he _ hv).trans (hi i h).1, (he _ hd).trans (hi i h).2⟩

end LeanCanny.ETR.ComplexCircuit.Differential
