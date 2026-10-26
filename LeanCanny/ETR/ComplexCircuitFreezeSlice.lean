/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitFreezeEncoding
public import LeanCanny.Algebra.CoordinateSlicePolynomial

/-! # Exact coordinate slices at parameter-wire values

The parameter value can be any element of the evaluation ring. It is not
serialized as a coefficient. This identifies the shared circuit's output
with the actual coordinate slice, including irrational real parameter values.
Generating the formulas that select those values is a separate obligation.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.CircuitFreeze
open MvPolynomial LeanCanny.Algebra

theorem eval_substitution {K : Type*} [CommRing K] (φ : ℤ →+* K) (parameter : ℕ)
    (p : MvPolynomial ℕ ℤ) (x : ℕ → K) :
    (substitution parameter p).eval₂ φ x = p.eval₂ φ (fun i => if i = 0 then x parameter else x (i - 1)) := by
  induction p using MvPolynomial.induction_on with
  | C z =>
    rw [substitution, eval₂Hom_C, eval₂_C, eval₂_C]
  | add p q hp hq => simpa only [map_add, eval₂_add] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    rw [map_mul, eval₂_mul, hp, eval₂_mul, eval₂_X]
    congr 1
    by_cases hi : i = 0 <;> simp [substitution, hi]

theorem eval_slice {n : ℕ} {K : Type*} [CommRing K] (φ : ℤ →+* K) (parameter : ℕ)
    (q : MvPolynomial (Fin (n + 1)) ℤ) (x : ℕ → K) :
    (substitution parameter (rename Fin.val q)).eval₂ φ x =
      (CoordinateSlicePolynomial.family q).eval₂ (Polynomial.eval₂RingHom φ (x parameter)) (fun j => x j.val) := by
  rw [eval_substitution, eval₂_rename, CoordinateSlicePolynomial.eval_family]
  apply congrArg (q.eval₂ φ)
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simp

theorem symbolic_eval_slice {n : ℕ} {K : Type*} [CommRing K] (φ : ℤ →+* K)
    (inputs parameter start out : ℕ) (ops : List Operation) (q : MvPolynomial (Fin (n + 1)) ℤ)
    (hsource : Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) inputs ops out = rename Fin.val q)
    (hw : StraightLine.WellFormed inputs ops) (hp : parameter < start) (hs : inputs ≤ start + 1)
    (ho : out < inputs + ops.length) (x : ℕ → K) :
    (Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) start (program inputs parameter start ops)
      (output inputs parameter start out)).eval₂ φ x =
        (CoordinateSlicePolynomial.family q).eval₂ (Polynomial.eval₂RingHom φ (x parameter)) (fun j => x j.val) := by
  rw [symbolic_output inputs parameter start out ops hw hp hs ho, hsource]
  exact eval_slice φ parameter q x

end LeanCanny.ETR.ComplexCircuit.CircuitFreeze
