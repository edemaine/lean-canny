/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.TermEvaluationContext
public import LeanCanny.ETR.PolynomialMass

/-! # Controlled polynomials from polynomial-time encoded expression trees -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.TermEvaluation

open LeanCanny.Encoding LeanCanny.ETR Turing.MultiTapeTM MvPolynomial
open Cslib.Complexity

theorem eval_finitePolynomial_ring {R : Type*} [CommRing R] (t : Term) (n : ℕ) (y : Fin n → R) :
    (t.finitePolynomial n).eval₂ (Int.castRingHom R) y =
      t.eval (fun i => if h : i < n then y ⟨i, h⟩ else 0) := by
  induction t with
  | const z => simp only [Term.finitePolynomial, eval₂_C, Int.coe_castRingHom, Term.eval]
  | var i => by_cases hi : i < n <;> simp only [Term.finitePolynomial, hi, ↓reduceDIte,
      eval₂_X, eval₂_zero, Term.eval]
  | add t u ht hu => simp only [Term.finitePolynomial, eval₂_add, ht, hu, Term.eval]
  | mul t u ht hu => simp only [Term.finitePolynomial, eval₂_mul, ht, hu, Term.eval]

def arity (source : List Bool → List Bool) (w : List Bool) : ℕ :=
  (TermView.normalize (source w)).length

noncomputable def polynomial (source : List Bool → List Bool) (w : List Bool) :
    MvPolynomial (Fin (arity source w)) ℤ := (TermView.term (source w)).finitePolynomial (arity source w)

theorem arity_eq (source : List Bool → List Bool) (w : List Bool) :
    arity source w = (TermView.term (source w)).toData.size := by
  rw [arity, TermView.normalize_eq_term, LeanCanny.Data.length_toBits]

theorem arity_unary (source : List Bool → List Bool) (hs : source ∈ FP) : UnaryFn (arity source) :=
  UnaryFn.length (mem_FP_comp hs TermView.normalize_mem_FP)

theorem eval_polynomial {R : Type*} [CommRing R] (source : List Bool → List Bool)
    (w : List Bool) (y : ℕ → R) :
    (polynomial source w).eval₂ (Int.castRingHom R) (fun i => y i.val) =
      (TermView.term (source w)).eval y := by
  rw [polynomial, eval_finitePolynomial_ring]
  apply Term.eval_congr
  intro i hi
  have hn : i < arity source w := hi.trans_le (by rw [arity_eq]; exact Term.arity_le_dataSize _)
  simp only [hn, ↓reduceDIte]

noncomputable def controlled (source : List Bool → List Bool) (hs : source ∈ FP) :
    Controlled (polynomial source) encBits 0 where
  arity_computable := (arity_unary source hs).computableInPolyTime
  degreeBound := arity source
  degree_computable := (BinaryFn.ofUnary (arity_unary source hs)).computableInPolyTime
  degree_le w := (Term.totalDegree_finitePolynomial _ _).trans (by
    rw [arity_eq]; exact Term.degreeBound_le_dataSize _)
  massExponent := arity source
  mass_computable := (BinaryFn.ofUnary (arity_unary source hs)).computableInPolyTime
  mass_le w := by rw [polynomial, arity_eq]; exact Term.finitePolynomial_mass _ _
  cutoff := fun _ => 0
  cutoff_computable := .const 0
  evaluate := evaluate source
  evaluate_mem := CountingFunction.of_polyTime (evaluate_polyTime source hs)
  evaluate_eq w p z hp _ := by
    let : Fact p.Prime := ⟨hp⟩
    let : NeZero p := ⟨hp.ne_zero⟩
    have heval := evaluate_cast source w p z
    have hpoly := eval_polynomial source w (fun i => (z[i]?.getD 0 : ZMod p))
    have hv := congrArg ZMod.val (heval.trans hpoly.symm)
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (evaluate_lt source w p z hp), evaluation] using hv

theorem feasible_iff (source : List Bool → List Bool) (w : List Bool) :
    (∃ y : Fin (arity source w) → ℝ, (polynomial source w).eval₂ (Int.castRingHom ℝ) y = 0) ↔
      ∃ env : ℕ → ℝ, (TermView.term (source w)).eval env = 0 := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Formula.extend y, ?_⟩
    exact (Term.eval_finitePolynomial _ _ _).symm.trans hy
  · rintro ⟨env, he⟩
    exact ⟨fun i => env i.val, (eval_polynomial source w env).trans he⟩

end LeanCanny.CountingHierarchy.TermEvaluation
