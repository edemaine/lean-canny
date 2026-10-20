/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDenseGuard
public import LeanCanny.ETR.CompactPowerCoefficient
public import LeanCanny.ETR.TermArityFP

/-! # FP metadata and a degree guard for dense tube powers

A fixed positive power retains source arity. Its written source size M gives
the genuine integer compact polynomial power a total-degree bound 4*M².
The bound and the coefficient query width have uniform FP writers.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDense
open Complexity
open LeanCanny.Encoding
open Geometry

noncomputable def arity (base : List Bool → List Bool) : List Bool → ℕ := TermArity.arity base

def powerSource (base : List Bool → List Bool) (k : ℕ) : List Bool → List Bool :=
  CompactPowerCoefficient.source base (fun _ => k)

def size (base : List Bool → List Bool) (k : ℕ) : List Bool → ℕ := CollectedCoefficient.dimension (powerSource base k)
def degreeBudget (base : List Bool → List Bool) (k : ℕ) (c : List Bool) : ℕ := 4 * size base k c ^ 2
def width (base : List Bool → List Bool) (k : ℕ) (c : List Bool) : ℕ := degreeBudget base k c + 1

noncomputable def polynomial (base : List Bool → List Bool) (c : List Bool) : MvPolynomial (Fin (arity base c)) ℤ :=
  (TermView.term (base c)).compactPolynomial

theorem arity_unary {base : List Bool → List Bool} (hb : base ∈ FP) : UnaryFn (arity base) := TermArity.arity_unary hb

theorem powerSource_mem_FP {base : List Bool → List Bool} (hb : base ∈ FP) (k : ℕ) : powerSource base k ∈ FP :=
  TermPower.write_mem_FP hb (UnaryFn.const k)

theorem size_unary {base : List Bool → List Bool} (hb : base ∈ FP) (k : ℕ) : UnaryFn (size base k) :=
  CollectedCoefficient.dimension_unary (powerSource_mem_FP hb k)

theorem degreeBudget_unary {base : List Bool → List Bool} (hb : base ∈ FP) (k : ℕ) : UnaryFn (degreeBudget base k) :=
  (UnaryFn.const 4).mul ((size_unary hb k).pow_const 2)

theorem width_unary {base : List Bool → List Bool} (hb : base ∈ FP) (k : ℕ) : UnaryFn (width base k) :=
  (degreeBudget_unary hb k).add (UnaryFn.const 1)

theorem size_eq (base : List Bool → List Bool) (k : ℕ) (c : List Bool) :
    size base k c = ((TermView.term (base c)).power k).toData.size := by
  change (TermView.normalize (TermPower.write base (fun _ => k) c)).length = _
  rw [TermPower.write_correct, TermView.normalize_toBits, Data.length_toBits]

theorem arity_le_size (base : List Bool → List Bool) (k : ℕ) (hk : 0 < k) (c : List Bool) : arity base c ≤ size base k c := by
  have h := CollectedCoefficient.arity_le_dimension (powerSource base k) c
  change (TermView.term (TermPower.write base (fun _ => k) c)).arity ≤ size base k c at h
  rw [TermPower.write_correct, TermView.term_toBits, Term.arity_power _ _ hk] at h
  exact h

theorem polynomial_power_degree (base : List Bool → List Bool) (k : ℕ) (hk : 0 < k) (c : List Bool) :
    (polynomial base c ^ k).totalDegree ≤ degreeBudget base k c := by
  have hn := arity_le_size base k hk c
  have hd : (Term.finitePolynomial (arity base c) ((TermView.term (base c)).power k)).totalDegree ≤ size base k c :=
    (Term.totalDegree_finitePolynomial _ _).trans
      (((TermView.term (base c)).power k).degreeBound_le_dataSize.trans_eq (size_eq base k c).symm)
  change (CubePolynomial.cleared (Term.finitePolynomial (arity base c) (TermView.term (base c))) ^ k).totalDegree ≤ _
  rw [← CubePolynomial.cleared_pow, ← Term.finitePolynomial_power]
  calc
    _ ≤ 4 * arity base c * (Term.finitePolynomial (arity base c) ((TermView.term (base c)).power k)).totalDegree := by
      simpa only [Fintype.card_fin] using CubePolynomial.totalDegree_le_card
        (Term.finitePolynomial (arity base c) ((TermView.term (base c)).power k))
    _ ≤ 4 * size base k c * size base k c := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hn) hd
    _ = degreeBudget base k c := by simp only [degreeBudget, pow_two, Nat.mul_assoc]

theorem budget_lt_width (base : List Bool → List Bool) (k : ℕ) (c : List Bool) :
    degreeBudget base k c < 2 ^ width base k c :=
  (Nat.lt_succ_self _).trans_le (Nat.lt_two_pow_self.le)

end LeanCanny.ETR.TubeDense
