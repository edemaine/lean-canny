/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthExpandSpace
public import LeanCanny.Encoding.FlatAffinePowerControls
public import LeanCanny.Encoding.FlatAffineFullSourcePositiveCoefficient

/-! # Native rows of the complete affine power tower

Source derivatives and ancestral-height equations use the original readers.
Only the gradient multiplier sum is expanded by D-1. Its exponent queries
are divided in FP before invoking the charged signed-normal reader. Inactive
height rows remain linear, and the depth-zero dummy is retained.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerRowReaders
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineRowLayout FlatAffineRowAccess FlatAffineRowLinearReaders
open FlatAffineRowSourceReaders (old guard derivativePolynomial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))

noncomputable def power (u : List Bool) : ℕ := FlatAffinePowerControls.degree F u - 1

lemma power_ne_zero (u : List Bool) : power F u ≠ 0 := by
  unfold power FlatAffinePowerControls.degree BoundedFullWriter.degree BoundedSourceWriter.degree
    LeanCanny.Geometry.BoundedZeroSource.powerDegree LeanCanny.Geometry.BoundedZeroSource.powerHalfDegree
    LeanCanny.Geometry.BoundedZeroSource.degreeAllowance
  omega

theorem power_binary (h : F.source.PolyTime) : BinaryFn (power F) :=
  BinaryFn.ofUnary ((FlatAffinePowerControls.degree_unary h).sub (UnaryFn.const 1))

noncomputable def muPower (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  (muPolynomial F row u).expand (power F u)

noncomputable def gradient (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  derivativePolynomial F row u - muPower F row u

noncomputable def polynomial (u : List Bool) : MvPolynomial (Fin (FlatAffineFullSourcePositive.count F u)) ℤ :=
  if old F row u then
    if slot F row u < arity F u then gradient F row u
    else if slot F row u = arity F u then FlatAffineRowPolynomials.source F row u
      else FlatAffineRowPolynomials.levelRow F row u
  else X (Fin.last (FlatAffineFullSourceTower.count F u))

lemma muPower_eq (u : List Bool) : muPower F row u =
    ∑ j, C (FlatAffineFullSourceTower.direction F u (stage F row u) j (spatial F row u)) *
      X (multiplier F row u j) ^ power F u := by
  simp only [muPower, muPolynomial, map_sum, map_mul, expand_C, expand_X]

variable {F row}

theorem muPower_evaluator (h : F.Access) (hr : UnaryFn (fun u => (row u).val))
    {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (read F W target modulus (muPower F row)) := by
  have hp := power_binary F h.source
  have hA := FlatAffineFullSourcePositive.count_unary h
  have hq := FixedWidthExpandBits.quotientTarget_FP _ _ _ _ hA hW hp ht
  have E := FlatAffineRowLinearReaders.mu_evaluator h hr hW hq hm
  exact FixedWidthExpandBits.evaluator (FlatAffineFullSourcePositive.count F) W (power F) target
    (muPolynomial F row) modulus (power_ne_zero F) hA hW hp ht E

theorem gradient_evaluator (h : F.Access) (hr : UnaryFn (fun u => (row u).val))
    {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (read F W target modulus (guard F row (gradient F row))) := by
  have hd := FlatAffineRowSourceReaders.derivative_evaluator h hr hW ht hm
  have hmu := muPower_evaluator h hr hW ht hm
  have hg := FixedWidthRowBits.guarded_evaluator (FlatAffineFullSourcePositive.count F) W (muPower F row)
    target modulus (read F W target modulus (muPower F row)) (old F row)
    (FlatAffineRowSourceReaders.old_FP h hr) hmu (fun _ _ => rfl)
  have H := FixedWidthRowBits.sub_evaluator (FlatAffineFullSourcePositive.count F) W _ _ target modulus hm hd hg
  have he : (fun u => guard F row (derivativePolynomial F row) u - guard F row (muPower F row) u) =
      guard F row (gradient F row) := by
    funext u
    by_cases hc : old F row u
    · simp only [FlatAffineRowSourceReaders.guard, hc, ite_true]
      rfl
    · simp only [FlatAffineRowSourceReaders.guard, hc, ite_false, sub_self]
  exact H.congr (congrArg (fun p => FixedWidthRowBits.value (FlatAffineFullSourcePositive.count F) W p target modulus) he)

theorem evaluator (h : F.Access) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))
    (hr : UnaryFn (fun u => (row u).val)) {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (read F W target modulus (polynomial F row)) := by
  have hs := FlatAffineRowSourceReaders.source_evaluator h hr hW ht hm
  have hg := gradient_evaluator h hr hW ht hm
  have hl := FlatAffineRowLevelReader.evaluator h hr hW ht hm
  have hx := FixedWidthRowBits.variable_evaluator (FlatAffineFullSourcePositive.count F) W
    (fun u => Fin.last (FlatAffineFullSourceTower.count F u)) target modulus
    (FlatAffineFullSourcePositive.count_unary h) hW (FlatAffineFullSourceTower.count_unary h) ht hm
  have hi := BinaryFn.ofUnary (slot_unary h hr)
  have hn := BinaryFn.ofUnary (FlatAffineFullSourceTower.arity_unary h)
  have heq := FixedWidthRowBits.branch_evaluator (FlatAffineFullSourcePositive.count F) W _ _ target modulus
    (fun u => slot F row u = arity F u) (hi.eq hn) hs hl
  have hlt := FixedWidthRowBits.branch_evaluator (FlatAffineFullSourcePositive.count F) W _ _ target modulus
    (fun u => slot F row u < arity F u) (hi.lt hn) hg heq
  have H := FixedWidthRowBits.branch_evaluator (FlatAffineFullSourcePositive.count F) W _ _ target modulus
    (old F row) (FlatAffineRowSourceReaders.old_FP h hr) hlt hx
  have he : (fun u => if old F row u then
      (if slot F row u < arity F u then guard F row (gradient F row) u else
        if slot F row u = arity F u then guard F row (FlatAffineRowPolynomials.source F row) u
          else FlatAffineRowPolynomials.levelRow F row u)
      else X (Fin.last (FlatAffineFullSourceTower.count F u))) = polynomial F row := by
    funext u
    by_cases hc : old F row u <;> simp only [polynomial, FlatAffineRowSourceReaders.guard, hc, ite_true, ite_false]
  exact H.congr (congrArg (fun p => FixedWidthRowBits.value (FlatAffineFullSourcePositive.count F) W p target modulus) he)

end LeanCanny.Encoding.FlatAffinePowerRowReaders
