/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineRowIdentity
public import LeanCanny.Encoding.FlatAffineRowSourceReaders
public import LeanCanny.Encoding.FlatAffineRowLevelReader

/-! # Complete native coefficients of positively completed affine towers

Every selected row of the actual indexed tower is read from the original
source and the charged direction and ancestral-level records. The dummy row
also covers depth zero. Caller exponent widths are arbitrary unary controls;
the source derivative uses its own derived safe width.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineFullSourcePositiveCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineRowLayout FlatAffineRowAccess FlatAffineRowLinearReaders FlatAffineRowPolynomials
open FlatAffineRowSourceReaders (old guard derivativePolynomial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def value (F : Inputs) (W : List Bool → ℕ)
    (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))
    (target modulus : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthRowBits.value (FlatAffineFullSourcePositive.count F) W
    (fun u => FlatAffineFullSourcePositive.system F u (row u)) target modulus

theorem gradient_evaluator {F : Inputs} (h : F.Access)
    {row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)} (hr : UnaryFn (fun u => (row u).val))
    {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (hW : UnaryFn W) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (read F W target modulus (guard F row (gradient F row))) := by
  have hd := FlatAffineRowSourceReaders.derivative_evaluator h hr hW ht hm
  have hmu := mu_evaluator h hr hW ht hm
  have hg := FixedWidthRowBits.guarded_evaluator (FlatAffineFullSourcePositive.count F) W (muPolynomial F row)
    target modulus (read F W target modulus (muPolynomial F row)) (old F row)
    (FlatAffineRowSourceReaders.old_FP h hr) hmu (fun _ _ => rfl)
  have H := FixedWidthRowBits.sub_evaluator (FlatAffineFullSourcePositive.count F) W _ _ target modulus hm hd hg
  have he : (fun u => guard F row (derivativePolynomial F row) u - guard F row (muPolynomial F row) u) =
      guard F row (gradient F row) := by
    funext u
    by_cases hc : old F row u
    · simp only [FlatAffineRowSourceReaders.guard, hc, ite_true]
      rfl
    · simp only [FlatAffineRowSourceReaders.guard, hc, ite_false, sub_self]
  exact H.congr (congrArg (fun p => FixedWidthRowBits.value (FlatAffineFullSourcePositive.count F) W p target modulus) he)

theorem evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (hr : UnaryFn (fun u => (row u).val))
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value F W row target modulus) := by
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
        if slot F row u = arity F u then guard F row (source F row) u else levelRow F row u)
      else X (Fin.last (FlatAffineFullSourceTower.count F u))) = polynomial F row := by
    funext u
    by_cases hc : old F row u
    · unfold FlatAffineRowSourceReaders.old at hc
      simp only [FlatAffineRowSourceReaders.guard, FlatAffineRowPolynomials.polynomial,
        FlatAffineRowSourceReaders.old, hc, ite_true]
    · unfold FlatAffineRowSourceReaders.old at hc
      simp only [FlatAffineRowSourceReaders.guard, FlatAffineRowPolynomials.polynomial,
        FlatAffineRowSourceReaders.old, hc, ite_false]
  have Hp := H.congr (congrArg (fun p => FixedWidthRowBits.value (FlatAffineFullSourcePositive.count F) W p target modulus) he)
  have hrp : (fun u => FlatAffineFullSourcePositive.system F u (row u)) = polynomial F row :=
    funext (FlatAffineRowIdentity.row_eq F row)
  exact Hp.congr (congrArg (fun p => FixedWidthRowBits.value (FlatAffineFullSourcePositive.count F) W p target modulus) hrp.symm)

theorem packet (F : Inputs) (W : List Bool → ℕ)
    (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u))
    (target modulus : List Bool → List Bool) (u : List Bool) :
    value F W row target modulus u = MatrixPower.residueBits
      (((FlatAffineFullSourcePositive.system F u (row u)).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (FlatAffineFullSourcePositive.count F u))) (W u)
          (Nat.fromBitsLE (target u))) : ℤ) : ZMod (Nat.fromBitsLE (modulus u) + 1)) := rfl

end LeanCanny.Encoding.FlatAffineFullSourcePositiveCoefficient
