/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionFactor
public import LeanCanny.ETR.TubeProjectionTermFormula

/-! # Polynomial-space residues of projection-row terms

FP coordinate codes select the derivative and optional direction shift. Their
native-coordinate equalities connect the complete evaluator to the actual
embedded polynomial. Rejected direction patterns return zero.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeProjectionQuery
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding TubeProjectionEncoding
open Algebra.MatrixPower

attribute [local irreducible] TubeDense.polynomial TubePolynomial.integerPolynomial productValue

noncomputable def termValue (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (derivative : Bool)
    (j : ∀ c, Coordinate (TubeDense.arity base c)) (s : ∀ c, Option (Point (TubeDense.arity base c))) (c : List Bool) : List Bool :=
  residueBits (((termPolynomial (TubeDense.arity base c)
    (TubePolynomial.integerPolynomial (TubeDense.polynomial base c) (activeSet (TubeDense.arity base c) (active c)))
      (j c) (s c) derivative).coeff (exponent (TubeDense.arity base) W target c) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

noncomputable def termEvaluator (base : List Bool → List Bool) (W r shift : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (derivative shifted : Bool)
    (j : ∀ c, Coordinate (TubeDense.arity base c)) (s : ∀ c, Option (Point (TubeDense.arity base c)))
    (hb : base ∈ FP) (hW : UnaryFn W) (hr : UnaryFn r) (hshift : UnaryFn shift)
    (ha : active ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (hj : ∀ c, r c = (coordinateEquiv (TubeDense.arity base c) (j c)).val)
    (hs : ∀ c, (if shifted then some (shift c) else none) = (s c).map (fun i => (pointEquiv (TubeDense.arity base c) i).val)) :
    SpaceFunction (termValue base W active target modulus derivative j s) := by
  classical
  let R := productEvaluator base W r active target modulus derivative hb hW hr ha ht hm
  let P := Pattern (TubeDense.arity base) W target (fun c => if shifted then some (shift c) else none)
  have hP : FPPred P := pattern_fppred (TubeDense.arity_unary hb) hW hshift ht shifted
  let E := SpaceFunction.branch (fun c => decide (P c)) hP.flag_mem_FP R
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine E.congr (funext fun c => ?_)
  have hf := coeff_termPolynomial (TubeDense.arity base) W target (fun c => if shifted then some (shift c) else none) c
    (TubePolynomial.integerPolynomial (TubeDense.polynomial base c) (activeSet (TubeDense.arity base c) (active c)))
      (j c) (s c) derivative (hs c)
  by_cases hp : P c
  · change (if decide (P c) then productValue base W r active target modulus derivative c else []) = _
    rw [ite_eq_left (show decide (P c) = true by simp only [hp, decide_true])]
    rw [productValue_correct base W r active target modulus derivative c (j c) (hj c)]
    unfold termValue
    rw [hf, ite_eq_left hp]
    simp only [Int.cast_mul, Int.cast_natCast]
  · change (if decide (P c) then productValue base W r active target modulus derivative c else []) = _
    simp only [hp, decide_false, Bool.false_eq_true, ite_false]
    unfold termValue
    rw [hf, ite_eq_right hp]
    simp [residueBits, BinaryNatCode.encode]

end LeanCanny.ETR.TubeProjectionQuery
