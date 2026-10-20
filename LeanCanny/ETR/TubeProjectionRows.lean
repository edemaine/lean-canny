/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionTermSpace

/-! # Projection rows assembled from certified coefficient terms

The level row is one unshifted source term. Each partial row is one embedded
partial derivative minus the base partial derivative times a direction variable.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeProjectionQuery
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding TubeProjectionEncoding
open Algebra.MatrixPower

theorem integerProjection_level_term (n : ℕ) (p : MvPolynomial (Fin n) ℤ) (s : Finset (Constraint n)) :
    TubePolynomial.integerProjection p s none =
      termPolynomial n (TubePolynomial.integerPolynomial p s) (.inl (TubePolynomial.base (Fin n))) none false := by
  have h := Algebra.ProjectionFlatten.level (TubePolynomial.polynomial p s) (TubePolynomial.base (Fin n))
  change TubePolynomial.integerProjection p s none = _ at h
  rw [h]
  simp only [termPolynomial, Bool.false_eq_true, ite_false, shiftVector, MvPolynomial.monomial_zero', map_one, mul_one]
  rfl

theorem integerProjection_partial_terms (n : ℕ) (p : MvPolynomial (Fin n) ℤ) (s : Finset (Constraint n))
    (i : {i : Point n // i ≠ TubePolynomial.base (Fin n)}) :
    TubePolynomial.integerProjection p s (some i) =
      termPolynomial n (TubePolynomial.integerPolynomial p s) (.inl i.val) none true -
        termPolynomial n (TubePolynomial.integerPolynomial p s) (.inl (TubePolynomial.base (Fin n))) (some i.val) true := by
  have h := Algebra.ProjectionFlatten.partial_eq (TubePolynomial.polynomial p s) (TubePolynomial.base (Fin n)) i.val
  change TubePolynomial.integerProjection p s (some i) = _ at h
  rw [h]
  simp only [termPolynomial, ite_true, shiftVector, MvPolynomial.monomial_zero', map_one, mul_one]
  change _ - (MvPolynomial.X (.inl (.inr i.val)) : MvPolynomial (Variable n) ℤ) * _ = _ - _ * (MvPolynomial.X (.inl (.inr i.val)) : MvPolynomial (Variable n) ℤ)
  rw [mul_comm (MvPolynomial.X _)]
  rfl

attribute [local irreducible] TubeDense.polynomial TubePolynomial.integerPolynomial
  TubePolynomial.integerProjection termValue ArithmeticBits.addMod ArithmeticBits.negate

noncomputable def rowValue (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active target modulus : List Bool → List Bool)
    (row : ∀ c, TubePolynomial.ProjectionIndex (Fin (TubeDense.arity base c))) (c : List Bool) : List Bool :=
  residueBits (((TubePolynomial.integerProjection (TubeDense.polynomial base c)
    (activeSet (TubeDense.arity base c) (active c)) (row c)).coeff (exponent (TubeDense.arity base) W target c) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus c) + 1))

noncomputable def levelEvaluator (base : List Bool → List Bool) (W : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (hb : base ∈ FP) (hW : UnaryFn W)
    (ha : active ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (rowValue base W active target modulus (fun _ => none)) := by
  let n := TubeDense.arity base
  let E := termEvaluator base W n n active target modulus false false
    (fun c => .inl (TubePolynomial.base (Fin (n c)))) (fun _ => none)
    hb hW (TubeDense.arity_unary hb) (TubeDense.arity_unary hb) ha ht hm
    (fun c => (index_shift_source_false (n c)).symm) (fun _ => rfl)
  refine E.congr (funext fun c => ?_)
  unfold termValue rowValue
  rw [integerProjection_level_term]

/-- Subtract two canonical residue responses while retaining their input. -/
def subtractResponses (modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (TubeCombine.modulus modulus z)
    (pair (pairFst (pairSnd z)) (ArithmeticBits.negate (pair (TubeCombine.modulus modulus z) (pairSnd (pairSnd z))))))

theorem subtractResponses_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : subtractResponses modulus ∈ FP := by
  have hmod := TubeCombine.modulus_mem_FP hm
  have hx := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hy := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hn := mem_FP_comp (mem_FP_pair hmod hy) ArithmeticBits.negate_mem_FP
  have h := mem_FP_comp (mem_FP_pair hmod (mem_FP_pair hx hn)) ArithmeticBits.addMod_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem subtractResponses_residueBits (modulus : List Bool → List Bool) (c : List Bool)
    (x y : ZMod (Nat.fromBitsLE (modulus c) + 1)) :
    subtractResponses modulus (pair c (pair (residueBits x) (residueBits y))) = residueBits (x - y) := by
  let : NeZero (Nat.fromBitsLE (modulus c) + 1) := ⟨by omega⟩
  simp only [subtractResponses, TubeCombine.modulus, pairFst_pair, pairSnd_pair, BinaryNat.succ_eq_bits]
  change ArithmeticBits.addMod (pair (BinaryNatCode.encode (Nat.fromBitsLE (modulus c) + 1))
    (pair (residueBits x) (ArithmeticBits.negate (pair (BinaryNatCode.encode (Nat.fromBitsLE (modulus c) + 1)) (residueBits y))))) = _
  rw [ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits, sub_eq_add_neg]

attribute [local irreducible] subtractResponses

noncomputable def partialEvaluator (base : List Bool → List Bool) (W r : List Bool → ℕ)
    (active target modulus : List Bool → List Bool)
    (i : ∀ c, {i : Point (TubeDense.arity base c) // i ≠ TubePolynomial.base (Fin (TubeDense.arity base c))})
    (hb : base ∈ FP) (hW : UnaryFn W) (hr : UnaryFn r) (ha : active ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (hi : ∀ c, r c = (pointEquiv (TubeDense.arity base c) (i c).val).val) :
    SpaceFunction (rowValue base W active target modulus (fun c => some (i c))) := by
  let n := TubeDense.arity base
  let A := termEvaluator base W r r active target modulus true false
    (fun c => .inl (i c).val) (fun _ => none)
    hb hW hr hr ha ht hm (fun c => (hi c).trans (tube_index_point (n c) (i c).val).symm) (fun _ => rfl)
  let B := termEvaluator base W n r active target modulus true true
    (fun c => .inl (TubePolynomial.base (Fin (n c)))) (fun c => some (i c).val)
    hb hW (TubeDense.arity_unary hb) hr ha ht hm
    (fun c => (index_shift_source_false (n c)).symm) (fun c => congrArg some (hi c))
  let E := (A.pairOutputs B).withInput.postcompose (subtractResponses modulus) (subtractResponses_mem_FP hm)
  refine E.congr (funext fun c => ?_)
  change subtractResponses modulus (pair c (pair
    (termValue base W active target modulus true (fun c => .inl (i c).val) (fun _ => none) c)
    (termValue base W active target modulus true (fun c => .inl (TubePolynomial.base (Fin (n c)))) (fun c => some (i c).val) c))) = _
  unfold termValue rowValue
  rw [subtractResponses_residueBits, integerProjection_partial_terms, MvPolynomial.coeff_sub, Int.cast_sub]

end LeanCanny.ETR.TubeProjectionQuery
