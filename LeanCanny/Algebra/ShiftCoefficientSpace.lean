/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ShiftCoefficientResidue

/-! # Shifted coefficients with arbitrary native space-bounded source readers

Only the direction writer is FP. The source coefficient, modular power, and
binomial children compose through native space rules with the input retained.
-/

@[expose] public section

namespace LeanCanny.Algebra.ShiftCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
attribute [local irreducible] BinaryNat.mulMod BinaryNat.powMod ArithmeticBits.negate

theorem negativeDirection_controls (a : Access) (hd : a.direction ∈ FP) : negativeDirection a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair modulus_mem_FP (mem_FP_comp original_mem_FP hd)) ArithmeticBits.negate_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem powerInput_controls (a : Access) (hd : a.direction ∈ FP) : powerInput a ∈ FP :=
  mem_FP_pair (negativeDirection_controls a hd) (mem_FP_pair leftIndex_mem_FP modulusMinusOne_mem_FP)

def finishFactor (a : Access) (q : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (modulus (pairFst q))
    (pair (pairSnd q) (BinaryNat.powMod (powerInput a (pairFst q)))))

theorem finishFactor_mem_FP (a : Access) (hd : a.direction ∈ FP) : finishFactor a ∈ FP := by
  have hm := mem_FP_comp pairFst_mem_FP modulus_mem_FP
  have hp := mem_FP_comp (mem_FP_comp pairFst_mem_FP (powerInput_controls a hd)) BinaryNat.powMod_mem_FP
  have h := mem_FP_comp (mem_FP_pair hm (mem_FP_pair pairSnd_mem_FP hp)) BinaryNat.mulMod_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem factorEvaluator (a : Access) (hd : a.direction ∈ FP) (C : SpaceFunction a.coefficient) :
    SpaceFunction (factor a) := by
  let E := (C.precompose coefficientInput coefficientInput_mem_FP).withInput.postcompose
    (finishFactor a) (finishFactor_mem_FP a hd)
  exact E.congr (funext fun p => by simp only [Function.comp_apply, finishFactor, pairFst_pair, pairSnd_pair, factor])

def finishProduct (q : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (modulus (pairFst q)) (pairSnd q))

theorem finishProduct_mem_FP : finishProduct ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP modulus_mem_FP) pairSnd_mem_FP) BinaryNat.mulMod_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem evaluatorWithCoefficient (a : Access) (hd : a.direction ∈ FP) (C : SpaceFunction a.coefficient) :
    SpaceFunction (computed a) := by
  let B := BinomialResidue.evaluator.precompose binomialInput binomialInput_mem_FP
  let E := (B.pairOutputs (factorEvaluator a hd C)).withInput.postcompose finishProduct finishProduct_mem_FP
  exact E.congr (funext fun p => by simp only [Function.comp_apply, finishProduct, pairFst_pair, pairSnd_pair, computed, finish])

theorem certifiedWithCoefficient (a : Access) (hd : a.direction ∈ FP) (C : SpaceFunction a.coefficient)
    (F : Family) (h : Represents a F) : SpaceFunction F.value := by
  refine (evaluatorWithCoefficient a hd C).congr (funext fun p => ?_)
  exact computed_correct a p (F.polynomial (original p)) (F.direction (original p)) (h.direction _)
    (fun k => h.coefficient (pairFst p) k)

end LeanCanny.Algebra.ShiftCoefficientBits
