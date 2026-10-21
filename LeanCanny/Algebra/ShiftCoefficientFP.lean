/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BinomialResidue
public import LeanCanny.Algebra.ModularPowFP
public import LeanCanny.Computation.SpaceFunctionComposition

/-!
# Encoded assembly of a shifted-polynomial coefficient residue

Input `pair q (pair i j)` retains modular context `q`. The binomial child is
prepared with indices `i+j,i`. Its result is multiplied by the accessed input
coefficient and the modular power of the negative direction. All preparation
and final arithmetic are FP; the binomial computation uses certified space.
-/

@[expose] public section

namespace LeanCanny.Algebra.ShiftCoefficientBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower

structure Access where
  direction : List Bool → List Bool
  coefficient : List Bool → List Bool

structure Access.PolyTime (a : Access) : Prop where
  direction : a.direction ∈ FP
  coefficient : a.coefficient ∈ FP

def leftIndex (p : List Bool) : List Bool := pairFst (pairSnd p)
def rightIndex (p : List Bool) : List Bool := pairSnd (pairSnd p)
def original (p : List Bool) : List Bool := pairFst (pairFst p)
def modulusMinusOne (p : List Bool) : List Bool := pairSnd (pairFst p)
def modulus (p : List Bool) : List Bool := BinaryNat.succ (modulusMinusOne p)
def sumIndex (p : List Bool) : List Bool := BinaryNat.add (pair (leftIndex p) (rightIndex p))
def coefficientInput (p : List Bool) : List Bool := pair (pairFst p) (sumIndex p)
def binomialInput (p : List Bool) : List Bool :=
  pair (sumIndex p) (pair (leftIndex p) (modulusMinusOne p))

def negativeDirection (a : Access) (p : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (modulus p) (a.direction (original p)))

def powerInput (a : Access) (p : List Bool) : List Bool :=
  pair (negativeDirection a p) (pair (leftIndex p) (modulusMinusOne p))

def factor (a : Access) (p : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (modulus p)
    (pair (a.coefficient (coefficientInput p)) (BinaryNat.powMod (powerInput a p))))

def finish (a : Access) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (modulus (pairFst z)) (pair (pairSnd z) (factor a (pairFst z))))

def computed (a : Access) (p : List Bool) : List Bool :=
  finish a (pair p (BinomialResidue.value (binomialInput p)))

theorem leftIndex_mem_FP : leftIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem rightIndex_mem_FP : rightIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem original_mem_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem modulusMinusOne_mem_FP : modulusMinusOne ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

theorem modulus_mem_FP : modulus ∈ FP := by
  have h := mem_FP_comp modulusMinusOne_mem_FP BinaryNat.succ_mem_FP
  exact h

theorem sumIndex_mem_FP : sumIndex ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair leftIndex_mem_FP rightIndex_mem_FP) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := sumIndex) h ?_
  intro p
  simp only [Function.comp_apply, sumIndex]

theorem coefficientInput_mem_FP : coefficientInput ∈ FP := by
  have h := mem_FP_pair pairFst_mem_FP sumIndex_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem binomialInput_mem_FP : binomialInput ∈ FP := by
  have h := mem_FP_pair sumIndex_mem_FP (mem_FP_pair leftIndex_mem_FP modulusMinusOne_mem_FP)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem negativeDirection_mem_FP (a : Access) (ha : a.PolyTime) : negativeDirection a ∈ FP := by
  have hd := mem_FP_comp original_mem_FP ha.direction
  have h := mem_FP_comp (mem_FP_pair modulus_mem_FP hd) ArithmeticBits.negate_mem_FP
  refine mem_FP_of_eq (g := negativeDirection a) h ?_
  intro p
  simp only [Function.comp_apply, negativeDirection]

theorem powerInput_mem_FP (a : Access) (ha : a.PolyTime) : powerInput a ∈ FP := by
  have h := mem_FP_pair (negativeDirection_mem_FP a ha) (mem_FP_pair leftIndex_mem_FP modulusMinusOne_mem_FP)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem factor_mem_FP (a : Access) (ha : a.PolyTime) : factor a ∈ FP := by
  have hc := mem_FP_comp coefficientInput_mem_FP ha.coefficient
  have hp := mem_FP_comp (powerInput_mem_FP a ha) BinaryNat.powMod_mem_FP
  have h := mem_FP_comp (mem_FP_pair modulus_mem_FP (mem_FP_pair hc hp)) BinaryNat.mulMod_mem_FP
  refine mem_FP_of_eq (g := factor a) h ?_
  intro p
  simp only [Function.comp_apply, factor]

theorem finish_mem_FP (a : Access) (ha : a.PolyTime) : finish a ∈ FP := by
  have hm := mem_FP_comp pairFst_mem_FP modulus_mem_FP
  have hf := mem_FP_comp pairFst_mem_FP (factor_mem_FP a ha)
  have h := mem_FP_comp (mem_FP_pair hm (mem_FP_pair pairSnd_mem_FP hf)) BinaryNat.mulMod_mem_FP
  refine mem_FP_of_eq (g := finish a) h ?_
  intro p
  simp only [Function.comp_apply, finish]

theorem evaluator (a : Access) (ha : a.PolyTime) : SpaceFunction (computed a) := by
  have E := ((BinomialResidue.evaluator.precompose binomialInput binomialInput_mem_FP).withInput).postcompose
    (finish a) (finish_mem_FP a ha)
  refine E.congr (g := computed a) ?_
  funext p
  simp only [Function.comp_apply, computed]

end LeanCanny.Algebra.ShiftCoefficientBits
