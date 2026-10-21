/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannySubresultantResidue
public import LeanCanny.Algebra.CoordinateRecovery

/-!
# Modular coordinate coefficients including linear inputs

FP source-degree tests select the direct right-linear or shifted-left-linear
coefficient routine, falling back to the certified subresultant evaluator.
The same source interface therefore computes the complete piecewise coordinate
polynomials, with original source degrees retained across modular degree drops.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyCoordinateBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower
open Polynomial
open CannyResultantBits (mValue)
open CannySubresultantBits (Family Access)

noncomputable def integerCoefficient (F : Family) (c : List Bool) : ℤ :=
  (coordinateCoefficient (F.source.left c) (F.source.right c) (F.source.direction c)
    (F.coefficient c)).coeff (F.source.degree c)

theorem integerCoefficient_eq_numerator (F : Family) (c : List Bool) (h : F.coefficient c = 0) :
    integerCoefficient F c =
      (coordinateNumerator (F.source.left c) (F.source.right c) (F.source.direction c)).coeff (F.source.degree c) := by
  simp only [integerCoefficient, h, coordinateCoefficient_zero]

theorem integerCoefficient_eq_denominator (F : Family) (c : List Bool) (h : F.coefficient c = 1) :
    integerCoefficient F c =
      (coordinateDenominator (F.source.left c) (F.source.right c) (F.source.direction c)).coeff (F.source.degree c) := by
  simp only [integerCoefficient, h, coordinateCoefficient_one]

noncomputable def value (F : Family) (q : List Bool) : List Bool :=
  residueBits (integerCoefficient F (pairFst q) : ZMod (mValue q))

def zeroLanguage (F : Family) : Language := {q | (integerCoefficient F (pairFst q) : ZMod (mValue q)) = 0}

def linearRightValue {F : Family} (a : Access F) (q : List Bool) : List Bool :=
  if a.source.degree (pairFst q) = [] then a.source.rightCoefficient (pair q (a.coefficient (pairFst q))) else []

def shiftQuery {F : Family} (a : Access F) (q : List Bool) : List Bool :=
  pair q (pair (a.coefficient (pairFst q)) (a.source.degree (pairFst q)))

theorem shiftQuery_mem_FP {F : Family} (a : Access F) (ha : a.PolyTime) : shiftQuery a ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP ha.coefficient
  have hd := mem_FP_comp pairFst_mem_FP ha.source.degree
  exact mem_FP_pair id_mem_FP (mem_FP_pair hc hd)

theorem linearRightValue_mem_FP {F : Family} (a : Access F) (ha : a.PolyTime) : linearRightValue a ∈ FP := by
  have hd := mem_FP_comp pairFst_mem_FP ha.source.degree
  have hc := mem_FP_comp pairFst_mem_FP ha.coefficient
  have hr := mem_FP_comp (mem_FP_pair id_mem_FP hc) ha.source.rightCoefficient
  have he := (stringEq_fppred hd (constFn_mem_FP [])).ite_mem_FP hr (constFn_mem_FP [])
  refine mem_FP_of_eq (g := linearRightValue a) he ?_
  intro q
  simp only [Function.comp_apply, id_eq, linearRightValue]

theorem linearRightValue_correct {F : Family} (a : Access F) (q : List Bool) :
    linearRightValue a q = residueBits
      (((C ((F.source.right (pairFst q)).coeff (F.coefficient (pairFst q))) : Polynomial ℤ).coeff
        (F.source.degree (pairFst q)) : ZMod (mValue q))) := by
  unfold linearRightValue
  rw [a.source.degree_eq, a.coefficient_eq]
  by_cases hd : F.source.degree (pairFst q) = 0
  · rw [hd]
    simp only [show BinaryNatCode.encode 0 = [] from rfl, ↓reduceIte]
    rw [a.source.rightCoefficient_eq]
    simp only [Polynomial.coeff_C_zero]
  · have hcode : BinaryNatCode.encode (F.source.degree (pairFst q)) ≠ [] := by
      intro h
      exact hd (BinaryNatCode.encode_injective
        (show BinaryNatCode.encode (F.source.degree (pairFst q)) = BinaryNatCode.encode 0 from h))
    rw [ite_eq_right hcode]
    rw [Polynomial.coeff_C, ite_eq_right hd]
    simp [residueBits, BinaryNatCode.encode]

theorem shiftValue_correct {F : Family} (a : Access F) (q : List Bool) :
    F.source.shiftSource.value (shiftQuery a q) = residueBits
      (((((shiftFamily (F.source.left (pairFst q)) (F.source.direction (pairFst q))).coeff
        (F.coefficient (pairFst q))).coeff (F.source.degree (pairFst q)) : ℤ) : ZMod (mValue q))) := by
  rw [shiftQuery, a.coefficient_eq, a.source.degree_eq, ShiftCoefficientBits.Family.value_packet]
  rfl

theorem evaluator {F : Family} (a : Access F) (ha : a.PolyTime) : SpaceFunction (value F) := by
  have L := ShiftCoefficientBits.certified a.source.shiftAccess (a.source.shift_polyTime ha.source)
    F.source.shiftSource a.source.shift_represents
  have hright := stringEq_fppred (mem_FP_comp pairFst_mem_FP ha.source.rightDegree)
    (constFn_mem_FP (BinaryNatCode.encode 1))
  have hleft := stringEq_fppred (mem_FP_comp pairFst_mem_FP ha.source.leftDegree)
    (constFn_mem_FP (BinaryNatCode.encode 1))
  let E := SpaceFunction.branch (fun q => decide (a.source.rightDegree (pairFst q) = BinaryNatCode.encode 1))
    hright.flag_mem_FP (SpaceFunction.ofFP (linearRightValue a) (linearRightValue_mem_FP a ha))
    (SpaceFunction.branch (fun q => decide (a.source.leftDegree (pairFst q) = BinaryNatCode.encode 1))
      hleft.flag_mem_FP (L.precompose (shiftQuery a) (shiftQuery_mem_FP a ha))
      (CannySubresultantBits.Access.evaluator a ha))
  refine E.congr (funext fun q => ?_)
  by_cases hn : (F.source.right (pairFst q)).natDegree = 1
  · have hword : a.source.rightDegree (pairFst q) = BinaryNatCode.encode 1 := by rw [a.source.rightDegree_eq, hn]
    simp only [hword, decide_true, ↓reduceIte]
    rw [linearRightValue_correct]
    simp only [value, integerCoefficient, coordinateCoefficient, hn, ↓reduceIte]
  · have hword : a.source.rightDegree (pairFst q) ≠ BinaryNatCode.encode 1 := by
      rw [a.source.rightDegree_eq]
      exact fun h => hn (BinaryNatCode.encode_injective h)
    simp only [Function.comp_apply, hword, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hm : (F.source.left (pairFst q)).natDegree = 1
    · have hword' : a.source.leftDegree (pairFst q) = BinaryNatCode.encode 1 := by rw [a.source.leftDegree_eq, hm]
      simp only [hword', decide_true, ↓reduceIte]
      rw [shiftValue_correct]
      simp only [value, integerCoefficient, coordinateCoefficient, hn, hm, ↓reduceIte]
    · have hword' : a.source.leftDegree (pairFst q) ≠ BinaryNatCode.encode 1 := by
        rw [a.source.leftDegree_eq]
        exact fun h => hm (BinaryNatCode.encode_injective h)
      simp only [hword', decide_false, Bool.false_eq_true, ↓reduceIte, value, integerCoefficient,
        coordinateCoefficient, hn, hm, CannySubresultantBits.Family.value,
        CannySubresultantBits.Family.integerCoefficient]

theorem decider {F : Family} (a : Access F) (ha : a.PolyTime) : SpaceDecider (zeroLanguage F) := by
  have hflag : (fun w : List Bool => [decide (w = [])]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply (evaluator a ha).decider (fun w => decide (w = [])) hflag
  intro q
  let : NeZero (mValue q) := ⟨by simp only [mValue]; omega⟩
  have hz : residueBits (0 : ZMod (mValue q)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change _ = 0 ↔ decide (residueBits _ = []) = true
  rw [decide_eq_true_eq, ← hz, (residueBits_injective (mValue q)).eq_iff]

theorem zeroLanguage_mem_PSPACE {F : Family} (a : Access F) (ha : a.PolyTime) : zeroLanguage F ∈ PSPACE :=
  (decider a ha).mem_PSPACE

end LeanCanny.Algebra.CannyCoordinateBits
