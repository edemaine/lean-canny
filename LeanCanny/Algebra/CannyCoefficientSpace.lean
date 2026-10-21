/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ShiftCoefficientSpace
public import LeanCanny.Algebra.CannyCoordinateResidue

/-! # Compositional Canny resultant and coordinate coefficient readers

Degree, direction, and coefficient-selection writers remain FP. Original
coefficient children may take arbitrary time in polynomial space. This permits
the output of an eliminant or another resultant to be used as an input.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits.Access
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Encoding.Brackets

structure ControlsPolyTime {F : Family} (a : Access F) : Prop where
  leftDegree : a.leftDegree ∈ FP
  rightDegree : a.rightDegree ∈ FP
  direction : a.direction ∈ FP
  degree : a.degree ∈ FP

theorem controls_of_polyTime {F : Family} (a : Access F) (ha : a.PolyTime) : a.ControlsPolyTime :=
  ⟨ha.leftDegree, ha.rightDegree, ha.direction, ha.degree⟩

def constantInput (p : List Bool) : List Bool := pair (pairFst p) (ShiftCoefficientBits.leftIndex p)

theorem constantInput_mem_FP : constantInput ∈ FP := mem_FP_pair pairFst_mem_FP ShiftCoefficientBits.leftIndex_mem_FP

theorem constantCoefficientEvaluator {F : Family} (a : Access F) (R : SpaceFunction a.rightCoefficient) :
    SpaceFunction a.constantCoefficient := by
  have hp := stringEq_fppred (mem_FP_comp ShiftCoefficientBits.rightIndex_mem_FP BinaryNat.normalize_mem_FP) (constFn_mem_FP [])
  let E := SpaceFunction.branch (fun p => decide (BinaryNat.normalize (ShiftCoefficientBits.rightIndex p) = []))
    hp.flag_mem_FP (R.precompose constantInput constantInput_mem_FP) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun p => by
    by_cases h : BinaryNat.normalize (ShiftCoefficientBits.rightIndex p) = [] <;>
      simp [constantCoefficient, constantInput, h])

theorem modular_controlsWithCoefficients {F : Family} (a : Access F) (ha : a.ControlsPolyTime) :
    a.modular.bits.ControlsPolyTime := by
  have hl := mem_FP_comp pairFst_mem_FP ha.leftDegree
  have hr := mem_FP_comp pairFst_mem_FP ha.rightDegree
  have hm := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have hd := mem_FP_comp pairFst_mem_FP ha.degree
  constructor
  · simpa only [modular] using hl
  · simpa only [modular] using hr
  · simpa only [modular] using hm
  · simpa only [modular] using hd

theorem evaluatorWithCoefficients {F : Family} (a : Access F) (ha : a.ControlsPolyTime)
    (L : SpaceFunction a.leftCoefficient) (R : SpaceFunction a.rightCoefficient) : SpaceFunction F.value := by
  have SL := ShiftCoefficientBits.certifiedWithCoefficient a.shiftAccess ha.direction L F.shiftSource a.shift_represents
  have E := ResultantPolynomial.ModularAccess.evaluator a.modular (a.modular_controlsWithCoefficients ha)
    SL (a.constantCoefficientEvaluator R)
  exact E.congr (funext F.modular_value)

end LeanCanny.Algebra.CannyResultantBits.Access

namespace LeanCanny.Algebra.CannySubresultantBits.Access
open LeanCanny.Encoding LeanCanny.Computation

structure ControlsPolyTime {F : Family} (a : Access F) : Prop where
  source : a.source.ControlsPolyTime
  coefficient : a.coefficient ∈ FP

theorem controls_of_polyTime {F : Family} (a : Access F) (ha : a.PolyTime) : a.ControlsPolyTime :=
  ⟨a.source.controls_of_polyTime ha.source, ha.coefficient⟩

theorem modular_controlsWithCoefficients {F : Family} (a : Access F) (ha : a.ControlsPolyTime) :
    a.modular.bits.ControlsPolyTime := by
  have hb := a.source.modular_controlsWithCoefficients ha.source
  have hc := mem_FP_comp pairFst_mem_FP ha.coefficient
  constructor
  · simpa only [modular] using hb
  · exact constFn_mem_FP _
  · simpa only [modular] using hc

theorem evaluatorWithCoefficients {F : Family} (a : Access F) (ha : a.ControlsPolyTime)
    (L : SpaceFunction a.source.leftCoefficient) (R : SpaceFunction a.source.rightCoefficient) :
    SpaceFunction F.value := by
  have SL := ShiftCoefficientBits.certifiedWithCoefficient a.source.shiftAccess ha.source.direction L
    F.source.shiftSource a.source.shift_represents
  have E := SubresultantPolynomial.ModularAccess.evaluator a.modular (a.modular_controlsWithCoefficients ha)
    SL (a.source.constantCoefficientEvaluator R)
  exact E.congr (funext F.modular_value)

end LeanCanny.Algebra.CannySubresultantBits.Access

namespace LeanCanny.Algebra.CannyCoordinateBits
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Encoding.Brackets
open CannySubresultantBits (Family Access)

def directInput {F : Family} (a : Access F) (q : List Bool) : List Bool := pair q (a.coefficient (pairFst q))

theorem directInput_mem_FP {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : directInput a ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_comp pairFst_mem_FP ha.coefficient)

theorem linearRightEvaluator {F : Family} (a : Access F) (ha : a.ControlsPolyTime)
    (R : SpaceFunction a.source.rightCoefficient) : SpaceFunction (linearRightValue a) := by
  have hp := stringEq_fppred (mem_FP_comp pairFst_mem_FP ha.source.degree) (constFn_mem_FP [])
  let E := SpaceFunction.branch (fun q => decide (a.source.degree (pairFst q) = [])) hp.flag_mem_FP
    (R.precompose (directInput a) (directInput_mem_FP a ha)) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun q => by by_cases h : a.source.degree (pairFst q) = [] <;>
    simp [linearRightValue, directInput, h])

theorem shiftQuery_controls {F : Family} (a : Access F) (ha : a.ControlsPolyTime) : shiftQuery a ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (mem_FP_comp pairFst_mem_FP ha.coefficient)
    (mem_FP_comp pairFst_mem_FP ha.source.degree))

theorem evaluatorWithCoefficients {F : Family} (a : Access F) (ha : a.ControlsPolyTime)
    (L : SpaceFunction a.source.leftCoefficient) (R : SpaceFunction a.source.rightCoefficient) :
    SpaceFunction (value F) := by
  have SL := ShiftCoefficientBits.certifiedWithCoefficient a.source.shiftAccess ha.source.direction L
    F.source.shiftSource a.source.shift_represents
  have hright := stringEq_fppred (mem_FP_comp pairFst_mem_FP ha.source.rightDegree) (constFn_mem_FP (BinaryNatCode.encode 1))
  have hleft := stringEq_fppred (mem_FP_comp pairFst_mem_FP ha.source.leftDegree) (constFn_mem_FP (BinaryNatCode.encode 1))
  let E := SpaceFunction.branch (fun q => decide (a.source.rightDegree (pairFst q) = BinaryNatCode.encode 1))
    hright.flag_mem_FP (linearRightEvaluator a ha R)
    (SpaceFunction.branch (fun q => decide (a.source.leftDegree (pairFst q) = BinaryNatCode.encode 1))
      hleft.flag_mem_FP (SL.precompose (shiftQuery a) (shiftQuery_controls a ha))
      (a.evaluatorWithCoefficients ha L R))
  refine E.congr (funext fun q => ?_)
  by_cases hn : (F.source.right (pairFst q)).natDegree = 1
  · have hw : a.source.rightDegree (pairFst q) = BinaryNatCode.encode 1 := by rw [a.source.rightDegree_eq, hn]
    simp only [hw, decide_true, ↓reduceIte]
    rw [linearRightValue_correct]
    simp only [value, integerCoefficient, coordinateCoefficient, hn, ↓reduceIte]
  · have hw : a.source.rightDegree (pairFst q) ≠ BinaryNatCode.encode 1 := by
      rw [a.source.rightDegree_eq]
      exact fun h => hn (BinaryNatCode.encode_injective h)
    simp only [Function.comp_apply, hw, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hm : (F.source.left (pairFst q)).natDegree = 1
    · have hw' : a.source.leftDegree (pairFst q) = BinaryNatCode.encode 1 := by rw [a.source.leftDegree_eq, hm]
      simp only [hw', decide_true, ↓reduceIte]
      rw [shiftValue_correct]
      simp only [value, integerCoefficient, coordinateCoefficient, hn, hm, ↓reduceIte]
    · have hw' : a.source.leftDegree (pairFst q) ≠ BinaryNatCode.encode 1 := by
        rw [a.source.leftDegree_eq]
        exact fun h => hm (BinaryNatCode.encode_injective h)
      simp only [hw', decide_false, Bool.false_eq_true, ↓reduceIte, value, integerCoefficient,
        coordinateCoefficient, hn, hm, CannySubresultantBits.Family.value,
        CannySubresultantBits.Family.integerCoefficient]

end LeanCanny.Algebra.CannyCoordinateBits
