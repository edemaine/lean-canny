/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientMinorSpace
public import LeanCanny.Algebra.PrincipalCoefficientAccess
public import LeanCanny.Algebra.SubresultantGCDGeneral

/-! # Uniform coefficient-form residues from original polynomial readers

An integer request is `pair context (pair order coefficient)` and the modular
query pairs that request with a modulus predecessor. Orders are clamped to the
two formal degree bounds; coefficients above the clamped order return zero.
-/

@[expose] public section

namespace LeanCanny.Algebra.CoefficientFormBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower PrincipalSubresultant
open PrincipalCoefficientBits (minimum integerResidue)

def rawOrder (r : List Bool) : List Bool := pairFst (pairSnd r)
def rawCoefficient (r : List Bool) : List Bool := pairSnd (pairSnd r)

theorem rawOrder_FP : rawOrder ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem rawCoefficient_FP : rawCoefficient ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

def order (F : Resultant.Family) (r : List Bool) : ℕ :=
  min (Nat.fromBitsLE (rawOrder r)) (min (F.leftDegree (pairFst r)) (F.rightDegree (pairFst r)))

def family (F : Resultant.Family) : CoefficientMinorBits.Family where
  source := {
    left r := F.left (pairFst r)
    right r := F.right (pairFst r)
    leftDegree r := F.leftDegree (pairFst r)
    rightDegree r := F.rightDegree (pairFst r)
    coefficientBits r := F.coefficientBits (pairFst r)
    order := order F
    order_left _ := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
    order_right _ := (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
    left_bound r := F.left_bound (pairFst r)
    right_bound r := F.right_bound (pairFst r) }
  coefficient r := min (Nat.fromBitsLE (rawCoefficient r)) (order F r)
  coefficient_le _ := Nat.min_le_right _ _

def orderCode {F : Resultant.Family} (a : Resultant.Access F) (r : List Bool) : List Bool :=
  minimum (rawOrder r) (minimum (a.bits.leftDegree (pairFst r)) (a.bits.rightDegree (pairFst r)))

theorem orderCode_FP {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime) : orderCode a ∈ FP :=
  PrincipalCoefficientBits.minimum_mem_FP rawOrder_FP
    (PrincipalCoefficientBits.minimum_mem_FP (mem_FP_comp pairFst_mem_FP ha.leftDegree)
      (mem_FP_comp pairFst_mem_FP ha.rightDegree))

theorem orderCode_eq {F : Resultant.Family} (a : Resultant.Access F) (r : List Bool) :
    orderCode a r = BinaryNatCode.encode (order F r) := by
  simp only [orderCode, PrincipalCoefficientBits.minimum_eq, a.leftDegree, a.rightDegree,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, order]

def access {F : Resultant.Family} (a : Resultant.Access F) : CoefficientMinorBits.Access (family F) where
  source := {
    bits := {
      base := {
        leftDegree := a.bits.leftDegree ∘ pairFst
        rightDegree := a.bits.rightDegree ∘ pairFst
        coefficientBits := a.bits.coefficientBits ∘ pairFst
        leftCoefficient := a.bits.leftCoefficient ∘ PrincipalCoefficientBits.sourceQuery
        rightCoefficient := a.bits.rightCoefficient ∘ PrincipalCoefficientBits.sourceQuery }
      order := orderCode a }
    leftDegree_eq _ := a.leftDegree _
    rightDegree_eq _ := a.rightDegree _
    coefficientBits_eq _ := a.coefficientBits _
    order_eq := orderCode_eq a
    left_eq q i := by
      simp only [Function.comp_apply, PrincipalCoefficientBits.sourceQuery, pairFst_pair, pairSnd_pair]
      have h := a.leftCoefficient (pair (pairFst (pairFst q)) (pairSnd q)) i
      change _ = integerResidue ((F.left (pairFst (pair (pairFst (pairFst q)) (pairSnd q)))).coeff i)
        (Nat.fromBitsLE (pairSnd (pair (pairFst (pairFst q)) (pairSnd q))) + 1) at h
      rw [pairFst_pair, pairSnd_pair] at h
      exact h
    right_eq q i := by
      simp only [Function.comp_apply, PrincipalCoefficientBits.sourceQuery, pairFst_pair, pairSnd_pair]
      have h := a.rightCoefficient (pair (pairFst (pairFst q)) (pairSnd q)) i
      change _ = integerResidue ((F.right (pairFst (pair (pairFst (pairFst q)) (pairSnd q)))).coeff i)
        (Nat.fromBitsLE (pairSnd (pair (pairFst (pairFst q)) (pairSnd q))) + 1) at h
      rw [pairFst_pair, pairSnd_pair] at h
      exact h }
  coefficient r := minimum (rawCoefficient r) (orderCode a r)
  coefficient_eq r := by
    simp only [PrincipalCoefficientBits.minimum_eq, orderCode_eq, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, family]

theorem access_controls {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime) :
    (access a).ControlsPolyTime := by
  have hl := mem_FP_comp pairFst_mem_FP ha.leftDegree
  have hr := mem_FP_comp pairFst_mem_FP ha.rightDegree
  have hb := mem_FP_comp pairFst_mem_FP ha.coefficientBits
  exact ⟨⟨⟨hl, hr, hb⟩, orderCode_FP a ha⟩,
    PrincipalCoefficientBits.minimum_mem_FP rawCoefficient_FP (orderCode_FP a ha)⟩

noncomputable def value (F : Resultant.Family) (q : List Bool) : List Bool :=
  integerResidue ((coefficientForm (F.left (pairFst (pairFst q))) (F.right (pairFst (pairFst q)))
    (F.leftDegree (pairFst (pairFst q))) (F.rightDegree (pairFst (pairFst q))) (order F (pairFst q))).coeff
      (Nat.fromBitsLE (rawCoefficient (pairFst q)))) (Nat.fromBitsLE (pairSnd q) + 1)

theorem minor_value (F : Resultant.Family) (q : List Bool) :
    (family F).integer.modular.value q =
      integerResidue (((family F).integer.matrix (pairFst q)).det) (Nat.fromBitsLE (pairSnd q) + 1) := by
  change residueBits (((family F).integer.matrix (pairFst q)).map
    (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))).det = _
  exact congrArg residueBits ((Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))).map_det
    ((family F).integer.matrix (pairFst q))).symm

def within {F : Resultant.Family} (a : Resultant.Access F) (q : List Bool) : Prop :=
  Nat.fromBitsLE (rawCoefficient (pairFst q)) ≤ Nat.fromBitsLE (orderCode a (pairFst q))
instance {F : Resultant.Family} (a : Resultant.Access F) (q : List Bool) : Decidable (within a q) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem within_FP {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime) : FPPred (within a) := by
  have hl := mem_FP_comp pairFst_mem_FP rawCoefficient_FP
  have hr := mem_FP_comp pairFst_mem_FP (orderCode_FP a ha)
  have h := BinaryNat.le_fppred hl hr
  exact h.of_iff (fun _ => Iff.rfl)

theorem evaluator {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime)
    (P : SpaceFunction a.bits.leftCoefficient) (Q : SpaceFunction a.bits.rightCoefficient) : SpaceFunction (value F) := by
  have E := (access a).residueEvaluator (access_controls a ha)
    (P.precompose PrincipalCoefficientBits.sourceQuery PrincipalCoefficientBits.sourceQuery_mem_FP)
    (Q.precompose PrincipalCoefficientBits.sourceQuery PrincipalCoefficientBits.sourceQuery_mem_FP)
  have R := SpaceFunction.branch (fun q => decide (within a q)) (within_FP a ha).flag_mem_FP E
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine R.congr (funext fun q => ?_)
  have hw : within a q ↔ Nat.fromBitsLE (rawCoefficient (pairFst q)) ≤ order F (pairFst q) := by
    simp only [within, orderCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  simp only [decide_eq_true_eq, hw]
  rw [value, coefficientForm_coeff]
  by_cases h : Nat.fromBitsLE (rawCoefficient (pairFst q)) ≤ order F (pairFst q)
  · rw [ite_eq_left h, ite_eq_left h, subresultantCoeff_eq_minor_det, minor_value]
    dsimp +instances only [CoefficientMinorBits.Family.integer, family, PrincipalMinorBits.Family.integer]
    rw [Nat.min_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    simp only [integerResidue, residueBits, Int.cast_zero, ZMod.val_zero, BinaryNatCode.encode]
    rfl

theorem packet (F : Resultant.Family) (c : List Bool) (j k b : ℕ)
    (hj : j ≤ min (F.leftDegree c) (F.rightDegree c)) :
    value F (pair (pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))) (BinaryNatCode.encode b)) =
      integerResidue ((coefficientForm (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c) j).coeff k) (b + 1) := by
  simp only [value, rawCoefficient, order, rawOrder, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.min_eq_left hj]

end LeanCanny.Algebra.CoefficientFormBits
