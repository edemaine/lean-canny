/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ResultantPolynomialSpace
public import LeanCanny.Algebra.ShiftCoefficientResidue
public import LeanCanny.Algebra.CannyResultantDegrees

/-!
# Certified residues of Canny's resultant coefficients

The left Sylvester input is `p₁(θ-c*x)` and the right input is `p₂(x)`.
Shifted coefficient evaluation supplies the first child; an FP constant
coefficient guard supplies the second. Source orders default to the integer
input degrees, so modular degree drops do not change the usual resultant.
Explicit supplied orders instead define the corresponding Sylvester
determinant on every input, without a source-degree consistency hypothesis.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower
open Polynomial

def mValue (q : List Bool) : ℕ := Nat.fromBitsLE (pairSnd q) + 1

structure Family where
  left : List Bool → Polynomial ℤ
  right : List Bool → Polynomial ℤ
  direction : List Bool → ℕ
  degree : List Bool → ℕ

noncomputable def Family.value (F : Family) (q : List Bool) : List Bool :=
  residueBits (((cannyResultant (F.left (pairFst q)) (F.right (pairFst q)) (F.direction (pairFst q))).coeff
    (F.degree (pairFst q)) : ℤ) : ZMod (mValue q))

def Family.zeroLanguage (F : Family) : LeanCanny.Language :=
  {q | (((cannyResultant (F.left (pairFst q)) (F.right (pairFst q)) (F.direction (pairFst q))).coeff
    (F.degree (pairFst q)) : ℤ) : ZMod (mValue q)) = 0}

def Family.shiftSource (F : Family) : ShiftCoefficientBits.Family where
  polynomial := F.left
  direction := F.direction

noncomputable def Family.specifiedValue (F : Family) (leftOrder rightOrder : List Bool → ℕ)
    (q : List Bool) : List Bool :=
  residueBits (((cannyResultantWithDegrees (F.left (pairFst q)) (F.right (pairFst q)) (F.direction (pairFst q))
    (leftOrder (pairFst q)) (rightOrder (pairFst q))).coeff (F.degree (pairFst q)) : ℤ) : ZMod (mValue q))

noncomputable def Family.modularWithDegrees (F : Family) (leftOrder rightOrder : List Bool → ℕ) : ResultantPolynomial.ModularFamily where
  modulus := mValue
  left := fun q => (shiftFamily (F.left (pairFst q)) (F.direction (pairFst q))).map
    (Polynomial.mapRingHom (Int.castRingHom (ZMod (mValue q))))
  right := fun q => ((F.right (pairFst q)).map C).map
    (Polynomial.mapRingHom (Int.castRingHom (ZMod (mValue q))))
  leftDegree := leftOrder ∘ pairFst
  rightDegree := rightOrder ∘ pairFst
  degree := fun q => F.degree (pairFst q)
  modulus_ne_zero := fun q => by simp only [mValue]; omega

noncomputable def Family.modular (F : Family) : ResultantPolynomial.ModularFamily :=
  F.modularWithDegrees (fun c => (F.left c).natDegree) (fun c => (F.right c).natDegree)

set_option backward.isDefEq.respectTransparency false in
theorem Family.modularWithDegrees_value (F : Family) (leftOrder rightOrder : List Bool → ℕ) (q : List Bool) :
    (F.modularWithDegrees leftOrder rightOrder).value q = F.specifiedValue leftOrder rightOrder q := by
  simp only [ResultantPolynomial.ModularFamily.value, Family.modularWithDegrees, Function.comp_apply,
    Polynomial.resultant_map_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rfl

theorem Family.specifiedValue_exact (F : Family) (q : List Bool) :
    F.specifiedValue (fun c => (F.left c).natDegree) (fun c => (F.right c).natDegree) q = F.value q := rfl

theorem Family.specifiedValue_eq (F : Family) (leftOrder rightOrder : List Bool → ℕ) (q : List Bool)
    (hl : leftOrder (pairFst q) = (F.left (pairFst q)).natDegree)
    (hr : rightOrder (pairFst q) = (F.right (pairFst q)).natDegree) :
    F.specifiedValue leftOrder rightOrder q = F.value q := by
  simp only [Family.specifiedValue, hl, hr, cannyResultantWithDegrees_exact, Family.value]

theorem Family.modular_value (F : Family) (q : List Bool) : F.modular.value q = F.value q :=
  (F.modularWithDegrees_value _ _ q).trans (F.specifiedValue_exact q)

structure Access (F : Family)
    (leftOrder : List Bool → ℕ := fun c => (F.left c).natDegree)
    (rightOrder : List Bool → ℕ := fun c => (F.right c).natDegree) where
  leftDegree : List Bool → List Bool
  rightDegree : List Bool → List Bool
  direction : List Bool → List Bool
  degree : List Bool → List Bool
  leftCoefficient : List Bool → List Bool
  rightCoefficient : List Bool → List Bool
  leftDegree_eq : ∀ c, leftDegree c = BinaryNatCode.encode (leftOrder c)
  rightDegree_eq : ∀ c, rightDegree c = BinaryNatCode.encode (rightOrder c)
  direction_eq : ∀ c, direction c = BinaryNatCode.encode (F.direction c)
  degree_eq : ∀ c, degree c = BinaryNatCode.encode (F.degree c)
  leftCoefficient_eq : ∀ q k, leftCoefficient (pair q (BinaryNatCode.encode k)) =
    residueBits (((F.left (pairFst q)).coeff k : ℤ) : ZMod (mValue q))
  rightCoefficient_eq : ∀ q k, rightCoefficient (pair q (BinaryNatCode.encode k)) =
    residueBits (((F.right (pairFst q)).coeff k : ℤ) : ZMod (mValue q))

structure Access.PolyTime {F : Family} {leftOrder rightOrder : List Bool → ℕ} (a : Access F leftOrder rightOrder) : Prop where
  leftDegree : a.leftDegree ∈ FP
  rightDegree : a.rightDegree ∈ FP
  direction : a.direction ∈ FP
  degree : a.degree ∈ FP
  leftCoefficient : a.leftCoefficient ∈ FP
  rightCoefficient : a.rightCoefficient ∈ FP

namespace Access

def shiftAccess {F : Family} {leftOrder rightOrder : List Bool → ℕ} (a : Access F leftOrder rightOrder) : ShiftCoefficientBits.Access where
  direction := a.direction
  coefficient := a.leftCoefficient

theorem shift_polyTime {F : Family} {leftOrder rightOrder : List Bool → ℕ} (a : Access F leftOrder rightOrder) (ha : a.PolyTime) : a.shiftAccess.PolyTime :=
  ⟨ha.direction, ha.leftCoefficient⟩

theorem shift_represents {F : Family} {leftOrder rightOrder : List Bool → ℕ} (a : Access F leftOrder rightOrder) : ShiftCoefficientBits.Represents a.shiftAccess F.shiftSource :=
  ⟨a.direction_eq, a.leftCoefficient_eq⟩

def constantCoefficient {F : Family} {leftOrder rightOrder : List Bool → ℕ} (a : Access F leftOrder rightOrder) (p : List Bool) : List Bool :=
  if BinaryNat.normalize (ShiftCoefficientBits.rightIndex p) = [] then
    a.rightCoefficient (pair (pairFst p) (ShiftCoefficientBits.leftIndex p)) else []

theorem constantCoefficient_mem_FP {F : Family} {leftOrder rightOrder : List Bool → ℕ} (a : Access F leftOrder rightOrder) (ha : a.PolyTime) : a.constantCoefficient ∈ FP := by
  have hk := mem_FP_comp ShiftCoefficientBits.rightIndex_mem_FP BinaryNat.normalize_mem_FP
  have hq := mem_FP_pair pairFst_mem_FP ShiftCoefficientBits.leftIndex_mem_FP
  have hr := mem_FP_comp hq ha.rightCoefficient
  have h := (stringEq_fppred hk (constFn_mem_FP [])).ite_mem_FP hr (constFn_mem_FP [])
  refine mem_FP_of_eq (g := a.constantCoefficient) h ?_
  intro p
  simp only [Function.comp_apply, constantCoefficient]

set_option backward.isDefEq.respectTransparency false in
noncomputable def modular {F : Family} {leftOrder rightOrder : List Bool → ℕ} (a : Access F leftOrder rightOrder) : ResultantPolynomial.ModularAccess (F.modularWithDegrees leftOrder rightOrder) where
  bits := {
    leftDegree := a.leftDegree ∘ pairFst
    rightDegree := a.rightDegree ∘ pairFst
    modulus := BinaryNat.succ ∘ pairSnd
    degree := a.degree ∘ pairFst
    leftCoefficient := F.shiftSource.value
    rightCoefficient := a.constantCoefficient }
  leftDegree_eq := fun q => a.leftDegree_eq (pairFst q)
  rightDegree_eq := fun q => a.rightDegree_eq (pairFst q)
  modulus_eq := fun q => by simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Family.modularWithDegrees, mValue, BinaryNatCode.encode]
  degree_eq := fun q => a.degree_eq (pairFst q)
  leftCoefficient_eq := by
    intro q k d
    change F.shiftSource.value (pair q (pair (BinaryNatCode.encode k) (BinaryNatCode.encode d))) = _
    rw [ShiftCoefficientBits.Family.value_packet]
    simp only [Family.shiftSource, Family.modularWithDegrees, Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    rfl
  rightCoefficient_eq := by
    intro q k d
    simp only [constantCoefficient, ShiftCoefficientBits.leftIndex, ShiftCoefficientBits.rightIndex,
      pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, ShiftCoefficientBits.code_value, BinaryNat.bits_eq_nil_iff,
      a.rightCoefficient_eq, Family.modularWithDegrees, Polynomial.coeff_map, Polynomial.coe_mapRingHom,
      Polynomial.coeff_C]
    split_ifs <;> simp [residueBits, BinaryNatCode.encode]

theorem modular_controls {F : Family} {leftOrder rightOrder : List Bool → ℕ} (a : Access F leftOrder rightOrder) (ha : a.PolyTime) : a.modular.bits.ControlsPolyTime := by
  have hl := mem_FP_comp pairFst_mem_FP ha.leftDegree
  have hr := mem_FP_comp pairFst_mem_FP ha.rightDegree
  have hm := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have hd := mem_FP_comp pairFst_mem_FP ha.degree
  constructor
  · simpa only [modular] using hl
  · simpa only [modular] using hr
  · simpa only [modular] using hm
  · simpa only [modular] using hd

theorem evaluator {F : Family} (a : Access F) (ha : a.PolyTime) : SpaceFunction F.value := by
  have L := ShiftCoefficientBits.certified a.shiftAccess (shift_polyTime a ha) F.shiftSource (shift_represents a)
  have R := SpaceFunction.ofFP a.constantCoefficient (constantCoefficient_mem_FP a ha)
  have E := ResultantPolynomial.ModularAccess.evaluator a.modular (modular_controls a ha) L R
  refine E.congr ?_
  funext q
  exact F.modular_value q

theorem decider {F : Family} (a : Access F) (ha : a.PolyTime) : SpaceDecider F.zeroLanguage := by
  let accept := fun bits : List Bool => decide (bits = [])
  have haccept : (fun bits => [accept bits]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  refine (evaluator a ha).decider accept haccept ?_
  intro q
  let : NeZero (mValue q) := ⟨by simp only [mValue]; omega⟩
  have hz : residueBits (0 : ZMod (mValue q)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change _ ↔ decide (F.value q = []) = true
  rw [decide_eq_true_eq, Family.value, ← hz, (residueBits_injective (mValue q)).eq_iff]
  rfl

theorem zeroLanguage_mem_PSPACE {F : Family} (a : Access F) (ha : a.PolyTime) : F.zeroLanguage ∈ PSPACE :=
  (decider a ha).mem_PSPACE

end Access
end LeanCanny.Algebra.CannyResultantBits
