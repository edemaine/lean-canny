/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPolynomialFactorSpace

/-!
# Polynomial-space modular determinant coefficient evaluation

Polynomial powering consumes the factor coefficient evaluator. A final FP
parity test supplies the Berkowitz sign, yielding a selected coefficient of
the determinant from space-bounded original matrix coefficient access.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.ModularAccess

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower
open Berkowitz
open Polynomial

noncomputable def powerFamily (F : ModularFamily) : PolynomialPower.ModularFamily where
  dimension := fun c => (F.dimension c + 1) * (F.dimension c + 1)
  modulus := F.modulus
  exponent := F.dimension
  row := fun c => (powerQuery (F.dimension c) 0).row
  col := fun c => (powerQuery (F.dimension c) 0).col
  degree := F.degree
  matrix := fun c => powerMatrix (F.matrix c)
  modulus_ne_zero := F.modulus_ne_zero

def splitDegree (p : List Bool) : List Bool :=
  pair (pair (pairFst p) (pair (pairFst (pairSnd p)) (pairFst (pairSnd (pairSnd p)))))
    (pairSnd (pairSnd (pairSnd p)))

theorem splitDegree_mem_FP : splitDegree ∈ FP := by
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have ht := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hj := mem_FP_comp ht pairFst_mem_FP
  have hd := mem_FP_comp ht pairSnd_mem_FP
  have h := mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_pair hi hj)) hd
  refine mem_FP_of_eq (g := splitDegree) h ?_
  intro p
  simp only [Function.comp_apply, splitDegree]

noncomputable def powerAccess {F : ModularFamily} (a : ModularAccess F) :
    PolynomialPower.ModularAccess (powerFamily F) where
  bits := {
    dimension := fun c => BinaryNat.mul (pair (BinaryNat.succ (a.dimension c)) (BinaryNat.succ (a.dimension c)))
    modulus := a.modulus
    exponent := a.dimension
    row := fun _ => []
    col := fun c => BinaryNat.mul (pair (a.dimension c) (BinaryNat.succ (a.dimension c)))
    degree := a.degree
    coefficient := factorValue a ∘ splitDegree }
  dimension_eq := fun c => by
    simp only [a.dimension_eq, BinaryNat.succ_eq_bits, BinaryNat.mul_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, powerFamily]
  modulus_eq := a.modulus_eq
  exponent_eq := a.dimension_eq
  row_eq := fun c => by simp [powerFamily, powerQuery, finProdFinEquiv, BinaryNatCode.encode]
  col_eq := fun c => by
    simp [a.dimension_eq, powerFamily, powerQuery, finProdFinEquiv, BinaryNat.mul_pair,
      BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.mul_comm]
  degree_eq := a.degree_eq
  coefficient_eq := by
    intro c i j D
    simp only [Function.comp_apply, splitDegree, pairFst_pair, pairSnd_pair]
    exact factorValue_packet a c i j D

theorem power_controls {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    a.powerAccess.bits.ControlsPolyTime := by
  have hw := mem_FP_comp ha.dimension BinaryNat.succ_mem_FP
  have hd := mem_FP_comp (mem_FP_pair hw hw) BinaryNat.mul_mem_FP
  have hc := mem_FP_comp (mem_FP_pair ha.dimension hw) BinaryNat.mul_mem_FP
  constructor
  · simpa only [powerAccess, Function.comp_def] using hd
  · simpa only [powerAccess] using ha.modulus
  · simpa only [powerAccess] using ha.dimension
  · exact constFn_mem_FP []
  · simpa only [powerAccess, Function.comp_def] using hc
  · simpa only [powerAccess] using ha.degree

theorem powerEvaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) : SpaceFunction (powerFamily F).value := by
  have C := (factorEvaluator a ha E).precompose splitDegree splitDegree_mem_FP
  have EC : SpaceFunction a.powerAccess.bits.coefficient := by
    simpa only [powerAccess] using C
  exact PolynomialPower.ModularAccess.evaluator a.powerAccess (power_controls a ha) EC

def finish {F : ModularFamily} (a : ModularAccess F) (z : List Bool) : List Bool :=
  if BinaryNat.mod (pair (a.dimension (pairFst z)) (BinaryNatCode.encode 2)) = [] then pairSnd z
  else ArithmeticBits.negate (pair (a.modulus (pairFst z)) (pairSnd z))

theorem finish_mem_FP {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) : finish a ∈ FP := by
  have hn := mem_FP_comp pairFst_mem_FP ha.dimension
  have hp := mem_FP_comp (mem_FP_pair hn (constFn_mem_FP (BinaryNatCode.encode 2))) BinaryNat.mod_mem_FP
  have hm := mem_FP_comp pairFst_mem_FP ha.modulus
  have hneg := mem_FP_comp (mem_FP_pair hm pairSnd_mem_FP) ArithmeticBits.negate_mem_FP
  have h := (stringEq_fppred hp (constFn_mem_FP [])).ite_mem_FP pairSnd_mem_FP hneg
  refine mem_FP_of_eq (g := finish a) h ?_
  intro z
  simp only [Function.comp_apply, finish]

theorem finish_pair {F : ModularFamily} (a : ModularAccess F) (c : List Bool) (x : ZMod (F.modulus c)) :
    finish a (pair c (residueBits x)) = residueBits ((-1) ^ F.dimension c * x) := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  rw [finish, pairFst_pair, pairSnd_pair, a.dimension_eq, a.modulus_eq]
  simp only [BinaryNat.mod_pair, QueryBits.code_value, BinaryNat.bits_eq_nil_iff]
  rw [neg_one_pow_eq_pow_mod_two]
  by_cases he : F.dimension c % 2 = 0
  · simp [he]
  · have ho : F.dimension c % 2 = 1 := by have h := Nat.mod_lt (F.dimension c) (by decide : 0 < 2); omega
    simp [ho, ArithmeticBits.negate_residueBits]

theorem evaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) : SpaceFunction F.value := by
  have P := ((powerEvaluator a ha E).withInput).postcompose (finish a) (finish_mem_FP a ha)
  refine P.congr ?_
  funext c
  simp only [Function.comp_apply]
  change finish a (pair c (residueBits
    (((powerMatrix (F.matrix c) ^ F.dimension c) (powerQuery (F.dimension c) 0).row
      (powerQuery (F.dimension c) 0).col).coeff (F.degree c)))) = _
  rw [finish_pair]
  have h := det_eq_powerMatrix (F.matrix c)
  have hs : (-1 : (ZMod (F.modulus c))[X]) ^ F.dimension c = C ((-1 : ZMod (F.modulus c)) ^ F.dimension c) := by simp
  simp only [ModularFamily.value, h, hs, Polynomial.coeff_C_mul]

theorem decider {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) : SpaceDecider F.zeroLanguage := by
  let accept := fun bits : List Bool => decide (bits = [])
  have haccept : (fun bits => [accept bits]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  refine (evaluator a ha E).decider accept haccept ?_
  intro c
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  have hz : residueBits (0 : ZMod (F.modulus c)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change (F.matrix c).det.coeff (F.degree c) = 0 ↔
    decide (residueBits ((F.matrix c).det.coeff (F.degree c)) = []) = true
  rw [decide_eq_true_eq, ← hz, (residueBits_injective (F.modulus c)).eq_iff]

theorem zeroLanguage_mem_PSPACE_of_evaluator {F : ModularFamily} (a : ModularAccess F)
    (ha : a.ControlsPolyTime) (E : SpaceFunction a.entry) : F.zeroLanguage ∈ PSPACE :=
  (decider a ha E).mem_PSPACE

end LeanCanny.Algebra.BerkowitzPolynomial.ModularAccess
