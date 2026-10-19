/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PseudoRemainderEntrySpace
public import LeanCanny.Algebra.MatrixMomentSpaceEntries

/-! # A complete streamed pseudo-remainder coefficient evaluator

FP binary fields and suspended coefficient access to the original head and
input suffice. The matrix entries, coordinate row, powering, and scalar moment
are supplied internally. The coefficient ring may have zero divisors, and the
formal head bound is retained when reduction modulo the modulus lowers degrees.
-/

@[expose] public section

namespace LeanCanny.Algebra.PseudoRemainderBits
open Complexity Polynomial Matrix
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower
open scoped Classical

structure Family where
  modulus : List Bool → ℕ
  head : (c : List Bool) → (ZMod (modulus c))[X]
  input : (c : List Bool) → (ZMod (modulus c))[X]
  degree : List Bool → ℕ
  bound : List Bool → ℕ
  selected : (c : List Bool) → Fin (bound c + 1)
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  degree_pos : ∀ c, 0 < degree c
  degree_le : ∀ c, degree c ≤ bound c
  head_degree : ∀ c, (head c).natDegree ≤ degree c
  input_degree : ∀ c, (input c).natDegree ≤ bound c

noncomputable def Family.value (F : Family) (c : List Bool) : List Bool :=
  residueBits (((PseudoRemainder.step (F.head c) (F.degree c))^[2 * (F.bound c + 1)]
    (F.input c)).coeff (F.selected c).val)

noncomputable def Family.moment (F : Family) : MatrixMoment.ModularFamily where
  dimension c := F.bound c + 1
  modulus := F.modulus
  exponent c := 2 * (F.bound c + 1)
  row c j := if j = F.selected c then 1 else 0
  column c j := (F.input c).coeff j.val
  matrix c := PseudoRemainder.matrix (F.head c) (F.degree c) (F.bound c)
  modulus_ne_zero := F.modulus_ne_zero

theorem Family.moment_value (F : Family) (c : List Bool) : F.moment.value c = F.value c := by
  have h := congrFun (PseudoRemainder.iterate_toFn (F.head c) (F.input c)
    (F.degree c) (F.bound c) (2 * (F.bound c + 1))
    (F.degree_pos c) (F.degree_le c) (F.input_degree c)) (F.selected c)
  change residueBits ((fun j => if j = F.selected c then 1 else 0) ⬝ᵥ
    (PseudoRemainder.matrix (F.head c) (F.degree c) (F.bound c) ^ (2 * (F.bound c + 1)) *ᵥ
      (fun j => (F.input c).coeff j.val))) = _
  simp only [dotProduct, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact congrArg residueBits h.symm

structure DataAccess (F : Family) where
  source : Access
  bound : List Bool → List Bool
  selected : List Bool → List Bool
  inputCoefficient : List Bool → List Bool
  degree_eq : ∀ c, source.headDegree c = BinaryNatCode.encode (F.degree c)
  modulus_eq : ∀ c, source.modulus c = BinaryNatCode.encode (F.modulus c)
  bound_eq : ∀ c, bound c = BinaryNatCode.encode (F.bound c)
  selected_eq : ∀ c, selected c = BinaryNatCode.encode (F.selected c).val
  head_eq : ∀ c k, source.coefficient (pair c (BinaryNatCode.encode k)) = residueBits ((F.head c).coeff k)
  input_eq : ∀ c k, inputCoefficient (pair c (BinaryNatCode.encode k)) = residueBits ((F.input c).coeff k)

structure DataAccess.ControlsPolyTime {F : Family} (a : DataAccess F) : Prop where
  degree : a.source.headDegree ∈ FP
  modulus : a.source.modulus ∈ FP
  bound : a.bound ∈ FP
  selected : a.selected ∈ FP

namespace DataAccess

def dimension {F : Family} (a : DataAccess F) (c : List Bool) : List Bool := BinaryNat.succ (a.bound c)
def exponent {F : Family} (a : DataAccess F) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (dimension a c) (dimension a c))
def rowValue {F : Family} (a : DataAccess F) (q : List Bool) : List Bool :=
  if BinaryNat.normalize (pairSnd q) = a.selected (pairFst q) then
    ArithmeticBits.one (a.source.modulus (pairFst q)) else []

theorem dimension_mem_FP {F : Family} (a : DataAccess F) (ha : a.ControlsPolyTime) :
    dimension a ∈ FP := mem_FP_comp ha.bound BinaryNat.succ_mem_FP

theorem dimension_code {F : Family} (a : DataAccess F) (c : List Bool) :
    dimension a c = BinaryNatCode.encode (F.bound c + 1) := by
  simp only [dimension, a.bound_eq, BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem exponent_mem_FP {F : Family} (a : DataAccess F) (ha : a.ControlsPolyTime) :
    exponent a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (dimension_mem_FP a ha) (dimension_mem_FP a ha)) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := exponent a) h ?_
  intro c
  simp only [exponent, Function.comp_apply]

theorem rowValue_mem_FP {F : Family} (a : DataAccess F) (ha : a.ControlsPolyTime) :
    rowValue a ∈ FP := by
  have hi := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  have hs := mem_FP_comp pairFst_mem_FP ha.selected
  have ho := mem_FP_comp (mem_FP_comp pairFst_mem_FP ha.modulus) ArithmeticBits.one_mem_FP
  have h := (stringEq_fppred hi hs).ite_mem_FP ho (constFn_mem_FP [])
  refine mem_FP_of_eq (g := rowValue a) h ?_
  intro q
  simp only [rowValue, Function.comp_apply]

set_option backward.isDefEq.respectTransparency false in
noncomputable def moment {F : Family} (a : DataAccess F) : MatrixMoment.ModularAccess F.moment where
  bits := {
    dimension := dimension a
    row := rowValue a
    column := a.inputCoefficient
    entry := entry a.source }
  modulus := a.source.modulus
  exponent := exponent a
  dimension_eq c := dimension_code a c
  modulus_eq := a.modulus_eq
  exponent_eq c := by
    simp only [exponent, dimension_code, BinaryNat.add_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, Family.moment]
    congr 1
    omega
  row_eq c j := by
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    change rowValue a (pair c (BinaryNatCode.encode j.val)) =
      residueBits (if j = F.selected c then 1 else 0)
    simp only [rowValue, pairSnd_pair, pairFst_pair, a.selected_eq, a.modulus_eq,
      show BinaryNat.normalize (BinaryNatCode.encode j.val) = BinaryNatCode.encode j.val from
        BinaryNat.normalize_bits j.val,
      BinaryNatCode.encode_injective.eq_iff, ← Fin.ext_iff]
    by_cases hj : j = F.selected c
    · simp only [ite_eq_left hj]
      exact ArithmeticBits.one_residueBits _
    · simp only [ite_eq_right hj]
      simp [residueBits, BinaryNatCode.encode]
  column_eq c i := a.input_eq c i.val
  entry_eq c i j := by
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    exact entry_correct a.source c _ _ _ (F.head c) (F.head_degree c)
      (a.degree_eq c) (a.modulus_eq c) (a.head_eq c) i j

noncomputable def evaluator {F : Family} (a : DataAccess F) (ha : a.ControlsPolyTime)
    (P : SpaceFunction a.source.coefficient) (G : SpaceFunction a.inputCoefficient) :
    SpaceFunction F.value := by
  have hc : a.moment.ControlsPolyTime :=
    ⟨dimension_mem_FP a ha, ha.modulus, exponent_mem_FP a ha⟩
  let E := MatrixMoment.ModularAccess.evaluator a.moment hc
    (SpaceFunction.ofFP (rowValue a) (rowValue_mem_FP a ha)) G
    (entryEvaluator a.source ha.degree ha.modulus P)
  exact E.congr (funext F.moment_value)

end DataAccess
end LeanCanny.Algebra.PseudoRemainderBits
