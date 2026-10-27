/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialPseudoRemainderSource

/-! # Native parameter coefficients of polynomial reduction iterates

A polynomial scalar moment selects one outer coefficient of the fixed even
reduction iterate. The polynomial powering backend selects its parameter
coefficient using the original head and input modular readers.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialPseudoRemainderBits
open Polynomial Matrix LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

def modulusCode (z : List Bool) : List Bool := BinaryNat.succ (pairSnd (pairFst z))
theorem modulusCode_FP : modulusCode ∈ FP := by polytime [modulusCode]
theorem modulusCode_eq (z : List Bool) : modulusCode z = BinaryNatCode.encode (modulus z) :=
  BinaryNat.succ_eq_bits _

def selectedCode (F : Family) (z : List Bool) : List Bool :=
  BinaryNat.mod (pair (pairSnd (pairSnd z)) (BinaryNat.succ (BinaryNatCode.encode (F.bound (origin z)))))
theorem selectedCode_eq (F : Family) (z : List Bool) :
    selectedCode F z = BinaryNatCode.encode (selected F z).val := by
  simp only [selectedCode, selected, index, BinaryNat.mod_pair, BinaryNat.succ_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
theorem selectedCode_FP {F : Family} (A : Access F) : selectedCode F ∈ FP := by
  have hb := BinaryFn.bits_mem_FP (A.bound.comp origin_FP)
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    (mem_FP_comp hb BinaryNat.succ_mem_FP)) BinaryNat.mod_mem_FP
  exact h

def row (F : Family) (e : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairFst (pairSnd e)) = Nat.fromBitsLE (selectedCode F (pairFst e)) ∧
    Nat.fromBitsLE (pairSnd (pairSnd e)) = 0 then ArithmeticBits.one (modulusCode (pairFst e)) else []

theorem row_FP {F : Family} (A : Access F) : row F ∈ FP := by
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp pairFst_mem_FP (selectedCode_FP A)
  have hu := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hp := (BinaryNat.eq_fppred hi hs).and
    (BinaryNat.eq_fppred hu (constFn_mem_FP []))
  have ho := mem_FP_comp (mem_FP_comp pairFst_mem_FP modulusCode_FP) ArithmeticBits.one_mem_FP
  exact hp.ite_mem_FP ho (constFn_mem_FP [])

theorem row_packet (F : Family) (z : List Bool) (j : Fin (F.bound (origin z) + 1)) (u : ℕ) :
    row F (pair z (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u))) =
      residueBits (((if j = selected F z then 1 else 0 : (ZMod (modulus z))[X])).coeff u) := by
  let : NeZero (modulus z) := ⟨by simp [modulus]⟩
  simp only [row, pairFst_pair, pairSnd_pair, selectedCode_eq, modulusCode_eq,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, ← Fin.ext_iff]
  by_cases hj : j = selected F z
  · simp only [hj, ite_true, true_and, Polynomial.coeff_one]
    by_cases hu : u = 0
    · subst u
      simp only [ite_true]
      exact ArithmeticBits.one_residueBits _
    · simp [hu, residueBits, BinaryNatCode.encode]
  · simp [hj, residueBits, BinaryNatCode.encode]

noncomputable def moment (F : Family) : PolynomialMoment.ModularFamily where
  dimension z := F.bound (origin z) + 1
  modulus := modulus
  exponent z := 2 * (F.bound (origin z) + 1)
  degree := parameter
  row z j := if j = selected F z then 1 else 0
  column z j := (mapCoefficients (F.input (origin z)) (modulus z)).coeff j.val
  matrix := matrix F
  modulus_ne_zero z := by simp [modulus]

set_option backward.isDefEq.respectTransparency false in
noncomputable def momentAccess {F : Family} (A : Access F) : PolynomialMoment.ModularAccess (moment F) where
  bits := {
    dimension z := BinaryNatCode.encode (F.bound (origin z) + 1)
    row := row F
    column := column A
    entry := entry A }
  modulus := modulusCode
  exponent z := BinaryNatCode.encode (2 * (F.bound (origin z) + 1))
  degree z := BinaryNat.normalize (pairFst (pairSnd z))
  dimension_eq _ := rfl
  modulus_eq := modulusCode_eq
  exponent_eq _ := rfl
  degree_eq _ := BinaryNat.normalize_eq_bits _
  row_eq := row_packet F
  column_eq z i u := column_packet A z i.val u
  entry_eq z i j u := by
    change Fin (F.bound (origin z) + 1) at i j
    simpa only [moment] using entry_packet A z i j u

theorem moment_controls {F : Family} (A : Access F) :
    PolynomialMoment.ModularAccess.ControlsPolyTime (F := moment F) (momentAccess A) := by
  have hb : BinaryFn (fun z => F.bound (origin z) + 1) :=
    BinaryFn.add (A.bound.comp origin_FP) (BinaryFn.const 1)
  have hd := hb.bits_mem_FP
  have he := BinaryFn.bits_mem_FP ((BinaryFn.const 2).mul hb)
  have hu := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) BinaryNat.normalize_mem_FP
  exact ⟨hd, modulusCode_FP, he, hu⟩

attribute [local irreducible] row column entry

theorem moment_evaluator {F : Family} (A : Access F) : SpaceFunction (moment F).value := by
  have R : SpaceFunction (momentAccess A).bits.row := SpaceFunction.ofFP _ (row_FP A)
  have C : SpaceFunction (momentAccess A).bits.column := column_evaluator A
  have E : SpaceFunction (momentAccess A).bits.entry := entry_evaluator A
  exact PolynomialMoment.ModularAccess.evaluator (F := moment F) (momentAccess A) (moment_controls A) R C E

theorem moment_value (F : Family) (z : List Bool) :
    (moment F).value z = residueBits ((((F.reduced (origin z)).coeff (selected F z).val).coeff (parameter z) : ℤ) :
      ZMod (modulus z)) := by
  have h := congrFun (PseudoRemainder.iterate_toFn
    (mapCoefficients (F.head (origin z)) (modulus z)) (mapCoefficients (F.input (origin z)) (modulus z))
    (F.degree (origin z)) (F.bound (origin z)) (2 * (F.bound (origin z) + 1))
    (F.degree_pos _) (F.degree_le _) (Polynomial.natDegree_map_le.trans (F.input_degree _))) (selected F z)
  change ((PseudoRemainder.step (mapCoefficients (F.head (origin z)) (modulus z)) (F.degree (origin z)))^[2 * (F.bound (origin z) + 1)]
      (mapCoefficients (F.input (origin z)) (modulus z))).coeff (selected F z).val =
    (PseudoRemainder.matrix (mapCoefficients (F.head (origin z)) (modulus z)) (F.degree (origin z))
      (F.bound (origin z)) ^ (2 * (F.bound (origin z) + 1)) *ᵥ
        (fun j => (mapCoefficients (F.input (origin z)) (modulus z)).coeff j.val)) (selected F z) at h
  change residueBits (((fun j => if j = selected F z then (1 : (ZMod (modulus z))[X]) else 0) ⬝ᵥ
    (PseudoRemainder.matrix (mapCoefficients (F.head (origin z)) (modulus z)) (F.degree (origin z))
      (F.bound (origin z)) ^ (2 * (F.bound (origin z) + 1)) *ᵥ
        (fun j => (mapCoefficients (F.input (origin z)) (modulus z)).coeff j.val))).coeff (parameter z)) = _
  simp only [dotProduct, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← h]
  have hm : (PseudoRemainder.step (mapCoefficients (F.head (origin z)) (modulus z)) (F.degree (origin z)))^[2 * (F.bound (origin z) + 1)]
      (mapCoefficients (F.input (origin z)) (modulus z)) = mapCoefficients (F.reduced (origin z)) (modulus z) :=
    PseudoRemainder.iterate_map (Polynomial.mapRingHom (Int.castRingHom (ZMod (modulus z)))) _ _ _ _
  rw [hm, mapCoefficients_coeff]

end LeanCanny.Algebra.PolynomialPseudoRemainderBits
