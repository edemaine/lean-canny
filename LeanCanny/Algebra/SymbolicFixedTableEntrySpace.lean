/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableSlice
public import LeanCanny.Algebra.CannyCoefficientSpace

/-! # Native symbolic shifted-resultant matrix entry readers

Alpha selection is retained in the original context. The existing integer
Canny source supplies Sylvester guards and binomial arithmetic on one slice.
This is an entry reader, suitable for the bivariate determinant backend; no
claim that a resultant commutes with coefficient slicing is used.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTableEntryBits
open Polynomial SymbolicScaledSquarefree SymbolicFixedTable
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

structure Family where
  left : List Bool → Polynomial Coefficient
  right : List Bool → Polynomial Coefficient
  leftOrder : List Bool → ℕ
  rightOrder : List Bool → ℕ
  direction : List Bool → ℕ

noncomputable def integerResidue (z : ℤ) (m : ℕ) : List Bool := residueBits (z : ZMod m)

noncomputable def coefficient (p : List Bool → Polynomial Coefficient) (q : List Bool) : List Bool :=
  let a : ℤ := ((p (pairFst (pairFst q))).coeff (Nat.fromBitsLE (pairSnd (pairSnd q)))).coeff
    (Nat.fromBitsLE (pairFst (pairSnd q)))
  integerResidue a (Nat.fromBitsLE (pairSnd (pairFst q)) + 1)

def sliceCoefficientQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst q))) (pairSnd (pairFst q)))
    (pair (pairSnd (pairFst (pairFst q))) (pairSnd q))

theorem sliceCoefficientQuery_FP : sliceCoefficientQuery ∈ FP := by
  exact mem_FP_pair
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP)
      (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP)

noncomputable def Family.sliced (F : Family) : CannyResultantBits.Family where
  left c := slice (F.left (pairFst c)) (Nat.fromBitsLE (pairSnd c))
  right c := slice (F.right (pairFst c)) (Nat.fromBitsLE (pairSnd c))
  direction c := F.direction (pairFst c)
  degree _ := 0

noncomputable def Family.access (F : Family) : CannyResultantBits.Access F.sliced
    (fun c => F.leftOrder (pairFst c)) (fun c => F.rightOrder (pairFst c)) where
  leftDegree c := BinaryNatCode.encode (F.leftOrder (pairFst c))
  rightDegree c := BinaryNatCode.encode (F.rightOrder (pairFst c))
  direction c := BinaryNatCode.encode (F.direction (pairFst c))
  degree _ := []
  leftCoefficient := coefficient F.left ∘ sliceCoefficientQuery
  rightCoefficient := coefficient F.right ∘ sliceCoefficientQuery
  leftDegree_eq _ := rfl
  rightDegree_eq _ := rfl
  direction_eq _ := rfl
  degree_eq _ := rfl
  leftCoefficient_eq := by
    intro q k
    change coefficient F.left (sliceCoefficientQuery (pair q (BinaryNatCode.encode k))) =
      integerResidue ((F.sliced.left (pairFst q)).coeff k) (CannyResultantBits.mValue q)
    simp only [coefficient, sliceCoefficientQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, Family.sliced, slice_coeff, CannyResultantBits.mValue]
  rightCoefficient_eq := by
    intro q k
    change coefficient F.right (sliceCoefficientQuery (pair q (BinaryNatCode.encode k))) =
      integerResidue ((F.sliced.right (pairFst q)).coeff k) (CannyResultantBits.mValue q)
    simp only [coefficient, sliceCoefficientQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, Family.sliced, slice_coeff, CannyResultantBits.mValue]

theorem Family.access_controls (F : Family) (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder)
    (hc : BinaryFn F.direction) : F.access.ControlsPolyTime := by
  constructor
  · change (fun c => BinaryNatCode.encode (F.leftOrder (pairFst c))) ∈ FP
    exact mem_FP_comp (f := pairFst) (g := fun c => BinaryNatCode.encode (F.leftOrder c)) pairFst_mem_FP hm.bits_mem_FP
  · change (fun c => BinaryNatCode.encode (F.rightOrder (pairFst c))) ∈ FP
    exact mem_FP_comp (f := pairFst) (g := fun c => BinaryNatCode.encode (F.rightOrder c)) pairFst_mem_FP hn.bits_mem_FP
  · change (fun c => BinaryNatCode.encode (F.direction (pairFst c))) ∈ FP
    exact mem_FP_comp (f := pairFst) (g := fun c => BinaryNatCode.encode (F.direction c)) pairFst_mem_FP hc.bits_mem_FP
  · exact constFn_mem_FP []

def entryQuery (q : List Bool) : List Bool :=
  pair (pair (pair (pairFst (pairFst q)) (pairFst (pairSnd (pairSnd (pairSnd q))))) (pairSnd (pairFst q)))
    (pair (pairFst (pairSnd q)) (pair (pairFst (pairSnd (pairSnd q))) (pairSnd (pairSnd (pairSnd (pairSnd q))))))

theorem entryQuery_FP : entryQuery ∈ FP := by
  have h3 := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
  exact mem_FP_pair
    (mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (mem_FP_comp h3 pairFst_mem_FP))
      (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
      (mem_FP_pair (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP)
        (mem_FP_comp h3 pairSnd_mem_FP)))

noncomputable def Family.entry (F : Family) : List Bool → List Bool :=
  F.access.modular.determinant.entry ∘ entryQuery

theorem Family.entryEvaluator (F : Family) (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder)
    (hc : BinaryFn F.direction) (L : SpaceFunction (coefficient F.left)) (R : SpaceFunction (coefficient F.right)) :
    SpaceFunction F.entry := by
  have ha := F.access_controls hm hn hc
  have SL := ShiftCoefficientBits.certifiedWithCoefficient F.access.shiftAccess ha.direction
    (L.precompose sliceCoefficientQuery sliceCoefficientQuery_FP) F.sliced.shiftSource F.access.shift_represents
  have SR := F.access.constantCoefficientEvaluator (R.precompose sliceCoefficientQuery sliceCoefficientQuery_FP)
  exact (F.access.modular.entryEvaluator (F.access.modular_controlsWithCoefficients ha) SL SR).precompose entryQuery entryQuery_FP

theorem Family.entry_correct (F : Family) (c m : List Bool)
    (i j : Fin (F.leftOrder c + F.rightOrder c)) (u v : ℕ) :
    F.entry (pair (pair c m) (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
        residueBits (((((Polynomial.sylvester (shiftFamily (F.left c) (F.direction c))
          ((F.right c).map C) (F.leftOrder c) (F.rightOrder c) i j).coeff v).coeff u) : ℤ) :
          ZMod (Nat.fromBitsLE m + 1)) := by
  let z := pair (pair c (BinaryNatCode.encode u)) m
  let enc : ℤ → List Bool := fun x => integerResidue x (Nat.fromBitsLE m + 1)
  have hl (k : ℕ) : F.access.modular.bits.leftCoefficient
      (pair z (pair (BinaryNatCode.encode k) (BinaryNatCode.encode v))) =
      enc (((shiftFamily (slice (F.left c) u) (F.direction c)).coeff k).coeff v) := by
    have h := ShiftCoefficientBits.Family.value_packet F.sliced.shiftSource z k v
    change F.sliced.shiftSource.value _ = integerResidue _ (Nat.fromBitsLE (pairSnd z) + 1) at h
    change F.sliced.shiftSource.value _ = _
    rw [h]
    simp only [CannyResultantBits.Family.shiftSource, Family.sliced, z, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, enc]
  have hr (k : ℕ) : F.access.modular.bits.rightCoefficient
      (pair z (pair (BinaryNatCode.encode k) (BinaryNatCode.encode v))) =
      enc ((((slice (F.right c) u).map C).coeff k).coeff v) := by
    have h := F.access.rightCoefficient_eq z k
    change F.access.rightCoefficient (pair z (BinaryNatCode.encode k)) =
      integerResidue ((F.sliced.right (pairFst z)).coeff k) (CannyResultantBits.mValue z) at h
    change F.access.constantCoefficient _ = _
    simp only [CannyResultantBits.Access.constantCoefficient, ShiftCoefficientBits.leftIndex,
      ShiftCoefficientBits.rightIndex, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits,
      ShiftCoefficientBits.code_value, BinaryNat.bits_eq_nil_iff, h, Polynomial.coeff_map, Polynomial.coeff_C]
    split_ifs <;> simp only [Family.sliced, z, enc, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, CannyResultantBits.mValue]
    · rfl
  have h := SylvesterPolynomialBits.Access.entry_correct F.access.modular.bits z
    (shiftFamily (slice (F.left c) u) (F.direction c)) ((slice (F.right c) u).map C)
    (F.leftOrder c) (F.rightOrder c) v enc
    (by simp only [CannyResultantBits.Access.modular, Family.access, z, Function.comp_apply, pairFst_pair])
    (by simp only [CannyResultantBits.Access.modular, Family.access, z, Function.comp_apply, pairFst_pair])
    hl hr (by simp [enc, integerResidue, residueBits, BinaryNatCode.encode]) i j
  have hs := sylvester_slice (F.left c) (F.right c) (F.direction c) (F.leftOrder c) (F.rightOrder c) u v i j
  rw [← hs] at h
  change F.entry _ = integerResidue _ (Nat.fromBitsLE m + 1)
  simpa only [Family.entry, Function.comp_apply, entryQuery, z, pairFst_pair, pairSnd_pair,
    CannyResultantBits.Access.modular, ResultantPolynomial.ModularAccess.determinant, enc] using h

end LeanCanny.Algebra.SymbolicFixedTableEntryBits
