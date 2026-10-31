/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralHeightEntry

/-! # Native entries of actual canonical height-numerator matrices

An ordered product combines the constructed new generator with the
lifted inverse matrix. All coefficient reads return to the original
source, including internal characteristic scans. The numerator matrix
is computed internally rather than supplied by another reader.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralHeightSourceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open PaddedIntegralGeneratorSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def family (S : Source) : MatrixProductBits.Family where
  width := rank S
  count _ := 2
  modulus q := Nat.fromBitsLE (modulus q) + 1
  row := index S row
  col := index S col
  factor q k := (if k = 0 then S.matrix (base q) else PaddedIntegralHeightSourceMatrix.liftMatrix S (base q)).map
    (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus q) + 1)))
  modulus_ne_zero _ := by omega

attribute [local irreducible] Source.matrix PaddedIntegralHeightSourceMatrix.liftMatrix PaddedIntegralHeightSourceMatrix.matrix

noncomputable def access (S : Source) (B : PaddedIntegralSelectedMatrixSource.Bounds S) (a : Access S) :
    MatrixProductBits.Access (family S) where
  width := rank_binary S a
  count := BinaryFn.const 2
  modulus := (BinaryFn.fromBits modulus_FP).add (BinaryFn.const 1)
  row := index_binary S a row row_FP
  col := index_binary S a col col_FP
  entry := PaddedIntegralHeightEntryBits.entry S B
  entry_eq q k i j := by
    have HK : PaddedIntegralHeightEntryBits.factor
        (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = k := by
      simp only [PaddedIntegralHeightEntryBits.factor, PaddedIntegralHeightEntryBits.factorCode,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    change PaddedIntegralHeightEntryBits.entry S B
      (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((if k = 0 then S.matrix (base q) else PaddedIntegralHeightSourceMatrix.liftMatrix S (base q)).map
        (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus q) + 1))) i j)
    rw [PaddedIntegralHeightEntryBits.entry, HK]
    by_cases hk : k = 0
    · rw [ite_eq_left hk, ite_eq_left hk]
      exact PaddedIntegralHeightEntryBits.root_packet S q k i j
    · rw [ite_eq_right hk, ite_eq_right hk]
      exact PaddedIntegralHeightEntryBits.lift_packet S B q k i j

noncomputable def value (S : Source) (q : List Bool) : List Bool :=
  residueBits ((PaddedIntegralHeightSourceMatrix.matrix S (base q) (index S row q) (index S col q) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus q) + 1))

theorem value_eq (S : Source) : (family S).value = value S := by
  funext q
  rw [MatrixProductBits.Family.value]
  change residueBits (MatrixProduct.product
    (fun k => (if k = 0 then S.matrix (base q) else PaddedIntegralHeightSourceMatrix.liftMatrix S (base q)).map
      (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus q) + 1)))) 0 2 (index S row q) (index S col q)) = _
  simp only [MatrixProduct.product, Nat.reduceAdd, ite_eq_right (by decide : (1 : ℕ) ≠ 0),
    mul_one, ← Matrix.map_mul, Matrix.map_apply]
  exact congrArg (fun M : Matrix (Fin (rank S q)) (Fin (rank S q)) ℤ =>
    residueBits ((M (index S row q) (index S col q) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1)))
      (PaddedIntegralHeightSourceMatrix.matrix_eq S (base q)).symm

theorem evaluator (S : Source) (B : PaddedIntegralSelectedMatrixSource.Bounds S) (a : Access S)
    (hh : BinaryFn B.height) (E : SpaceFunction a.entry) : SpaceFunction (value S) :=
  (MatrixProductBits.evaluator (family S) (access S B a) (PaddedIntegralHeightEntryBits.entry_evaluator S B a hh E)).congr
    (value_eq S)

theorem value_packet (S : Source) (c mw : List Bool) (i j : Fin (FixedWidthPolynomial.count (S.arity c + 1) (S.width c))) :
    value S (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((PaddedIntegralHeightSourceMatrix.matrix S c i j : ℤ) : ZMod (Nat.fromBitsLE mw + 1)) := by
  generalize hz : pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) = q
  have hb : base q = c := by rw [base, ← hz, pairFst_pair, pairFst_pair]
  have hm : modulus q = mw := by rw [modulus, ← hz, pairFst_pair, pairSnd_pair]
  have hr : (index S row q).val = i.val := by rw [← hz]; exact row_packet S c mw i j
  have hc : (index S col q).val = j.val := by rw [← hz]; exact col_packet S c mw i j
  subst c
  subst mw
  have HI : index S row q = i := Fin.ext hr
  have HJ : index S col q = j := Fin.ext hc
  have HP : ((index S row q, index S col q) : Fin (rank S q) × Fin (rank S q)) = (i, j) := Prod.ext HI HJ
  exact congrArg (fun rc : Fin (rank S q) × Fin (rank S q) =>
    residueBits ((PaddedIntegralHeightSourceMatrix.matrix S (base q) rc.1 rc.2 : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1))) HP

end LeanCanny.Algebra.PaddedIntegralHeightSourceBits
