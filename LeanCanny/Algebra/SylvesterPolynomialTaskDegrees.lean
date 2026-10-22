/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SylvesterPolynomialTaskRouting

/-! # Coefficient indices admitted by Sylvester band guards

The polynomial degree word is copied unchanged. The selected polynomial
index is at most the corresponding supplied source order whenever the band
guard is active, for arbitrary matrix indices and input words.
-/

@[expose] public section

namespace LeanCanny.Algebra.SylvesterPolynomialBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation

def coefficientDegree (p : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairSnd (pairSnd p)))

attribute [local irreducible] BinaryNat.sub BinaryNat.add

theorem rightInput_index (p : List Bool) :
    Nat.fromBitsLE (pairFst (pairSnd (rightInput p))) =
      Nat.fromBitsLE (pairFst (pairSnd p)) - Nat.fromBitsLE (pairFst (pairSnd (pairSnd p))) := by
  simp only [rightInput, PolynomialMoment.vectorInput, SylvesterBits.coefficientInput,
    SylvesterBits.col, SylvesterBits.row, PolynomialMoment.augmentedInput,
    pairFst_pair, pairSnd_pair, BinaryNat.sub_pair, Nat.fromBitsLE_bits]

theorem leftInput_index (a : Access) (p : List Bool) :
    Nat.fromBitsLE (pairFst (pairSnd (leftInput a p))) =
      Nat.fromBitsLE (pairFst (pairSnd p)) -
        (Nat.fromBitsLE (pairFst (pairSnd (pairSnd p))) - Nat.fromBitsLE (a.leftDegree (pairFst p))) := by
  simp only [leftInput, PolynomialMoment.vectorInput, SylvesterBits.coefficientInput,
    SylvesterBits.rightShift, SylvesterBits.leftDegree, SylvesterBits.context, Access.scalarBits,
    SylvesterBits.col, SylvesterBits.row, PolynomialMoment.augmentedInput,
    pairFst_pair, pairSnd_pair, BinaryNat.sub_pair, Nat.fromBitsLE_bits]

theorem rightInput_degree (p : List Bool) :
    Nat.fromBitsLE (pairSnd (pairSnd (rightInput p))) = coefficientDegree p := by
  simp only [rightInput, PolynomialMoment.vectorInput, SylvesterBits.coefficientInput,
    PolynomialMoment.augmentedInput, pairFst_pair, pairSnd_pair, coefficientDegree]

theorem leftInput_degree (a : Access) (p : List Bool) :
    Nat.fromBitsLE (pairSnd (pairSnd (leftInput a p))) = coefficientDegree p := by
  simp only [leftInput, PolynomialMoment.vectorInput, SylvesterBits.coefficientInput,
    PolynomialMoment.augmentedInput, pairFst_pair, pairSnd_pair, coefficientDegree]

theorem rightInput_index_le (a : Access) (p : List Bool)
    (ha : active a p = true) (hs : selectRight a p = true) :
    Nat.fromBitsLE (pairFst (pairSnd (rightInput p))) ≤ Nat.fromBitsLE (a.rightDegree (pairFst p)) := by
  simp only [active, hs, ite_true] at ha
  have hb := of_decide_eq_true ha
  simp only [SylvesterBits.bandEnd, SylvesterBits.rightDegree,
    SylvesterBits.context, Access.scalarBits, SylvesterBits.col, SylvesterBits.row, PolynomialMoment.augmentedInput,
    pairFst_pair, pairSnd_pair, BinaryNat.add_pair, Nat.fromBitsLE_bits] at hb
  rw [rightInput_index]
  omega

theorem leftInput_index_le (a : Access) (p : List Bool)
    (ha : active a p = true) (hs : selectRight a p = false) :
    Nat.fromBitsLE (pairFst (pairSnd (leftInput a p))) ≤ Nat.fromBitsLE (a.leftDegree (pairFst p)) := by
  simp only [active, hs, Bool.false_eq_true, ite_false] at ha
  have hb := of_decide_eq_true ha
  simp only [SylvesterBits.bandEnd, SylvesterBits.leftDegree,
    SylvesterBits.rightShift, SylvesterBits.context, Access.scalarBits, SylvesterBits.col, SylvesterBits.row,
    PolynomialMoment.augmentedInput, pairFst_pair, pairSnd_pair, BinaryNat.add_pair, BinaryNat.sub_pair,
    Nat.fromBitsLE_bits] at hb
  rw [leftInput_index]
  omega

end LeanCanny.Algebra.SylvesterPolynomialBits.RecursiveStage
