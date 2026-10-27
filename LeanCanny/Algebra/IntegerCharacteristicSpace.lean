/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CharacteristicCoefficientSpace
public import LeanCanny.Algebra.IntegerDeterminantSpaceEntries
public import LeanCanny.Algebra.IntegerZeroSpace

/-! # Native integer characteristic-coefficient zero tests

All modular entry calls are charged to the original space-bounded reader.
Out-of-range coefficient indices return zero. No characteristic polynomial or
coefficient table is materialized, and empty matrices are allowed.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open Berkowitz
open scoped Classical

noncomputable def value (F : IntegerFamily) (index : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits ((((F.matrix (pairFst q)).charpoly.coeff (Nat.fromBitsLE (index (pairFst q)))) : ℤ) :
    ZMod (Nat.fromBitsLE (pairSnd q) + 1))

theorem packet (F : IntegerFamily) (index : List Bool → List Bool) (c m : List Bool) :
    value F index (pair c m) = residueBits
      ((((F.matrix c).charpoly.coeff (Nat.fromBitsLE (index c))) : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hq : pair c m = q
  have hc : pairFst q = c := by rw [← hq, pairFst_pair]
  have hm : pairSnd q = m := by rw [← hq, pairSnd_pair]
  subst c
  subst m
  rfl

theorem evaluator {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) {index : List Bool → List Bool} (hi : index ∈ FP) :
    SpaceFunction (value F index) := by
  have hN : BinaryFn F.dimension := BinaryFn.of_bits (mem_FP_of_eq ha.dimension (fun c => a.dimension_eq c))
  have hp := (BinaryFn.fromBits hi).le hN
  have hp' := hp.comp pairFst_mem_FP
  have H := CharacteristicBits.evaluator a.modular (a.modular_controls ha) (mem_FP_comp pairFst_mem_FP hi) E
  have R := SpaceFunction.branch _ hp'.flag_mem_FP H (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply R.congr
  funext q
  simp only [decide_eq_true_eq]
  by_cases hv : Nat.fromBitsLE (index (pairFst q)) ≤ F.dimension (pairFst q)
  · rw [ite_eq_left hv]
    change residueBits (((F.matrix (pairFst q)).map (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1)))).charpoly.coeff
      (Nat.fromBitsLE (index (pairFst q)) % (F.dimension (pairFst q) + 1))) = _
    rw [Nat.mod_eq_of_lt (by omega), Matrix.charpoly_map, Polynomial.coeff_map]
    rfl
  · rw [ite_eq_right hv]
    have hz : (F.matrix (pairFst q)).charpoly.coeff (Nat.fromBitsLE (index (pairFst q))) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)
    simp only [value, hz, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode]
    rfl

theorem zeroDecider {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) {index budget : List Bool → List Bool} (hi : index ∈ FP) (hb : budget ∈ FP)
    (hbudget : ∀ c, ((F.matrix c).charpoly.coeff (Nat.fromBitsLE (index c))).natAbs.size ≤ Nat.fromBitsLE (budget c)) :
    SpaceDecider {c | (F.matrix c).charpoly.coeff (Nat.fromBitsLE (index c)) = 0} := by
  apply IntegerZeroBits.zeroDecider (evaluator a ha E hi) budget hb
    (fun c => (F.matrix c).charpoly.coeff (Nat.fromBitsLE (index c))) hbudget
  intro c m hm
  generalize hw : BinaryNatCode.encode (m - 1) = w
  have he : Nat.fromBitsLE w + 1 = m := by
    rw [← hw]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    omega
  subst m
  exact packet F index c w

end LeanCanny.Algebra.IntegerCharacteristicBits
