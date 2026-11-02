/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightCellAccess
public import LeanCanny.Algebra.ModularSumSpace
/-! # Modular affine-reference sums from original cells and charged table replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightReferenceSumBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (cell Primitive)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus BinaryNat.mulMod BinaryNat.mod

def multiply (P : Parameters) (p : List Bool) :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (modulus P (pairFst (pairFst p)))) (pairSnd p))

theorem multiply_FP (P : Parameters) (a : Access P) : multiply P ∈ FP := by
  have HM : BinaryFn (fun p => modulus P (pairFst (pairFst p))) := (modulus_binary P a).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP) BinaryNat.mulMod_mem_FP

theorem multiply_packet (P : Parameters) (z : List Bool) (x y : ZMod (modulus P (pairFst z))) :
    multiply P (pair z (pair (residueBits x) (residueBits y))) = residueBits (x * y) := by
  simp only [multiply, pairFst_pair, pairSnd_pair]
  exact ArithmeticBits.mulMod_residueBits _ x y

def shiftQuery (P : Parameters) (p : List Bool) := pair (pairFst p)
  (BinaryNatCode.encode (birth P (pairFst (pairFst p)) + Nat.fromBitsLE (pairSnd p)))

theorem shiftQuery_FP (P : Parameters) (a : Access P) : shiftQuery P ∈ FP := by
  have HB : BinaryFn (fun p => birth P (pairFst (pairFst p))) :=
    (BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a)).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  exact mem_FP_pair pairFst_mem_FP (HB.add (BinaryFn.fromBits pairSnd_mem_FP)).bits_mem_FP

def heightRead (P : Parameters) := IntegralMixedFramedHeightTableReadBits.residueRead P ∘ shiftQuery P

theorem heightRead_FP (P : Parameters) (a : Access P) : heightRead P ∈ FP :=
  mem_FP_comp (shiftQuery_FP P a) (IntegralMixedFramedHeightTableReadBits.residueRead_FP P a)

theorem heightRead_packet (P : Parameters) (z : List Bool) (i : ℕ) :
    heightRead P (pair z (BinaryNatCode.encode i)) = residueBits
      (IntegralMixedFramedHeightTableReadBits.number P z (birth P (pairFst z) + i) : ZMod (modulus P (pairFst z))) := by
  simp only [heightRead, Function.comp_apply, shiftQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact IntegralMixedFramedHeightTableReadBits.residueRead_packet P z _

noncomputable def term (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (p : List Bool) :=
  multiply P (pair (pairFst p) (pair (IntegralMixedFramedHeightCellAccessBits.read P D J 1 p) (heightRead P p)))

theorem term_space (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : Primitive P D J) :
    SpaceFunction (term P D J) :=
  ((SpaceFunction.ofFP _ pairFst_mem_FP).pairOutputs ((IntegralMixedFramedHeightCellAccessBits.read_space P D J hp 1).pairOutputs
    (SpaceFunction.ofFP _ (heightRead_FP P a)))).postcompose (multiply P) (multiply_FP P a)

noncomputable def scalar (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) (i : ℕ) :
    ZMod (modulus P (pairFst z)) :=
  (cell P D J (pairFst z) 1 i : ZMod (modulus P (pairFst z))) *
    (IntegralMixedFramedHeightTableReadBits.number P z (birth P (pairFst z) + i) : ZMod (modulus P (pairFst z)))

theorem term_packet (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) (i : ℕ) :
    term P D J (pair z (BinaryNatCode.encode i)) = residueBits (scalar P D J z i) := by
  rw [term, pairFst_pair, IntegralMixedFramedHeightCellAccessBits.read_packet, heightRead_packet, multiply_packet]
  rfl

noncomputable def value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :=
  residueBits (∑ i ∈ Finset.range (birth P (pairFst z)), scalar P D J z i)

theorem value_space (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : Primitive P D J) :
    SpaceFunction (value P D J) := by
  have HC : BinaryFn (fun z => birth P (pairFst z)) := (BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a)).comp pairFst_mem_FP
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have E := ModularSum.evaluatorWithModulus (term_space P a D J hp) (fun z => BinaryNatCode.encode (birth P (pairFst z)))
    (fun z => BinaryNatCode.encode (modulus P (pairFst z))) HC.bits_mem_FP HM.bits_mem_FP
    (fun z => modulus P (pairFst z)) (funext fun _ => Nat.fromBitsLE_bits _) (scalar P D J)
    (fun z => Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z))) (fun z i _ => term_packet P D J z i)
  exact E.congr (funext fun z => by simp only [value, BinaryNatCode.encode, Nat.fromBitsLE_bits])

end LeanCanny.Algebra.IntegralMixedFramedHeightReferenceSumBits
