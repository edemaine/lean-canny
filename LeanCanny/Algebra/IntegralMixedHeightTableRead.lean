/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightTablePass
/-! # Native modular reads of the literal charged affine-height table -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightTableReadBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHeightTablePassBits (count width entry entryWord value)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem entry_lt (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (i : ℕ) :
    IntegralMixedHeightTablePassBits.entry P D q i < modulus P q := by
  unfold IntegralMixedHeightTablePassBits.entry entryWord
  split_ifs
  · simp only [residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact ZMod.val_lt _
  · let c := IntegralMixedHeightTableQueryBits.writer P (pair q (BinaryNatCode.encode (i - birth P q)))
    obtain ⟨z, hz⟩ := IntegralMixedOldHeightBits.value_canonical P D c
    rw [← hz]
    simp only [residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    let : NeZero (modulus P c) := ⟨modulus_ne_zero P c⟩
    exact (ZMod.val_lt z).trans_eq (IntegralMixedHeightTableQueryBits.writer_modulus P q _)

theorem entry_bits_lt (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (i : ℕ) :
    IntegralMixedHeightTablePassBits.entry P D q i < 2 ^ width P q := (entry_lt P D q i).trans (Nat.lt_size_self _)

attribute [local irreducible] IntegralMixedHeightTablePassBits.entry IntegralMixedHeightTablePassBits.value modulus

def read (P : Parameters) := FixedWidthQuery.read (count P ∘ pairFst) (width P ∘ pairFst) pairSnd

theorem read_FP (P : Parameters) (a : Access P) : read P ∈ FP :=
  FixedWidthQuery.read_mem_FP ((IntegralMixedHeightTablePassBits.count_unary P a).comp pairFst_mem_FP)
    ((IntegralMixedHeightTablePassBits.width_unary P a).comp pairFst_mem_FP) pairSnd_mem_FP

def number (P : Parameters) (z : List Bool) (i : ℕ) :=
  FixedWidthQuery.entry (count P ∘ pairFst) (width P ∘ pairFst) pairSnd z i

def residueRead (P : Parameters) (p : List Bool) :=
  BinaryNat.mod (pair (read P p) (BinaryNatCode.encode (modulus P (pairFst (pairFst p)))))

theorem residueRead_FP (P : Parameters) (a : Access P) : residueRead P ∈ FP := by
  have HM : BinaryFn (fun p => modulus P (pairFst (pairFst p))) :=
    (modulus_binary P a).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  exact mem_FP_comp (mem_FP_pair (read_FP P a) HM.bits_mem_FP) BinaryNat.mod_mem_FP

theorem read_packet (P : Parameters) (z : List Bool) (i : ℕ) :
    read P (pair z (BinaryNatCode.encode i)) = BinaryNatCode.encode (number P z i) :=
  FixedWidthQuery.read_packet _ _ _ z i

theorem residueRead_packet (P : Parameters) (z : List Bool) (i : ℕ) :
    residueRead P (pair z (BinaryNatCode.encode i)) =
      residueBits (number P z i : ZMod (modulus P (pairFst z))) := by
  rw [residueRead, read_packet, BinaryNat.mod_pair]
  simp only [pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, residueBits, ZMod.val_natCast]

theorem number_value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : ℕ) (hi : i < count P q) : number P (pair q (value P D q)) i = IntegralMixedHeightTablePassBits.entry P D q i := by
  unfold number FixedWidthQuery.entry
  simp only [Function.comp_apply, pairFst_pair, ite_eq_left hi, FixedWidthQuery.coordinate, pairSnd_pair]
  unfold IntegralMixedHeightTablePassBits.value
  exact FixedWidthNatVector.decode_block _ _ _ i hi (entry_bits_lt P D q i)

theorem residueRead_value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : ℕ) (hi : i < count P q) :
    residueRead P (pair (pair q (value P D q)) (BinaryNatCode.encode i)) = entryWord P D q i := by
  rw [residueRead_packet, number_value P D q i hi]
  have H : residueBits (IntegralMixedHeightTablePassBits.entry P D q i : ZMod (modulus P q)) =
      BinaryNatCode.encode (IntegralMixedHeightTablePassBits.entry P D q i) := by
    simp only [residueBits, ZMod.val_natCast, Nat.mod_eq_of_lt (entry_lt P D q i)]
  have HM := congrArg (modulus P) (pairFst_pair q (IntegralMixedHeightTablePassBits.value P D q))
  have HC := congrArg (fun m => residueBits (IntegralMixedHeightTablePassBits.entry P D q i : ZMod m)) HM
  exact HC.trans (H.trans (IntegralMixedHeightTablePassBits.entry_normalized P D q i))

end LeanCanny.Algebra.IntegralMixedHeightTableReadBits
