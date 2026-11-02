/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightTableRead
public import LeanCanny.Algebra.ModularFoldFP
/-! # Native bank multiplication consumes a previously charged reply table -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightBankProductBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHeightTableReadBits (number residueRead)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def scalar (P : Parameters) (z : List Bool) (i : ℕ) : ZMod (modulus P (pairFst z)) := number P z i
noncomputable def value (P : Parameters) (z : List Bool) :=
  residueBits (∏ i ∈ Finset.range (birth P (pairFst z)), scalar P z i)

theorem value_FP (P : Parameters) (a : Access P) : value P ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  exact ModularProduct.evaluatorWithModulus_FP (residueRead P) (fun z => BinaryNatCode.encode (modulus P (pairFst z)))
    (fun z => birth P (pairFst z)) (IntegralMixedFramedHeightTableReadBits.residueRead_FP P a) HM.bits_mem_FP
    ((IntegralMixedOldHeightBits.birth_unary P a).comp pairFst_mem_FP) (fun z => modulus P (pairFst z))
    (funext fun _ => Nat.fromBitsLE_bits _) (scalar P)
    (fun z => Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z)))
    (fun z i _ => IntegralMixedFramedHeightTableReadBits.residueRead_packet P z i)

theorem number_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : ℕ) (hi : i < birth P q) :
    number P (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) i =
      (((IntegralMixedOldBankCofactorBits.scalars P (IntegralMixedFramedOldHeightBits.bankFamily P D J) (birth P)).scale q i : ℤ) : ZMod (modulus P q)).val := by
  rw [IntegralMixedFramedHeightTableReadBits.number_value P D J q i (by unfold IntegralMixedFramedHeightTablePassBits.count; omega)]
  unfold IntegralMixedFramedHeightTablePassBits.entry IntegralMixedFramedHeightTablePassBits.entryWord
  rw [dite_eq_left hi]
  simp only [residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  change _ = ((IntegralMixedBankCofactor.scale (IntegralMixedVirtualTaskBits.family P (IntegralMixedFramedOldHeightBits.bankFamily P D J)) q i : ZMod (modulus P q))).val
  have HI : i < (IntegralMixedFramedOldHeightBits.bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q) :=
    hi.trans_eq (IntegralMixedFramedOldHeightBits.bank_birth P D J q).symm
  rw [IntegralMixedBankCofactor.scale]
  change _ = (((if h : i < (IntegralMixedFramedOldHeightBits.bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q) then
    ((IntegralMixedFramedOldHeightBits.bankFamily P D J).state (IntegralMixedVirtualTaskBits.saved P q)).bank.denominator ⟨i, h⟩ else 1 : ℤ) : ZMod (modulus P q))).val
  rw [dite_eq_left HI]

theorem value_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    value P (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) =
      residueBits (IntegralMixedHistory.commonDenominator (IntegralMixedFramedOldHeightBits.state P D J q) : ZMod (modulus P q)) := by
  have HS := congrArg (fun c => residueBits (∏ i ∈ Finset.range (birth P c),
      (number P (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q)) i : ZMod (modulus P c))))
    (pairFst_pair q (IntegralMixedFramedHeightTablePassBits.value P D J q))
  refine HS.trans ?_
  have H := IntegralMixedBankCofactor.denominator_eq (IntegralMixedVirtualTaskBits.family P (IntegralMixedFramedOldHeightBits.bankFamily P D J))
    (modulus P) (modulus_ne_zero P) (birth P) q
  have HE : (IntegralMixedOldBankCofactorBits.scalars P (IntegralMixedFramedOldHeightBits.bankFamily P D J) (birth P)).denominator q =
      IntegralMixedHistory.commonDenominator (IntegralMixedFramedOldHeightBits.state P D J q) := H
  rw [← HE]
  unfold CommonHeightBits.Scalars.denominator
  change _ = residueBits ((∏ i ∈ Finset.range ((IntegralMixedFramedOldHeightBits.bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q)),
    (IntegralMixedOldBankCofactorBits.scalars P (IntegralMixedFramedOldHeightBits.bankFamily P D J) (birth P)).scale q i : ℤ) : ZMod (modulus P q))
  rw [IntegralMixedFramedOldHeightBits.bank_birth, Int.cast_prod]
  apply congrArg residueBits
  apply Finset.prod_congr rfl
  intro i hi
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  rw [number_table P D J q i (Finset.mem_range.mp hi), ZMod.natCast_zmod_val]

end LeanCanny.Algebra.IntegralMixedFramedHeightBankProductBits
