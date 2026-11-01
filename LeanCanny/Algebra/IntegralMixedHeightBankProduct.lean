/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightTableRead
public import LeanCanny.Algebra.ModularFoldFP
/-! # Native bank multiplication consumes a previously charged reply table -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightBankProductBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHeightTableReadBits (number residueRead)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def scalar (P : Parameters) (z : List Bool) (i : ℕ) : ZMod (modulus P (pairFst z)) := number P z i
noncomputable def value (P : Parameters) (z : List Bool) :=
  residueBits (∏ i ∈ Finset.range (birth P (pairFst z)), scalar P z i)

theorem value_FP (P : Parameters) (a : Access P) : value P ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  exact ModularProduct.evaluatorWithModulus_FP (residueRead P) (fun z => BinaryNatCode.encode (modulus P (pairFst z)))
    (fun z => birth P (pairFst z)) (IntegralMixedHeightTableReadBits.residueRead_FP P a) HM.bits_mem_FP
    ((IntegralMixedOldHeightBits.birth_unary P a).comp pairFst_mem_FP) (fun z => modulus P (pairFst z))
    (funext fun _ => Nat.fromBitsLE_bits _) (scalar P)
    (fun z => Nat.pos_of_ne_zero (modulus_ne_zero P (pairFst z)))
    (fun z i _ => IntegralMixedHeightTableReadBits.residueRead_packet P z i)

theorem number_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : ℕ) (hi : i < birth P q) :
    number P (pair q (IntegralMixedHeightTablePassBits.value P D q)) i =
      (((IntegralMixedOldBankCofactorBits.scalars P (IntegralMixedOldHeightBits.bankFamily P D) (birth P)).scale q i : ℤ) : ZMod (modulus P q)).val := by
  rw [IntegralMixedHeightTableReadBits.number_value P D q i (by unfold IntegralMixedHeightTablePassBits.count; omega)]
  unfold IntegralMixedHeightTablePassBits.entry IntegralMixedHeightTablePassBits.entryWord
  rw [dite_eq_left hi]
  simp only [residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  change _ = ((IntegralMixedBankCofactor.scale (IntegralMixedVirtualTaskBits.family P (IntegralMixedOldHeightBits.bankFamily P D)) q i : ZMod (modulus P q))).val
  have HI : i < (IntegralMixedOldHeightBits.bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q) :=
    hi.trans_eq (IntegralMixedOldHeightBits.bank_birth P D q).symm
  rw [IntegralMixedBankCofactor.scale]
  change _ = (((if h : i < (IntegralMixedOldHeightBits.bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q) then
    ((IntegralMixedOldHeightBits.bankFamily P D).state (IntegralMixedVirtualTaskBits.saved P q)).bank.denominator ⟨i, h⟩ else 1 : ℤ) : ZMod (modulus P q))).val
  rw [dite_eq_left HI]

theorem value_table (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    value P (pair q (IntegralMixedHeightTablePassBits.value P D q)) =
      residueBits (IntegralMixedHistory.commonDenominator (IntegralMixedOldHeightBits.state P D q) : ZMod (modulus P q)) := by
  have HS := congrArg (fun c => residueBits (∏ i ∈ Finset.range (birth P c),
      (number P (pair q (IntegralMixedHeightTablePassBits.value P D q)) i : ZMod (modulus P c))))
    (pairFst_pair q (IntegralMixedHeightTablePassBits.value P D q))
  refine HS.trans ?_
  have H := IntegralMixedBankCofactor.denominator_eq (IntegralMixedVirtualTaskBits.family P (IntegralMixedOldHeightBits.bankFamily P D))
    (modulus P) (modulus_ne_zero P) (birth P) q
  have HE : (IntegralMixedOldBankCofactorBits.scalars P (IntegralMixedOldHeightBits.bankFamily P D) (birth P)).denominator q =
      IntegralMixedHistory.commonDenominator (IntegralMixedOldHeightBits.state P D q) := H
  rw [← HE]
  unfold CommonHeightBits.Scalars.denominator
  change _ = residueBits ((∏ i ∈ Finset.range ((IntegralMixedOldHeightBits.bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q)),
    (IntegralMixedOldBankCofactorBits.scalars P (IntegralMixedOldHeightBits.bankFamily P D) (birth P)).scale q i : ℤ) : ZMod (modulus P q))
  rw [IntegralMixedOldHeightBits.bank_birth, Int.cast_prod]
  apply congrArg residueBits
  apply Finset.prod_congr rfl
  intro i hi
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  rw [number_table P D q i (Finset.mem_range.mp hi), ZMod.natCast_zmod_val]

end LeanCanny.Algebra.IntegralMixedHeightBankProductBits
