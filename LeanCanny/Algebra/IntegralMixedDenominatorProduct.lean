/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedDenominatorPrefix
/-! # Native common bank denominators from charged prefix tables -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedDenominatorScriptBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralMixedHistory IntegralMixedHistoryScript IntegralMixedDenominatorBits
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def prefixReader (F : Family) (prefixLength : List Bool → ℕ) (p : List Bool) : List Bool :=
  WordList.reader (pair (prefixTable F prefixLength (pairFst p)) (pairSnd p))

theorem prefix_reader_evaluator (F : Family) (a : Access F) (prefixLength : List Bool → ℕ) (hp : UnaryFn prefixLength) :
    SpaceFunction (prefixReader F prefixLength) :=
  (((prefix_table_evaluator F a prefixLength hp).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP _ pairSnd_mem_FP)).postcompose WordList.reader WordList.reader_FP

noncomputable def prefixDenominatorAt (F : Family) (prefixLength : List Bool → ℕ) (c : List Bool) (j : ℕ) : ZMod (F.modulus c) :=
  (((IntegralDenominatorPass.integers (program F) c (prefixCount F prefixLength c))[j]?).getD 0 : ℤ)

theorem prefix_reader_packet (F : Family) (prefixLength : List Bool → ℕ) (c : List Bool) (j : ℕ) :
    prefixReader F prefixLength (pair c (BinaryNatCode.encode j)) = residueBits (prefixDenominatorAt F prefixLength c j) := by
  unfold prefixReader
  rw [pairFst_pair, pairSnd_pair, WordList.reader_packet]
  unfold prefixTable
  rw [WordList.get_encode, List.getElem?_map]
  unfold prefixDenominatorAt
  cases (IntegralDenominatorPass.integers (program F) c (prefixCount F prefixLength c))[j]? with
  | none => simp [residueBits, BinaryNatCode.encode]
  | some z => rfl

theorem prod_getD_zero (v : List ℤ) : (∏ j ∈ Finset.range v.length, (v[j]?).getD 0) = v.prod := by
  rw [Finset.prod_range]
  calc
    (∏ j : Fin v.length, (v[j.val]?).getD 0) = ∏ j : Fin v.length, v[j.val] := by
      apply Finset.prod_congr rfl
      intro j _
      rw [List.getElem?_eq_getElem j.isLt]
      rfl
    _ = v.prod := Fin.prod_univ_getElem v

theorem prefix_product_evaluator (F : Family) (a : Access F) (prefixLength : List Bool → ℕ) (hp : UnaryFn prefixLength) :
    SpaceFunction (fun c => residueBits ((IntegralDenominatorPass.integers (program F) c (prefixCount F prefixLength c)).prod : ZMod (F.modulus c))) := by
  have HC := prefixCount_unary F a prefixLength hp
  have E := ModularProduct.evaluatorWithModulus (prefix_reader_evaluator F a prefixLength hp)
    (fun c => BinaryNatCode.encode (prefixCount F prefixLength c)) (fun c => BinaryNatCode.encode (F.modulus c))
    (BinaryFn.ofUnary HC).bits_mem_FP a.modulus.bits_mem_FP F.modulus (funext fun _ => Nat.fromBitsLE_bits _)
    (prefixDenominatorAt F prefixLength) (fun c => Nat.pos_of_ne_zero (F.modulus_ne_zero c))
    (fun c j _ => prefix_reader_packet F prefixLength c j)
  refine E.congr (funext fun c => ?_)
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold prefixDenominatorAt
  rw [← Int.cast_prod]
  apply congrArg (fun z : ℤ => residueBits (z : ZMod (F.modulus c)))
  simpa only [IntegralDenominatorPass.integers_length] using prod_getD_zero (IntegralDenominatorPass.integers (program F) c (prefixCount F prefixLength c))

theorem actual_common_evaluator (F : Family) (a : Access F) (prefixLength : List Bool → ℕ) (hp : UnaryFn prefixLength)
    (S m : List Bool → ℕ) (ι : List Bool → Type)
    (x : ∀ c, State (F.spatial c) (S c) (F.width c) (m c) (ι c))
    (hx : ∀ c, bankList (x c) = IntegralDenominatorPass.integers (program F) c (prefixCount F prefixLength c)) :
    SpaceFunction (fun c => residueBits (commonDenominator (x c) : ZMod (F.modulus c))) :=
  (prefix_product_evaluator F a prefixLength hp).congr (funext fun c =>
    congrArg (fun z : ℤ => residueBits (z : ZMod (F.modulus c))) ((congrArg List.prod (hx c)).symm.trans (bankList_prod (x c))))
end LeanCanny.Algebra.IntegralMixedDenominatorScriptBits
