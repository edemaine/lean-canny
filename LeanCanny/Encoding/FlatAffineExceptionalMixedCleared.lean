/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalMixedGenerators

/-! # Native omitted denominators of the actual retained initial bank

A cleared retained numerator uses the product of every other original
integer leading coefficient. This product is streamed through the native
Space leading reader; the selected factor is replaced by one, including
for negative or nonunit leadings.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalMixedHistory
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width finitePolynomial)
open scoped Classical BigOperators
attribute [local irreducible] FlatAffineExceptionalBankSource.polynomial FlatAffineExceptionalBankSource.leading

noncomputable def omittedDenominator (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (i : Fin (births F u)) : ℤ :=
  ∏ j : Fin (births F u), if j = i then 1 else (finitePolynomial F C h u j).leadingCoeff

theorem omittedDenominator_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (i : Fin (births F u)) :
    omittedDenominator F C h u i = CommonIntegerDenominator.denominator
      (Finset.univ.erase i) (initial F C h S u hm).bank.denominator := by
  unfold omittedDenominator CommonIntegerDenominator.denominator
  rw [← Finset.prod_erase (a := i) Finset.univ (by simp)]
  apply Finset.prod_congr rfl
  intro j hj
  have H : j ≠ i := (Finset.mem_erase.mp hj).1
  rw [ite_eq_right H]
  exact (FlatAffineExceptionalParentBank.denominator_eq F C h S u hm j).symm

def omittedLeadingQuery (modulus : List Bool → ℕ) (q : List Bool) :=
  pair (pair (pairFst (pairFst q)) (pairSnd q)) (BinaryNatCode.encode (modulus (pairFst q) - 1))

theorem omittedLeadingQuery_FP {modulus : List Bool → ℕ} (hM : BinaryFn modulus) : omittedLeadingQuery modulus ∈ FP := by
  have HM : BinaryFn (fun q => modulus (pairFst q)) := hM.comp pairFst_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (HM.sub (BinaryFn.const 1)).bits_mem_FP

theorem omittedDenominator_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (i : ∀ q, Fin (births F (pairFst q))) (hi : BinaryFn (fun q => (i q).val))
    (modulus : List Bool → ℕ) (hmod : ∀ q, modulus q ≠ 0) (hM : BinaryFn modulus) :
    SpaceFunction (fun q => residueBits (omittedDenominator F C h (pairFst q) (i q) : ZMod (modulus q))) := by
  have E := (FlatAffineExceptionalBankSource.leading_evaluator hF C h hh).precompose
    (omittedLeadingQuery modulus) (omittedLeadingQuery_FP hM)
  have G := (BinaryFn.fromBits pairSnd_mem_FP).eq (hi.comp pairFst_mem_FP)
  have EO : SpaceFunction (fun z => residueBits (1 : ZMod (modulus (pairFst z)))) :=
    (SpaceFunction.ofFP _ (ModularScalarFP.natCast (hM.comp pairFst_mem_FP) (fun _ => 1) (BinaryFn.const 1))).congr
      (funext fun _ => by simp only [Nat.cast_one])
  have EF := SpaceFunction.branch _ G.flag_mem_FP EO E
  have H := ModularProduct.evaluatorWithModulus EF
    (fun q => BinaryNatCode.encode (births F (pairFst q))) (fun q => BinaryNatCode.encode (modulus q))
    (BinaryFn.ofUnary ((FlatAffineExceptionalBankSource.births_unary hF).comp pairFst_mem_FP)).bits_mem_FP
    hM.bits_mem_FP modulus (funext fun _ => Nat.fromBitsLE_bits _)
    (fun q j => if j = (i q).val then 1 else
      ((FlatAffineExceptionalBankSource.polynomial F C h (pair (pairFst q) (BinaryNatCode.encode j))).leadingCoeff : ZMod (modulus q)))
    (fun q => Nat.pos_of_ne_zero (hmod q)) (fun q j _ => ?_)
  · exact H.congr (funext fun q => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      unfold omittedDenominator
      rw [Int.cast_prod]
      congr 1
      rw [← Fin.prod_univ_eq_prod_range]
      apply Finset.prod_congr rfl
      intro j _
      simp only [finitePolynomial, Int.cast_ite, Int.cast_one, Fin.ext_iff]
      rfl)
  · simp only [Function.comp_apply, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have HI : (i (pairFst (pair q j.bits))).val = (i q).val :=
      congrArg (fun z : List Bool => (i z).val) (pairFst_pair q j.bits)
    rw [HI]
    by_cases hj : j = (i q).val
    · simp only [hj, decide_true, ite_true]
      exact congrArg (fun z : List Bool => residueBits (1 : ZMod (modulus z))) (pairFst_pair q j.bits)
    · simp only [hj, decide_false, Bool.false_eq_true, ite_false]
      have HM : Nat.fromBitsLE (BinaryNatCode.encode (modulus q - 1)) + 1 = modulus q := by
        simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
        have HP := Nat.pos_of_ne_zero (hmod q)
        omega
      have HQ : omittedLeadingQuery modulus (pair q j.bits) =
          pair (pair (pairFst q) j.bits) (BinaryNatCode.encode (modulus q - 1)) := by
        simp only [omittedLeadingQuery, pairFst_pair, pairSnd_pair]
      have HL := FlatAffineExceptionalBankSource.leading_packet F C h
        (pair (pairFst q) (BinaryNatCode.encode j)) (BinaryNatCode.encode (modulus q - 1))
      rw [HQ]
      have HD := congrArg (fun m : ℕ => residueBits
        ((FlatAffineExceptionalBankSource.polynomial F C h (pair (pairFst q) (BinaryNatCode.encode j))).leadingCoeff : ZMod m)) HM
      exact HL.trans HD

end LeanCanny.Encoding.FlatAffineExceptionalMixedHistory
