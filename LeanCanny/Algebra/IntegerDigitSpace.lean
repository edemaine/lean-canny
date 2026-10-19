/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ChineseRemainderDigitSpace
public import LeanCanny.Algebra.IntegerRankSpace
public import LeanCanny.Algebra.IndexedSumSpace

/-!
# Integer magnitude digits from certified residue access

Uniform residue access and an FP binary bit budget supply rank, sign, combined
modulus-product bits, and inverse-weighted integer-sum bits. The resulting
routine computes arbitrary magnitude bits with the complete composed workspace
and clock certificate. The lower-level composition also permits other operand
implementations with the same contracts.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerDigitBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open LeanCanny.Algebra.ChineseRemainder

noncomputable def rankOracle {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (budget : List Bool → List Bool) (hb : budget ∈ FP) (z : List Bool → ℤ)
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z c : ZMod m).val)) :
    SpaceFunction (ArithmeticBits.bitValue (IntegerRankBits.rank budget z)) := by
  have ER := R.precompose ArithmeticBits.sourceQuery ArithmeticBits.sourceQuery_mem_FP
  have EB := mem_FP_comp pairFst_mem_FP hb
  have E := IntegerRankBits.evaluator ER (budget ∘ pairFst) pairSnd EB pairSnd_mem_FP (z ∘ pairFst) (by
    intro p m hm
    simp only [Function.comp_apply, ArithmeticBits.sourceQuery, pairFst_pair, pairSnd_pair]
    exact hres (pairFst p) m hm)
  refine E.congr (funext fun p => ?_)
  simp only [ArithmeticBits.bitValue, IntegerRankBits.rank, IntegerRankBits.system, IntegerSignBits.bound,
    Function.comp_apply]
  rfl

noncomputable def evaluatorOfProducts {rho fm fs : List Bool → List Bool} (R : SpaceFunction rho)
    (budget : List Bool → List Bool) (hb : budget ∈ FP) (z : List Bool → ℤ)
    (hbudget : ∀ c, (z c).natAbs.size ≤ Nat.fromBitsLE (budget c))
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z c : ZMod m).val))
    (EM : SpaceFunction fm) (ES : SpaceFunction fs)
    (hproduct : ∀ c k, (fm (pair c (BinaryNatCode.encode k)))[0]?.getD false =
      (IntegerRankBits.system budget c).product.testBit k)
    (hsum : ∀ c k, (fs (pair c (BinaryNatCode.encode k)))[0]?.getD false =
      ((IntegerRankBits.system budget c).integerSum
        (fun i => (z c : ZMod ((IntegerRankBits.system budget c).modulus i)).val)).testBit k) :
    SpaceFunction (ArithmeticBits.bitValue (fun c => (z c).natAbs)) := by
  let F := fun c => IntegerRankBits.system budget c
  let r := fun c i => (z c : ZMod ((F c).modulus i)).val
  have EQ := rankOracle R budget hb z hres
  have EN := IntegerSignBits.evaluator R budget hb z hbudget hres
  refine magnitudeBitEvaluatorOfOperands (fun c => Nat.fromBitsLE (IntegerSignBits.bound budget c) + 1)
    F r z ?_ ?_ ES EM EQ EN hsum hproduct ?_ ?_
  · intro c i
    let : NeZero ((F c).modulus i) := ⟨((F c).positive i).ne'⟩
    exact ZMod.natCast_zmod_val _
  · intro c
    have hn : Nat.fromBitsLE (IntegerSignBits.bound budget c) = 2 * Nat.fromBitsLE (budget c) + 6 := by
      simp only [IntegerSignBits.bound_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have he := IntegerModular.two_natAbs_lt_lcmUpto (z c) (Nat.fromBitsLE (budget c)) (hbudget c)
    simpa only [F, IntegerRankBits.system, indexedSystem_product, hn] using he
  · intro c k
    exact ArithmeticBits.bitValue_packet (IntegerRankBits.rank budget z) c k
  · intro c
    by_cases hn : z c < 0 <;> simp [hn]

noncomputable def evaluator {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (budget : List Bool → List Bool) (hb : budget ∈ FP) (z : List Bool → ℤ)
    (hbudget : ∀ c, (z c).natAbs.size ≤ Nat.fromBitsLE (budget c))
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z c : ZMod m).val)) :
    SpaceFunction (ArithmeticBits.bitValue (fun c => (z c).natAbs)) := by
  have hbound := IntegerSignBits.bound_mem_FP hb
  refine evaluatorOfProducts R budget hb z hbudget hres
    (IndexedProductBits.productEvaluator (IntegerSignBits.bound budget) hbound)
    (IndexedSumBits.evaluator R (IntegerSignBits.bound budget) hbound) ?_ ?_
  · intro c k
    exact IndexedProductBits.productValue_packet (IntegerSignBits.bound budget) c k
  · intro c k
    exact IndexedSumBits.value_packet (IntegerSignBits.bound budget) rho c (z c) (hres c) k

def magnitudeBitLanguage (z : List Bool → ℤ) : Language :=
  {p | ((z (pairFst p)).natAbs).testBit (Nat.fromBitsLE (pairSnd p)) = true}

theorem magnitudeBitLanguage_mem_PSPACE {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (budget : List Bool → List Bool) (hb : budget ∈ FP) (z : List Bool → ℤ)
    (hbudget : ∀ c, (z c).natAbs.size ≤ Nat.fromBitsLE (budget c))
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z c : ZMod m).val)) :
    magnitudeBitLanguage z ∈ PSPACE := by
  have hflag := (FPPred.getBit id_mem_FP (UnaryFn.const 0)).flag_mem_FP
  apply ((evaluator R budget hb z hbudget hres).decider (fun w => w[0]?.getD false) hflag ?_).mem_PSPACE
  intro p
  simp only [magnitudeBitLanguage, Set.mem_ofPred_eq, ArithmeticBits.bitValue]
  cases ((z (pairFst p)).natAbs).testBit (Nat.fromBitsLE (pairSnd p)) <;> simp

end LeanCanny.Algebra.IntegerDigitBits
