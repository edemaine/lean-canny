/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ChineseRemainderDigitSpace
public import LeanCanny.Algebra.IntegerRankSpace

/-!
# Integer magnitude digits from residue access and large-product bit sources

Uniform residue access supplies the rank and sign computations automatically.
The two remaining algorithmic inputs are bit routines for the combined modulus
product and the inverse-weighted integer sum. The resulting routine computes
arbitrary magnitude bits with the complete composed workspace/clock certificate.
Implementing those two bit routines remains necessary for full digit recovery.
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

end LeanCanny.Algebra.IntegerDigitBits
