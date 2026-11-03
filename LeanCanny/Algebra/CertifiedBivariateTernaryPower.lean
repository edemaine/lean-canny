/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.BivariateProductSpace
public import LeanCanny.Algebra.FixedWidthBivariateReboxSpace
/-! # Native powers zero, one and two retain one bivariate source reader -/
@[expose] public section
namespace LeanCanny.Algebra.CertifiedBivariateTernaryPower
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open FixedWidthBivariateReboxBits (target modulus outer)
open scoped Classical
attribute [local irreducible] BinaryNat.succ ArithmeticBits.one

noncomputable def oneValue (z : List Bool) :=
  if Nat.fromBitsLE (target z)=0 ∧ outer z=0 then ArithmeticBits.one (BinaryNat.succ (modulus z)) else []

theorem oneValue_FP : oneValue∈FP :=by
  have HT : target∈FP:=by polytime [target]
  have HM : modulus∈FP:=by polytime [modulus]
  have HY : BinaryFn outer:=BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have H:=((BinaryFn.fromBits HT).eq (BinaryFn.const 0)).and (HY.eq (BinaryFn.const 0))
  have HS : (fun z=>BinaryNat.succ (modulus z))∈FP:=mem_FP_comp HM BinaryNat.succ_mem_FP
  have EO : (fun z=>ArithmeticBits.one (BinaryNat.succ (modulus z)))∈FP:=mem_FP_comp HS ArithmeticBits.one_mem_FP
  exact H.ite_mem_FP EO (constFn_mem_FP [])

noncomputable def oneReader : CertifiedPolynomial.BivariateReader (fun _=>(1 : Polynomial (Polynomial ℤ))) where
  coefficient:=oneValue
  evaluator:=SpaceFunction.ofFP _ oneValue_FP
  coefficient_eq q u v:=by
    simp only [oneValue,target,modulus,outer,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    by_cases hu : u=0 <;> by_cases hv : v=0
    · simp only [hu,hv,and_self,ite_true,Polynomial.coeff_one,ite_true]
      rw [BinaryNat.succ_eq_bits]
      change ArithmeticBits.one (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)+1))=
        residueBits (1 : ZMod (Nat.fromBitsLE (pairSnd q)+1))
      exact ArithmeticBits.one_residueBits _
    · simp only [hu,and_false,ite_false,Polynomial.coeff_one,hv,ite_false,Polynomial.coeff_zero,Int.cast_zero]
      simp only [residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]
    · simp only [hu,hv,false_and,ite_false,Polynomial.coeff_one,ite_true,ite_false,Int.cast_zero]
      simp only [residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]
    · simp only [hu,hv,false_and,ite_false,Polynomial.coeff_one,ite_false,Polynomial.coeff_zero,Int.cast_zero]
      simp only [residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

noncomputable def value {p : List Bool→Polynomial (Polynomial ℤ)} (R : CertifiedPolynomial.BivariateReader p)
    (e : List Bool→Fin 3) (z : List Bool) :=
  if (e (FixedWidthBivariateReader.origin z)).val=0 then oneValue z else
    if (e (FixedWidthBivariateReader.origin z)).val=1 then R.coefficient z else
      (CertifiedPolynomial.BivariateProduct.reader R R).coefficient z

theorem evaluator {p : List Bool→Polynomial (Polynomial ℤ)} (R : CertifiedPolynomial.BivariateReader p)
    (e : List Bool→Fin 3) (he : BinaryFn (fun c=>(e c).val)) : SpaceFunction (value R e) :=by
  have HE : BinaryFn (fun z=>(e (FixedWidthBivariateReader.origin z)).val):=he.comp FixedWidthBivariateReader.origin_FP
  have E1:=SpaceFunction.branch (fun z=>decide ((e (FixedWidthBivariateReader.origin z)).val=1))
    (HE.eq (BinaryFn.const 1)).flag_mem_FP R.evaluator (CertifiedPolynomial.BivariateProduct.reader R R).evaluator
  have E:=SpaceFunction.branch (fun z=>decide ((e (FixedWidthBivariateReader.origin z)).val=0))
    (HE.eq (BinaryFn.const 0)).flag_mem_FP oneReader.evaluator E1
  exact E.congr (funext fun z=>by simp only [value,oneReader,decide_eq_true_eq])

noncomputable def reader {p : List Bool→Polynomial (Polynomial ℤ)} (R : CertifiedPolynomial.BivariateReader p)
    (e : List Bool→Fin 3) (he : BinaryFn (fun c=>(e c).val)) :
    CertifiedPolynomial.BivariateReader (fun c=>p c^(e c).val) where
  coefficient:=value R e
  evaluator:=evaluator R e he
  coefficient_eq q u v:=by
    unfold value
    simp only [FixedWidthBivariateReader.origin,pairFst_pair]
    by_cases H0 : (e (pairFst q)).val=0
    · rw [ite_eq_left H0]
      exact (oneReader.coefficient_eq q u v).trans (by rw [H0,pow_zero])
    · rw [ite_eq_right H0]
      by_cases H1 : (e (pairFst q)).val=1
      · rw [ite_eq_left H1]
        exact (R.coefficient_eq q u v).trans (by rw [H1,pow_one])
      · rw [ite_eq_right H1]
        have H2 : (e (pairFst q)).val=2:=by have H:=(e (pairFst q)).isLt;omega
        exact ((CertifiedPolynomial.BivariateProduct.reader R R).coefficient_eq q u v).trans
          (by rw [H2,pow_two])

end LeanCanny.Algebra.CertifiedBivariateTernaryPower
