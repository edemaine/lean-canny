/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegerPolynomialExpandSource
public import LeanCanny.Algebra.ModularResidueSpace
public import LeanCanny.Computation.PolyTimeBinaryArithmetic

/-! # Native coefficient access after scalar power substitution

A positive binary substitution degree only divides the requested coefficient
index. The original coefficient machine and caller modulus are retained.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegerPolynomialExpandSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue)
open scoped Classical

def query (d : List Bool→ℕ) (z : List Bool) :=
  pair (pair (context z) (BinaryNatCode.encode (Nat.fromBitsLE (selectedDegree z)/d (context z)))) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd z)))

theorem query_FP {d : List Bool→ℕ} (hd : BinaryFn d) : query d∈FP :=
  mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP
    ((BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP).div
      (hd.comp RationalSubstitution.IntegerBits.context_mem_FP)).bits_mem_FP)
      (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP

theorem query_value (S : IntegerPolynomialRootQueriesBits.Source) (d : List Bool→ℕ) (z : List Bool) :
    PrimitivePairBits.coefficient S.polynomial (query d z)=residueBits
      (((S.polynomial (context z)).coeff (Nat.fromBitsLE (selectedDegree z)/d (context z)) : ℤ) : ZMod (mValue z)) := by
  have H : query d z=pair (pair (context z)
      (BinaryNatCode.encode (Nat.fromBitsLE (selectedDegree z)/d (context z))))
        (BinaryNatCode.encode (mValue z-1)) := by
    simp only [query,mValue,Nat.add_sub_cancel]
  rw [H,IntegerPolynomialRootQueriesBits.coefficient_packet _ _ _ (mValue z) (by unfold mValue; omega)]
  rfl

theorem coefficient_evaluator (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
    {d : List Bool→ℕ} (hd : BinaryFn d) (hpos : ∀ q,0<d q) :
    SpaceFunction (PrimitivePairBits.coefficient (source S d).polynomial) := by
  have E:=(hS.coefficient.precompose (query d) (query_FP hd)).congr (funext (query_value S d))
  have EZ : SpaceFunction (fun z=>residueBits (0 : ZMod (mValue z))) := by
    exact (SpaceFunction.ofFP (fun _ : List Bool=>[]) (constFn_mem_FP [])).congr (funext fun _=>by simp [residueBits,BinaryNatCode.encode])
  have HK:=BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  have HM:=(HK.mod (hd.comp RationalSubstitution.IntegerBits.context_mem_FP)).eq (BinaryFn.const 0)
  have EB:=ModularResidueSpace.branchEvaluator pairSnd _ _
    (fun z=>Nat.fromBitsLE (selectedDegree z)%d (context z)=0) HM E EZ
  refine EB.congr (funext fun z=>?_)
  unfold PrimitivePairBits.coefficient RationalSubstitution.IntegerBits.coefficientResidue
  rw [show (source S d).polynomial (context z)=Polynomial.expand ℤ (d (context z)) (S.polynomial (context z)) from rfl,
    Polynomial.coeff_expand (hpos _)]
  by_cases H : d (context z)∣Nat.fromBitsLE (selectedDegree z)
  · have H0:=Nat.mod_eq_zero_of_dvd H
    simp only [H,H0,ite_true]
  · have H0 : Nat.fromBitsLE (selectedDegree z)%d (context z)≠0:=fun h=>H (Nat.dvd_of_mod_eq_zero h)
    simp only [H,H0,ite_false,Int.cast_zero]

theorem access (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
    {d : List Bool→ℕ} (hd : BinaryFn d) (hpos : ∀ q,0<d q) :
    IntegerPolynomialRootQueriesBits.Access (source S d) where
  coefficient:=coefficient_evaluator S hS hd hpos
  degree:=hS.degree.mul hd
  mass:=hS.mass

end LeanCanny.Algebra.IntegerPolynomialExpandSource
