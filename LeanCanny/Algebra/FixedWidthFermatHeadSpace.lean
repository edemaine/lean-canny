/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthPowerMonomial
public import LeanCanny.Algebra.FixedWidthMonomialSpace
public import LeanCanny.Algebra.ModularNatMulFP
/-! # Compact pure-power heads from one original integer residue -/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthFermatHeadBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial MvPolynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

 def multiply (modulus factor : List Bool→List Bool) (z : List Bool) :=
  BinaryNat.mulMod (pair (FlatAffineIntegerSpace.modulusCode modulus (pairFst z))
    (pair (pairSnd z) (factor (pairFst z))))

attribute [local irreducible] BinaryNat.mulMod FlatAffineIntegerSpace.modulusCode

theorem multiply_FP (modulus factor : List Bool→List Bool) (hm : modulus∈FP) (hf : factor∈FP) :
    multiply modulus factor∈FP := by
  have HM : (fun z=>FlatAffineIntegerSpace.modulusCode modulus (pairFst z))∈FP :=
    mem_FP_comp (f:=pairFst) (g:=FlatAffineIntegerSpace.modulusCode modulus) pairFst_mem_FP (FlatAffineIntegerSpace.modulusCode_FP modulus hm)
  have HF : (fun z=>factor (pairFst z))∈FP := mem_FP_comp pairFst_mem_FP hf
  have HE:=mem_FP_comp (mem_FP_pair HM (mem_FP_pair pairSnd_mem_FP HF)) BinaryNat.mulMod_mem_FP
  exact mem_FP_of_eq HE (fun _=>rfl)

theorem multiply_packet (modulus : List Bool→List Bool) (c : List Bool)
    (z : ℤ) (k : ℕ) : multiply modulus (fun _=>BinaryNatCode.encode k)
      (pair c (residueBits (z : ZMod (Nat.fromBitsLE (modulus c)+1))))=
      residueBits ((z*(k : ℤ) : ℤ) : ZMod (Nat.fromBitsLE (modulus c)+1)) := by
  unfold multiply
  simp only [pairFst_pair,pairSnd_pair]
  rw [FlatAffineIntegerSpace.modulusCode_eq,ArithmeticBits.mulMod_nat_residueBits]
  simp only [Int.cast_mul,Int.cast_natCast]

theorem natMultiply_evaluator (modulus reader : List Bool→List Bool) (a : List Bool→ℤ)
    (k : List Bool→ℕ) (hm : modulus∈FP) (hk : BinaryFn k) (E : SpaceFunction reader)
    (hr : ∀q,reader q=residueBits (a q : ZMod (Nat.fromBitsLE (modulus q)+1))) :
    SpaceFunction (fun q=>residueBits ((a q*(k q : ℤ) : ℤ) : ZMod (Nat.fromBitsLE (modulus q)+1))) := by
  have HE:=E.withInput.postcompose (multiply modulus (fun q=>BinaryNatCode.encode (k q)))
    (multiply_FP modulus _ hm hk.bits_mem_FP)
  apply HE.congr
  funext q
  change multiply modulus _ (pair q (reader q))=_
  unfold multiply
  simp only [pairFst_pair,pairSnd_pair]
  rw [hr,FlatAffineIntegerSpace.modulusCode_eq,ArithmeticBits.mulMod_nat_residueBits]
  simp only [Int.cast_mul,Int.cast_natCast]

noncomputable def head (A D : List Bool→ℕ) (a : List Bool→ℤ) (q : List Bool) :
    MvPolynomial (Fin (A q)) ℤ := C (a q)*∑i : Fin (A q),X i^(D q)

theorem coefficient (A W D : List Bool→ℕ) (a : List Bool→ℤ) (target : List Bool→List Bool) (q : List Bool) :
    (head A D a q).coeff (nativeExponent (Equiv.refl _) (W q) (Nat.fromBitsLE (target q)))=
      a q*(FixedWidthPowerMonomial.multiplicity A W D target q : ℤ) := by
  rw [head,MvPolynomial.coeff_C_mul,MvPolynomial.coeff_sum,FixedWidthPowerMonomial.multiplicity_eq]
  congr 1
  simp only [MvPolynomial.coeff_X_pow,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

attribute [local irreducible] multiply head

theorem evaluator (A W D : List Bool→ℕ) (a : List Bool→ℤ) (target modulus reader : List Bool→List Bool)
    (hA : UnaryFn A) (hW : UnaryFn W) (hD : BinaryFn D) (ht : target∈FP) (hm : modulus∈FP)
    (E : SpaceFunction reader)
    (hr : ∀q,reader q=residueBits (a q : ZMod (Nat.fromBitsLE (modulus q)+1))) :
    SpaceFunction (FixedWidthRowBits.value A W (head A D a) target modulus) := by
  have HF:=FixedWidthPowerMonomial.multiplicity_binary A W D target hA hW hD ht
  have HE:=E.withInput.postcompose (multiply modulus (fun q=>BinaryNatCode.encode
    (FixedWidthPowerMonomial.multiplicity A W D target q))) (multiply_FP modulus _ hm HF.bits_mem_FP)
  apply HE.congr
  funext q
  change multiply modulus _ (pair q (reader q))=_
  rw [hr]
  unfold multiply
  simp only [pairFst_pair,pairSnd_pair]
  rw [FlatAffineIntegerSpace.modulusCode_eq,ArithmeticBits.mulMod_nat_residueBits]
  unfold FixedWidthRowBits.value
  rw [coefficient]
  simp only [Int.cast_mul,Int.cast_natCast]

end LeanCanny.Algebra.FixedWidthFermatHeadBits
