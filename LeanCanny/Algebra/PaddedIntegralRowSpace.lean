/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralLowerRowSpace

/-! # Native coefficients of the literal newest-first monic sampler row

The pure new-coordinate power has an FP coefficient reader. Its lower part
uses the actual creating companion with independent coordinate-power and
basis-box checks. Arbitrary caller moduli and exponent widths are retained.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralRowBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial MvPolynomial
open PaddedIntegralGeneratorSource UniformIntegralPowerSchedule MonicParameterRows
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ArithmeticBits.one

def topDegree (S : Source) (cap : List Bool→ℕ) (c : List Bool) := scalarDegree S c*birthPower S cap c

noncomputable def topPolynomial (S : Source) (cap : List Bool→ℕ) (c : List Bool) :
    MvPolynomial (Fin (S.arity c+1)) ℤ := X 0^topDegree S cap c

noncomputable def polynomial (S : Source) (cap : List Bool→ℕ) (c : List Bool) :
    MvPolynomial (Fin (S.arity c+1)) ℤ :=
  rename (headEquiv (S.arity c)) (MonicParameterRows.row (S.equation c) (scalarDegree S c)
    (weights (cap c) (scalarDegree S c) (S.arity c)) (birthPower S cap c))

def topReader (S : Source) (cap V : List Bool→ℕ) (target modulus : List Bool→List Bool) (c : List Bool) :=
  if FixedWidthPowerMonomial.Matches (fun q=>S.arity q+1) V (topDegree S cap) (fun _=>0) target c then
    ArithmeticBits.one (BinaryNatCode.encode (Nat.fromBitsLE (modulus c)+1)) else []

theorem topReader_FP (S : Source) (cap V : List Bool→ℕ) (target modulus : List Bool→List Bool)
    (hc : UnaryFn cap) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) (hV : UnaryFn V)
    (ht : target∈FP) (hm : modulus∈FP) : topReader S cap V target modulus∈FP := by
  have HD := (scalarDegree_binary S hw).mul (birthPower_binary S cap hc ha hw)
  have HG := FixedWidthPowerMonomial.matches_FP (fun q=>S.arity q+1) V (topDegree S cap) (fun _=>0) target
    (ha.add (UnaryFn.const 1)) hV HD (BinaryFn.const 0) ht
  have HM := (BinaryFn.fromBits hm).add (BinaryFn.const 1)
  exact HG.ite_mem_FP (mem_FP_comp HM.bits_mem_FP ArithmeticBits.one_mem_FP) (constFn_mem_FP [])

theorem topReader_value (S : Source) (cap V : List Bool→ℕ) (target modulus : List Bool→List Bool) (c : List Bool) :
    topReader S cap V target modulus c=FixedWidthRowBits.value (fun q=>S.arity q+1) V (topPolynomial S cap) target modulus c := by
  have HE : FixedWidthPowerMonomial.Matches (fun q=>S.arity q+1) V (topDegree S cap) (fun _=>0) target c ↔
      nativeExponent (Equiv.refl (Fin (S.arity c+1))) (V c) (Nat.fromBitsLE (target c)) =
        Finsupp.single (0 : Fin (S.arity c+1)) (topDegree S cap c) := by
    simpa using FixedWidthPowerMonomial.matches_iff (fun q=>S.arity q+1) V (topDegree S cap) (fun _=>0) target c
      (Nat.zero_lt_succ _)
  simp only [topReader,FixedWidthRowBits.value,topPolynomial,X_pow_eq_monomial,coeff_monomial]
  by_cases HG : FixedWidthPowerMonomial.Matches (fun q=>S.arity q+1) V (topDegree S cap) (fun _=>0) target c
  · rw [ite_eq_left HG,ite_eq_left (HE.mp HG).symm,ArithmeticBits.one_residueBits]
    simp only [Int.cast_one]
  · rw [ite_eq_right HG,ite_eq_right (fun H=>HG (HE.mpr H.symm))]
    simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode]
    rfl

theorem polynomial_eq (S : Source) (cap : List Bool→ℕ) (c : List Bool) :
    polynomial S cap c=topPolynomial S cap c+lowerPolynomial S cap c := by
  simp only [polynomial,MonicParameterRows.row,map_add,map_pow,rename_X,headEquiv_new,
    topPolynomial,topDegree,lowerPolynomial]

theorem row_evaluator (S : Source) (cap V : List Bool→ℕ) (target modulus : List Bool→List Bool)
    (hc : UnaryFn cap) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) (hV : UnaryFn V)
    (ht : target∈FP) (hm : modulus∈FP) (E : SpaceFunction (PaddedIntegralGeneratorSource.value S)) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>S.arity q+1) V (polynomial S cap) target modulus) := by
  have HT := (SpaceFunction.ofFP _ (topReader_FP S cap V target modulus hc ha hw hV ht hm)).congr
    (funext (topReader_value S cap V target modulus))
  have HL := lower_evaluator S cap V target modulus hc ha hw hV ht hm E
  have H := FixedWidthRowBits.add_evaluator (fun q=>S.arity q+1) V (topPolynomial S cap) (lowerPolynomial S cap)
    target modulus hm HT HL
  exact H.congr (funext fun c=>by simp only [FixedWidthRowBits.value,polynomial_eq])

end LeanCanny.Algebra.PaddedIntegralRowBits
