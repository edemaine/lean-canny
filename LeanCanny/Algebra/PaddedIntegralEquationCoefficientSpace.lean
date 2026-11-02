/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralEquationMatrixNative

/-! # Native powered coefficients of literal scalar equations

Arbitrary exponent widths are divided by the fixed positive scalar powers.
The existing basis-box guard rejects excessive old exponents. Each accepted
query reads one actual creating-companion entry, with its full space charge.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralEquationMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCoordinateBasis FixedWidthPolynomial PaddedIntegralGeneratorSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCoordinateCoefficientBits.Family.matrix Source.matrix

theorem entry_packet (S : Source) (c mw : List Bool)
    (r t : Fin (count (S.arity (pairFst c)) (S.width (pairFst c)))) :
    entry S (pair (pair c mw) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) =
      residueBits (((family S).matrix c r t : ℤ) : ZMod (Nat.fromBitsLE mw+1)) := by
  generalize hz : pair (pair c mw) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))=q
  have HC : PaddedIntegralGeneratorSource.base q=c := by
    rw [PaddedIntegralGeneratorSource.base,←hz,pairFst_pair,pairFst_pair]
  have HM : modulus q=mw := by rw [modulus,←hz,pairFst_pair,pairSnd_pair]
  have HR : (oldIndex S row q).val=r.val := by
    rw [←hz]
    simp only [oldIndex,rank,row,PaddedIntegralGeneratorSource.base,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits,Nat.mod_eq_of_lt r.isLt]
  have HT : (oldIndex S col q).val=t.val := by
    rw [←hz]
    simp only [oldIndex,rank,col,PaddedIntegralGeneratorSource.base,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits,Nat.mod_eq_of_lt t.isLt]
  subst c
  subst mw
  have HI : oldIndex S row q=r := Fin.ext HR
  have HJ : oldIndex S col q=t := Fin.ext HT
  simp only [entry,HI,HJ]

theorem powered_evaluator (S : Source) (cap V : List Bool → ℕ)
    (target modulus : List Bool → List Bool)
    (hcap : UnaryFn cap) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) (hV : UnaryFn V)
    (ht : target∈FP) (hm : modulus∈FP)
    (E : SpaceFunction (PaddedIntegralGeneratorSource.value S)) :
    SpaceFunction (FixedWidthRowBits.value (family S).arity V ((family S).poweredPolynomial cap) target modulus) :=
  IntegralCoordinateCoefficientBits.powered_evaluator (family S) cap V target modulus (entry S)
    hcap (ha.comp pairFst_mem_FP) (hw.comp pairFst_mem_FP) hV ht hm
    (evaluator S ha hw E) (entry_packet S)

theorem powered_polynomial_eq (S : Source) (cap : List Bool → ℕ) (c : List Bool) :
    (family S).poweredPolynomial cap c =
      CoordinatePowerSubstitution.substitute
        (UniformIntegralPowerSchedule.weights (cap c) (2^S.width (pairFst c)) (S.arity (pairFst c)))
        ((S.equation (pairFst c)).coeff (power S c).val) := by
  rw [IntegralCoordinateCoefficientBits.Family.poweredPolynomial,polynomial_eq]
  rfl

end LeanCanny.Algebra.PaddedIntegralEquationMatrixBits
