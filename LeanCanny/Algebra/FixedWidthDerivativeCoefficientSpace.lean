/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthBinaryDerivativeSpace
public import LeanCanny.Algebra.FixedWidthPowerMonomial
public import LeanCanny.Algebra.FixedWidthRowArithmetic
/-! # Binary-degree derivatives of a native coefficient packet family

The source coefficient query is an external packet. Its exact exponent word
need not fit in a flat arithmetic task field.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem coefficient_evaluator (A W V D selected : List Bool→ℕ) (target modulus coefficient : List Bool→List Bool)
    (p : (q : List Bool)→MvPolynomial (Fin (A q)) ℤ)
    (hs : ∀q,selected q<A q) (hpos : ∀q,0<D q) (hp : ∀q,(p q).totalDegree≤D q)
    (hw : ∀q,D q<2^W q)
    (hA : UnaryFn A) (hW : UnaryFn W) (hV : UnaryFn V) (hD : BinaryFn D)
    (hselected : UnaryFn selected) (ht : target∈FP) (hm : modulus∈FP) (E : SpaceFunction coefficient)
    (he : ∀q r,coefficient (pair q (BinaryNatCode.encode r))=
      residueBits ((p q).coeff (nativeExponent (Equiv.refl _) (W q) r) : ZMod (Nat.fromBitsLE (modulus q)+1))) :
    SpaceFunction (FixedWidthRowBits.value A V (fun q=>MvPolynomial.pderiv ⟨selected q,hs q⟩ (p q)) target modulus) := by
  have HM:=FlatAffineIntegerSpace.modulusCode_FP modulus hm
  have HE:=evaluator_binary A W V D selected target (FlatAffineIntegerSpace.modulusCode modulus) E
    hA hW hV hD hselected ht HM
  apply HE.congr
  funext q
  have HP:=packet A W V D selected target (FlatAffineIntegerSpace.modulusCode modulus)
    (Equiv.refl (Fin (A q))) coefficient q (p q) ⟨selected q,hs q⟩ (Nat.fromBitsLE (modulus q)+1)
    rfl rfl (hpos q) (hp q) (hw q) (FlatAffineIntegerSpace.modulusCode_eq modulus q) (he q)
  have HX : exponent V target (Equiv.refl (Fin (A q))) q=
      nativeExponent (Equiv.refl (Fin (A q))) (V q) (Nat.fromBitsLE (target q)) := by
    ext i
    simp only [exponent,Finsupp.coe_equivFunOnFinite_symm,Equiv.refl_apply]
    exact (FixedWidthPowerMonomial.native_coordinate A V target q i).symm
  exact HP.trans (congrArg (fun e=>residueBits
    ((MvPolynomial.pderiv (⟨selected q,hs q⟩ : Fin (A q)) (p q)).coeff e : ZMod (Nat.fromBitsLE (modulus q)+1))) HX)

end LeanCanny.Algebra.FixedWidthDerivativeBits
