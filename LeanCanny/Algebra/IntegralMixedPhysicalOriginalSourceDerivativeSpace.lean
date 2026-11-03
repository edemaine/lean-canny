/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalOriginalSourceSpace
public import LeanCanny.Algebra.IntegralMixedPhysicalOriginalDerivativeSpace
public import LeanCanny.Algebra.FixedWidthMonomialSpace
/-! # Exact physical source derivatives over a native query family -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalOriginalSourceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial MvPolynomial
open IntegralMixedPhysicalCriticalBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem derivative_evaluator (F : Family) (I : Indices F) (h : Metadata F I)
    (original : SpaceFunction (IntegralMixedPhysicalOriginalBits.scalar F I))
    (leading : SpaceFunction (fun q=>residueBits ((F.spatial q).leading : ZMod (I.modulus q))))
    (selected : List Bool→ℕ) (hs : ∀q,selected q<F.ambient q+1) (hselected : UnaryFn selected)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>F.ambient q+1) V
      (fun q=>pderiv ⟨selected q,hs q⟩ (polynomial F q)) target (modulusWord F I)) := by
  let A:=fun q=>F.ambient q+1
  let aD:=fun q=>(F.spatial q).leading*((F.spatial q).degree : ℤ)
  have HA : UnaryFn A:=h.ambient.add (UnaryFn.const 1)
  have HM : modulusWord F I∈FP:=(h.modulus.sub (BinaryFn.const 1)).bits_mem_FP
  have HL : SpaceFunction (fun q=>residueBits ((F.spatial q).leading : ZMod (Nat.fromBitsLE (modulusWord F I q)+1))) := by
    apply leading.congr
    funext q
    apply congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) rfl
    simp only [modulusWord,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have H:=I.modulus_ne_zero q
    omega
  have EA : SpaceFunction (fun q=>residueBits (aD q : ZMod (Nat.fromBitsLE (modulusWord F I q)+1))) :=
    FixedWidthFermatHeadBits.natMultiply_evaluator (modulusWord F I) _ (fun q=>(F.spatial q).leading)
      (fun q=>(F.spatial q).degree) HM h.degree HL (fun _=>rfl)
  have EH:=FixedWidthMonomialBits.coefficient_evaluator A V selected (fun q=>(F.spatial q).degree-1) target aD
    (modulusWord F I) _ EA (fun _=>rfl) HA hV (BinaryFn.ofUnary hselected) (h.degree.sub (BinaryFn.const 1)) ht
  have EL:=IntegralMixedPhysicalOriginalBits.derivative_evaluator F I h original selected hs hselected V hV target ht
  have EE:=FixedWidthRowBits.add_evaluator A V (IntegralMixedPhysicalOriginalBits.derivative F selected hs)
    (FixedWidthMonomialBits.polynomial A selected (fun q=>(F.spatial q).degree-1) aD) target (modulusWord F I) HM EL EH
  apply EE.congr
  funext q
  let p0 : MvPolynomial (Fin (A q)) ℤ:=IntegralMixedPhysicalOriginalBits.derivative F selected hs q
  let p1 : MvPolynomial (Fin (A q)) ℤ:=FixedWidthMonomialBits.polynomial A selected (fun q=>(F.spatial q).degree-1) aD q
  have HP : p0+p1=pderiv ⟨selected q,hs q⟩ (polynomial F q) := by
    dsimp only [p0,p1,FixedWidthMonomialBits.polynomial,IntegralMixedPhysicalOriginalBits.derivative,polynomial]
    rw [dite_eq_left (hs q),FermatCriticalHomogenization.pderiv_polynomial,MvPolynomial.C_mul_X_pow_eq_monomial]
  exact congrArg (fun p : MvPolynomial (Fin (A q)) ℤ=>residueBits
    (p.coeff (nativeExponent (Equiv.refl _) (V q) (Nat.fromBitsLE (target q))) : ZMod (Nat.fromBitsLE (modulusWord F I q)+1))) HP

theorem derivative_evaluator_of_modulus (F : Family) (I : Indices F) (h : Metadata F I)
    (original : SpaceFunction (IntegralMixedPhysicalOriginalBits.scalar F I))
    (M : List Bool→ℕ) (hM : ∀q,I.modulus q=M q)
    (leading : SpaceFunction (fun q=>residueBits ((F.spatial q).leading : ZMod (M q))))
    (selected : List Bool→ℕ) (hs : ∀q,selected q<F.ambient q+1) (hselected : UnaryFn selected)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>F.ambient q+1) V
      (fun q=>pderiv ⟨selected q,hs q⟩ (polynomial F q)) target (modulusWord F I)) := by
  have HL : SpaceFunction (fun q=>residueBits ((F.spatial q).leading : ZMod (I.modulus q))) :=
    leading.congr (funext fun q=>congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) rfl (hM q).symm)
  exact derivative_evaluator F I h original HL selected hs hselected V hV target ht

end LeanCanny.Algebra.IntegralMixedPhysicalOriginalSourceBits
