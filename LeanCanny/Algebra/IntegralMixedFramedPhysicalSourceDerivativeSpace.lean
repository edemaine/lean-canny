/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalSourcePolynomialSpace
public import LeanCanny.Algebra.IntegralMixedPhysicalOriginalDerivativeSpace
/-! # Literal physical source derivatives with binary degree

One actual original LOW coefficient and the original leading residue suffice.
All degree multiplication and sparse Fermat corrections stay native.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalSourceDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask FixedWidthPolynomial MvPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalLowBits (arity width low family indices modulusWord)
open IntegralMixedFramedPhysicalSourcePolynomialBits (leading degree polynomial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalBits.family

 theorem low_task_evaluator (P : Parameters) (F : IntegralMixedPhysicalCriticalBits.Family)
    (h : IntegralMixedPhysicalCriticalBits.Metadata (IntegralMixedPhysicalTaskBits.family P F) (IntegralMixedPhysicalTaskBits.indices P F))
    (original : SpaceFunction (IntegralMixedPhysicalNativeLowerBits.originalScalar P F))
    (selected : List Bool→ℕ) (hs : ∀q,selected q<(IntegralMixedPhysicalTaskBits.family P F).ambient q+1)
    (hselected : UnaryFn selected) (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>(IntegralMixedPhysicalTaskBits.family P F).ambient q+1) V
      (IntegralMixedPhysicalOriginalBits.derivative (IntegralMixedPhysicalTaskBits.family P F) selected hs) target (modulusWord P)) := by
  unfold IntegralMixedPhysicalNativeLowerBits.originalScalar at original
  have HE:=IntegralMixedPhysicalOriginalBits.derivative_evaluator (IntegralMixedPhysicalTaskBits.family P F)
    (IntegralMixedPhysicalTaskBits.indices P F) h original selected hs hselected V hV target ht
  have HM : (fun q=>BinaryNatCode.encode ((IntegralMixedPhysicalTaskBits.indices P F).modulus q-1))=modulusWord P := rfl
  rw [HM] at HE
  exact HE

theorem low_evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (selected : List Bool→ℕ) (hs : ∀q,selected q<arity P D J q) (hselected : UnaryFn selected)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (arity P D J) V
      (IntegralMixedPhysicalOriginalBits.derivative (family P D J) selected hs) target (modulusWord P)) :=
  low_task_evaluator P (IntegralMixedFramedPhysicalBits.family P D J)
    (IntegralMixedFramedPhysicalLowBits.metadata P a D J c) c.critical.physicalOriginal selected hs hselected V hV target ht

noncomputable def derivative (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (selected : List Bool→ℕ) (hs : ∀q,selected q<arity P D J q) (q : List Bool) :=
  MvPolynomial.pderiv ⟨selected q,hs q⟩ (polynomial P D J q)

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (selected : List Bool→ℕ) (hs : ∀q,selected q<arity P D J q) (hselected : UnaryFn selected)
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (arity P D J) V (derivative P D J selected hs) target (modulusWord P)) := by
  have HM:=IntegralMixedFramedPhysicalLowBits.metadata P a D J c
  have HA : UnaryFn (arity P D J):=HM.ambient.add (UnaryFn.const 1)
  have HMod:=IntegralMixedFramedPhysicalLowBits.modulusWord_FP P a
  let aD:=fun q=>leading P D J q*(degree P D J q : ℤ)
  have EA : SpaceFunction (fun q=>residueBits (aD q : ZMod (Nat.fromBitsLE (modulusWord P q)+1))) :=
    FixedWidthFermatHeadBits.natMultiply_evaluator (modulusWord P) _ (leading P D J) (degree P D J) HMod HM.degree
      (IntegralMixedFramedPhysicalSourcePolynomialBits.leading_space P D J c) (fun _=>rfl)
  have EH:=FixedWidthMonomialBits.coefficient_evaluator (arity P D J) V selected (fun q=>degree P D J q-1) target
    aD (modulusWord P) _ EA (fun _=>rfl) HA hV (BinaryFn.ofUnary hselected) (HM.degree.sub (BinaryFn.const 1)) ht
  have EL:=low_evaluator P a D J c selected hs hselected V hV target ht
  have EE:=FixedWidthRowBits.add_evaluator (arity P D J) V
    (IntegralMixedPhysicalOriginalBits.derivative (family P D J) selected hs)
    (FixedWidthMonomialBits.polynomial (arity P D J) selected (fun q=>degree P D J q-1) aD) target (modulusWord P) HMod EL EH
  apply EE.congr
  funext q
  let p0 : MvPolynomial (Fin (arity P D J q)) ℤ:=IntegralMixedPhysicalOriginalBits.derivative (family P D J) selected hs q
  let p1 : MvPolynomial (Fin (arity P D J q)) ℤ:=FixedWidthMonomialBits.polynomial (arity P D J) selected (fun q=>degree P D J q-1) aD q
  have HP : p0+p1=
      derivative P D J selected hs q := by
    dsimp only [p0,p1,FixedWidthMonomialBits.polynomial,IntegralMixedPhysicalOriginalBits.derivative,derivative,polynomial]
    rw [dite_eq_left (hs q),FermatCriticalHomogenization.pderiv_polynomial,MvPolynomial.C_mul_X_pow_eq_monomial]
    rfl
  exact congrArg (fun p : MvPolynomial (Fin (arity P D J q)) ℤ=>residueBits
    (p.coeff (nativeExponent (Equiv.refl _) (V q) (Nat.fromBitsLE (target q))) : ZMod (Nat.fromBitsLE (modulusWord P q)+1))) HP

end LeanCanny.Algebra.IntegralMixedFramedPhysicalSourceDerivativeBits
