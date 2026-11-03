/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalOriginalPullSpace
public import LeanCanny.Algebra.FixedWidthFermatHeadSpace
/-! # Physical spatial coefficients over an external native source query -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalOriginalSourceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedPhysicalCriticalBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def modulusWord (F : Family) (I : Indices F) (q : List Bool) := BinaryNatCode.encode (I.modulus q-1)
noncomputable def polynomial (F : Family) (q : List Bool) :=
  FermatCriticalHomogenization.polynomial (F.spatial q).low (F.spatial q).leading (F.spatial q).degree

theorem low_evaluator (F : Family) (I : Indices F) (h : Metadata F I)
    (original : SpaceFunction (IntegralMixedPhysicalOriginalBits.scalar F I))
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>F.ambient q+1) V (fun q=>(F.spatial q).low) target (modulusWord F I)) := by
  let A:=fun q=>F.ambient q+1
  let B:=fun q=>(F.spatial q).degree.size
  have HA : UnaryFn A:=h.ambient.add (UnaryFn.const 1)
  have HB : UnaryFn B:=sourceWidth_unary F I h
  have HP : ∀q e,e∈(F.spatial q).low.support→∀i,e i<2^B q := by
    intro q e he i
    exact ((MvPolynomial.monomial_le_degreeOf i he).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt
      ((F.spatial q).low_degree.trans (Nat.lt_size_self _))
  exact FixedWidthBoxRepackBits.evaluator A B V (fun q=>(F.spatial q).low) HP target (modulusWord F I) HA HB hV ht
    (IntegralMixedFramedPhysicalLowBits.fixed_evaluator_family F I I.modulus_ne_zero original _
      (FixedWidthQuery.repack_mem_FP HA hV HA HB ht))

theorem evaluator (F : Family) (I : Indices F) (h : Metadata F I)
    (original : SpaceFunction (IntegralMixedPhysicalOriginalBits.scalar F I))
    (leading : SpaceFunction (fun q=>residueBits ((F.spatial q).leading : ZMod (I.modulus q))))
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>F.ambient q+1) V (polynomial F) target (modulusWord F I)) := by
  have HL : SpaceFunction (fun q=>residueBits ((F.spatial q).leading : ZMod (Nat.fromBitsLE (modulusWord F I q)+1))) :=by
    apply leading.congr
    funext q
    apply congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) rfl
    simp only [modulusWord,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have HM:=I.modulus_ne_zero q
    omega
  have HA:=h.ambient.add (UnaryFn.const 1)
  have HM : modulusWord F I∈FP:=((h.modulus.sub (BinaryFn.const 1)).bits_mem_FP)
  have EL:=low_evaluator F I h original V hV target ht
  have EH:=FixedWidthFermatHeadBits.evaluator (fun q=>F.ambient q+1) V (fun q=>(F.spatial q).degree)
    (fun q=>(F.spatial q).leading) target (modulusWord F I) _ HA hV h.degree ht HM HL (fun _=>rfl)
  exact (FixedWidthRowBits.add_evaluator (fun q=>F.ambient q+1) V (fun q=>(F.spatial q).low)
    (FixedWidthFermatHeadBits.head (fun q=>F.ambient q+1) (fun q=>(F.spatial q).degree) (fun q=>(F.spatial q).leading))
    target (modulusWord F I) HM EL EH).congr (funext fun _=>rfl)

theorem evaluator_of_modulus (F : Family) (I : Indices F) (h : Metadata F I)
    (original : SpaceFunction (IntegralMixedPhysicalOriginalBits.scalar F I))
    (M : List Bool→ℕ) (hM : ∀q,I.modulus q=M q)
    (leading : SpaceFunction (fun q=>residueBits ((F.spatial q).leading : ZMod (M q))))
    (V : List Bool→ℕ) (hV : UnaryFn V) (target : List Bool→List Bool) (ht : target∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun q=>F.ambient q+1) V (polynomial F) target (modulusWord F I)) := by
  have HL : SpaceFunction (fun q=>residueBits ((F.spatial q).leading : ZMod (I.modulus q))) :=
    leading.congr (funext fun q=>congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) rfl (hM q).symm)
  exact evaluator F I h original HL V hV target ht

end LeanCanny.Algebra.IntegralMixedPhysicalOriginalSourceBits
