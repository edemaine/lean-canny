/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthBivariateZeroLift
public import LeanCanny.Algebra.FixedWidthParameterCons
public import LeanCanny.Algebra.FixedWidthBivariateReboxSpace
/-! # A zero source-parameter request and two dummy-exponent guards

The source context, outer coefficient and caller modulus are unchanged.
Only the exponent word is changed: drop both dummy blocks and prepend a
zero source-parameter block. Either nonzero dummy exponent returns zero.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBivariateZeroLiftBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FixedWidthBivariateReboxBits (target modulus outer)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem zero_row_evaluator (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>A c+1) W p))
    (hA : UnaryFn A) (hW : UnaryFn W) (hfit : ∀c y,((p c).coeff y).totalDegree<2^W c)
    (read : List Bool→List Bool) (hr : read∈FP) (y : List Bool→ℕ) (hy : BinaryFn y)
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (A∘read) (W∘read)
      (fun c=>MvTwoParameterCoefficient.one ((p (read c)).coeff (y c)) 0) target modulus) :=by
  have HP:=FixedWidthParameterConsBits.prepend_FP (W∘read) (fun _=>0) target (hW.comp hr) (BinaryFn.const 0) ht
  have E:=FixedWidthBivariateRowBits.evaluator (fun c=>A c+1) W p R (hA.add (UnaryFn.const 1)) hW hfit
    read hr y hy (FixedWidthParameterConsBits.prepend (W∘read) (fun _=>0) target) modulus HP hm
  refine E.congr (funext fun c=>?_)
  unfold FixedWidthRowBits.value
  simp only [FixedWidthParameterConsBits.prepend,Function.comp_apply]
  rw [FixedWidthParameterConsBits.nativeExponent_prepend (A (read c)) (W (read c)) 0 (target c) (Nat.two_pow_pos _)]
  rw [MvTwoParameterCoefficient.one,MvPolynomial.finSuccEquiv_coeff_coeff]

theorem row_evaluator (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>A c+1) W p))
    (hA : UnaryFn A) (hW : UnaryFn W) (hfit : ∀c y,((p c).coeff y).totalDegree<2^W c)
    (read : List Bool→List Bool) (hr : read∈FP) (y : List Bool→ℕ) (hy : BinaryFn y)
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>A (read c)+2) (W∘read)
      (fun c=>(head A p (read c)).coeff (y c)) target modulus) :=by
  let V:=W∘read
  let tail:=IntegerParameterCoefficientBits.spatial V target
  have HV : UnaryFn V:=hW.comp hr
  have HT : tail∈FP:=IntegerParameterCoefficientBits.spatial_mem_FP V target HV ht
  have Htail:=IntegerParameterCoefficientBits.spatial_mem_FP V tail HV HT
  have E0:=zero_row_evaluator A W p R hA hW hfit read hr y hy
    (IntegerParameterCoefficientBits.spatial V tail) modulus Htail hm
  have E1:=FixedWidthHeadLiftBits.evaluator (A∘read) V
    (fun c=>MvTwoParameterCoefficient.one ((p (read c)).coeff (y c)) 0) tail modulus HV HT E0
  have E2:=FixedWidthHeadLiftBits.evaluator (fun c=>A (read c)+1) V
    (fun c=>MvPolynomial.rename Fin.succ (MvTwoParameterCoefficient.one ((p (read c)).coeff (y c)) 0))
    target modulus HV ht E1
  refine E2.congr (funext fun c=>?_)
  unfold FixedWidthRowBits.value
  simp only [coefficient]
  rfl

noncomputable def coefficientWord (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) :=
  FixedWidthBivariateReboxBits.coefficient (fun c=>A c+2) W (head A p)

theorem coefficient_evaluator (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>A c+1) W p))
    (hA : UnaryFn A) (hW : UnaryFn W) (hfit : ∀c y,((p c).coeff y).totalDegree<2^W c) :
    SpaceFunction (coefficientWord A W p) :=
  row_evaluator A W p R hA hW hfit FixedWidthBivariateReader.origin FixedWidthBivariateReader.origin_FP
    outer (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) target modulus
    (by polytime [target]) (by polytime [modulus])

noncomputable def reader (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>A c+1) W p))
    (hA : UnaryFn A) (hW : UnaryFn W) (D : List Bool→ℕ)
    (hdegree : ∀c y,((p c).coeff y).totalDegree≤D c) (hfit : ∀c,D c<2^W c) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>A c+2) W (head A p)) :=
  FixedWidthBivariateReader.reader _ _ _ (coefficientWord A W p)
    (coefficient_evaluator A W p R hA hW (fun c y=>(hdegree c y).trans_lt (hfit c)))
    (hA.add (UnaryFn.const 2)) hW D (fun c y=>(degree A p c y).trans (hdegree c y)) hfit
    (FixedWidthBivariateReboxBits.coefficient_packet _ _ _)

theorem epsilon_row_evaluator (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>A c+1) W p))
    (hA : UnaryFn A) (hW : UnaryFn W) (hfit : ∀c y,((p c).coeff y).totalDegree<2^W c)
    (read : List Bool→List Bool) (hr : read∈FP) (y : List Bool→ℕ) (hy : BinaryFn y)
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>A (read c)+2) (W∘read)
      (fun c=>(epsilonHead A p (read c)).coeff (y c)) target modulus) :=by
  have HT:=IntegerParameterCoefficientBits.spatial_mem_FP (W∘read) target (hW.comp hr) ht
  have E0:=FixedWidthBivariateRowBits.evaluator (fun c=>A c+1) W p R (hA.add (UnaryFn.const 1)) hW hfit
    read hr y hy (IntegerParameterCoefficientBits.spatial (W∘read) target) modulus HT hm
  have E1:=FixedWidthHeadLiftBits.evaluator (fun c=>A (read c)+1) (W∘read)
    (fun c=>(p (read c)).coeff (y c)) target modulus (hW.comp hr) ht E0
  refine E1.congr (funext fun c=>?_)
  unfold FixedWidthRowBits.value
  simp only [epsilon_coefficient]

noncomputable def epsilonReader (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>A c+1) W p))
    (hA : UnaryFn A) (hW : UnaryFn W) (D : List Bool→ℕ)
    (hdegree : ∀c y,((p c).coeff y).totalDegree≤D c) (hfit : ∀c,D c<2^W c) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>A c+2) W (epsilonHead A p)) :=
  FixedWidthBivariateReader.reader _ _ _ (FixedWidthBivariateReboxBits.coefficient (fun c=>A c+2) W (epsilonHead A p))
    (epsilon_row_evaluator A W p R hA hW (fun c y=>(hdegree c y).trans_lt (hfit c))
      FixedWidthBivariateReader.origin FixedWidthBivariateReader.origin_FP outer
      (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) target modulus (by polytime [target]) (by polytime [modulus]))
    (hA.add (UnaryFn.const 2)) hW D (fun c y=>(epsilon_degree A p c y).trans (hdegree c y)) hfit
    (FixedWidthBivariateReboxBits.coefficient_packet _ _ _)

end LeanCanny.Algebra.FixedWidthBivariateZeroLiftBits
