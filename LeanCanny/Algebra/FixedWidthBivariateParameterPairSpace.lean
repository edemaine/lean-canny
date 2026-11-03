/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthBivariateParameterSuffixSpace
public import LeanCanny.Algebra.FixedWidthBivariateReboxSpace
/-! # Two independent infinitesimal axes share one literal raw tuple

The head keeps delta at zero and gains unused epsilon at one. The window
keeps epsilon at one and gains unused delta at zero. Both certified readers
use the same coefficient width after native reboxing.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBivariateParameterPairBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FixedWidthBivariateReboxBits (target modulus outer)
open scoped Classical

noncomputable def embedding (keepHead : Bool) (a : ℕ) : Fin (a+1)→Fin (1+(a+1)) :=
  if keepHead then FixedWidthParameterSuffixBits.shift 1 else FixedWidthSuffixLiftBits.shift 1

noncomputable def lift (keepHead : Bool) (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) :
    Polynomial (MvPolynomial (Fin (1+(A c+1))) ℤ) :=
  (p c).map (MvPolynomial.rename (embedding keepHead (A c))).toRingHom

theorem coefficient (keepHead : Bool) (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    (lift keepHead A p c).coeff y=MvPolynomial.rename (embedding keepHead (A c)) ((p c).coeff y) :=
  Polynomial.coeff_map _ _

theorem degree (keepHead : Bool) (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    ((lift keepHead A p c).coeff y).totalDegree≤((p c).coeff y).totalDegree :=by
  rw [coefficient]
  exact MvPolynomial.totalDegree_rename_le _ _

theorem mass (keepHead : Bool) (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    MvMass.mass ((lift keepHead A p c).coeff y)≤MvMass.mass ((p c).coeff y) :=by
  rw [coefficient]
  exact MvMass.rename_le _ _

noncomputable def coefficientWord (keepHead : Bool) (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) :=
  FixedWidthBivariateReboxBits.coefficient (fun c=>1+(A c+1)) W (lift keepHead A p)

theorem coefficient_evaluator (keepHead : Bool) (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>A c+1) W p))
    (hA : UnaryFn A) (hW : UnaryFn W) (hfit : ∀ c y,((p c).coeff y).totalDegree<2^W c) :
    SpaceFunction (coefficientWord keepHead A W p) :=by
  have HO:=FixedWidthBivariateReader.origin_FP
  have HY : BinaryFn outer:=BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have HT : target∈FP:=by polytime [target]
  have HM : modulus∈FP:=by polytime [modulus]
  cases keepHead with
  | true =>
    have E:=FixedWidthBivariateParameterSuffixBits.evaluator A W p R hA hW hfit
      FixedWidthBivariateReader.origin HO (fun _=>1) outer (UnaryFn.const 1) HY target modulus HT HM
    refine E.congr (funext fun z=>?_)
    simp only [coefficientWord,FixedWidthBivariateReboxBits.coefficient,FixedWidthRowBits.value,
      coefficient,embedding,ite_true]
    rfl
  | false =>
    have HS:=FixedWidthSuffixLiftBits.spatial_FP (fun _=>1) (W ∘ FixedWidthBivariateReader.origin) target
      (UnaryFn.const 1) (hW.comp HO) HT
    have EO:=FixedWidthBivariateRowBits.evaluator (fun c=>A c+1) W p R (hA.add (UnaryFn.const 1)) hW hfit
      FixedWidthBivariateReader.origin HO outer HY _ modulus HS HM
    have E:=FixedWidthSuffixLiftBits.evaluator (fun _=>1) (fun z=>A (FixedWidthBivariateReader.origin z)+1)
      (W ∘ FixedWidthBivariateReader.origin) (fun z=>(p (FixedWidthBivariateReader.origin z)).coeff (outer z))
      target modulus (UnaryFn.const 1) (hW.comp HO) HT EO
    refine E.congr (funext fun z=>?_)
    simp only [coefficientWord,FixedWidthBivariateReboxBits.coefficient,FixedWidthRowBits.value,
      coefficient,embedding,Bool.false_eq_true,ite_false]
    rfl

noncomputable def reader (keepHead : Bool) (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>A c+1) W p))
    (hA : UnaryFn A) (hW : UnaryFn W) (D : List Bool→ℕ)
    (hdegree : ∀ c y,((p c).coeff y).totalDegree≤D c) (hfit : ∀ c,D c<2^W c) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>1+(A c+1)) W (lift keepHead A p)) :=
  FixedWidthBivariateReader.reader _ _ _ (coefficientWord keepHead A W p)
    (coefficient_evaluator keepHead A W p R hA hW (fun c y=>(hdegree c y).trans_lt (hfit c)))
    ((UnaryFn.const 1).add (hA.add (UnaryFn.const 1))) hW D
    (fun c y=>(degree keepHead A p c y).trans (hdegree c y)) hfit
    (FixedWidthBivariateReboxBits.coefficient_packet _ _ _)

end LeanCanny.Algebra.FixedWidthBivariateParameterPairBits
