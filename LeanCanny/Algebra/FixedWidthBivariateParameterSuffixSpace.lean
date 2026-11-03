/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthParameterSuffixSpace
public import LeanCanny.Algebra.FixedWidthBivariateRowSpace
/-! # A charged creating-head reader supplies its literal terminal-suffix coefficients -/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBivariateParameterSuffixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

noncomputable def head (D A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) :
    Polynomial (MvPolynomial (Fin (D c+(A c+1))) ℤ) :=
  (p c).map (MvPolynomial.rename (FixedWidthParameterSuffixBits.shift (D c))).toRingHom

theorem coefficient (D A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    (head D A p c).coeff y=MvPolynomial.rename (FixedWidthParameterSuffixBits.shift (D c)) ((p c).coeff y) :=
  Polynomial.coeff_map _ _

theorem evaluator (A W : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>A c+1) W p))
    (hA : UnaryFn A) (hW : UnaryFn W) (hfit : ∀ c y,((p c).coeff y).totalDegree<2^W c)
    (read : List Bool→List Bool) (hr : read∈FP) (D y : List Bool→ℕ) (hD : UnaryFn D) (hy : BinaryFn y)
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>D c+(A (read c)+1)) (W ∘ read)
      (fun c=>MvPolynomial.rename (FixedWidthParameterSuffixBits.shift (D c)) ((p (read c)).coeff (y c)))
      target modulus) :=by
  have hAR:=hA.comp hr
  have hWR:=hW.comp hr
  have HW:=FixedWidthParameterSuffixBits.word_FP D (A ∘ read) (W ∘ read) target hD hAR hWR ht
  have HQ:=FixedWidthSuffixLiftBits.spatial_FP D (W ∘ read)
    (FixedWidthParameterSuffixBits.word D (A ∘ read) (W ∘ read) target) hD hWR HW
  have E:=FixedWidthBivariateRowBits.evaluator (fun c=>A c+1) W p R (hA.add (UnaryFn.const 1)) hW hfit
    read hr y hy _ modulus HQ hm
  exact FixedWidthParameterSuffixBits.evaluator D (A ∘ read) (W ∘ read) (fun c=>(p (read c)).coeff (y c))
    target modulus hD hAR hWR ht E

theorem degree (D A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    ((head D A p c).coeff y).totalDegree≤((p c).coeff y).totalDegree :=by
  rw [coefficient]
  exact MvPolynomial.totalDegree_rename_le _ _

theorem mass (D A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    MvMass.mass ((head D A p c).coeff y)≤MvMass.mass ((p c).coeff y) :=by
  rw [coefficient]
  exact MvMass.rename_le _ _

end LeanCanny.Algebra.FixedWidthBivariateParameterSuffixBits
