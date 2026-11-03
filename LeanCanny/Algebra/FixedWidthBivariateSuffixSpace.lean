/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthBivariateReboxSpace
public import LeanCanny.Algebra.FixedWidthSuffixLiftSpace
/-! # Bivariate heads on the literal suffix of one terminal tuple

Each outer coefficient is renamed into the same suffix. Native access
checks all newer exponent blocks before dropping them; it never chooses
another old tuple or evaluates a norm polynomial.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBivariateSuffixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
variable (D A U V : List Bool→ℕ)
variable (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c)) ℤ))

noncomputable def polynomial (c : List Bool) : Polynomial (MvPolynomial (Fin (D c+A c)) ℤ) :=
  (p c).map (MvPolynomial.rename (FixedWidthSuffixLiftBits.shift (D c))).toRingHom

theorem coefficient (c : List Bool) (k : ℕ) :
    (polynomial D A p c).coeff k=
      MvPolynomial.rename (FixedWidthSuffixLiftBits.shift (D c)) ((p c).coeff k) :=
  Polynomial.coeff_map _ _

theorem evaluation (c : List Bool) (z : Fin (D c+A c)→ℝ) :
    (polynomial D A p c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z)=
      (p c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ)
        (fun i=>z (FixedWidthSuffixLiftBits.shift (D c) i))) :=by
  ext k
  simp only [Polynomial.coeff_map,coefficient]
  exact FixedWidthSuffixLiftBits.evaluation _ _

theorem coefficient_degree (c : List Bool) (k : ℕ) :
    ((polynomial D A p c).coeff k).totalDegree≤((p c).coeff k).totalDegree :=by
  rw [coefficient]
  exact MvPolynomial.totalDegree_rename_le _ _

theorem row_evaluator
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A U p))
    (hA : UnaryFn A) (hU : UnaryFn U) (hold : ∀c y,((p c).coeff y).totalDegree<2^U c)
    (hD : UnaryFn D) (hV : UnaryFn V) (y : List Bool→ℕ) (hy : BinaryFn y)
    (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (fun c=>D c+A c) V
      (fun c=>(polynomial D A p c).coeff (y c)) target modulus) :=by
  have ES:=FixedWidthBivariateReboxBits.row_evaluator A U V p R hA hU hold
    id id_mem_FP y hy hV (FixedWidthSuffixLiftBits.spatial D V target) modulus
    (FixedWidthSuffixLiftBits.spatial_FP D V target hD hV ht) hm
  have E:=FixedWidthSuffixLiftBits.evaluator D A V (fun c=>(p c).coeff (y c)) target modulus hD hV ht ES
  exact E.congr (funext fun c=>by simp only [coefficient])

theorem word_evaluator
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A U p))
    (hA : UnaryFn A) (hU : UnaryFn U) (hold : ∀c y,((p c).coeff y).totalDegree<2^U c)
    (hD : UnaryFn D) (hV : UnaryFn V) :
    SpaceFunction (FixedWidthBivariateReboxBits.coefficient (fun c=>D c+A c) V (polynomial D A p)) :=by
  have EO:=FixedWidthBivariateReboxBits.row_evaluator A U (V∘FixedWidthBivariateReader.origin) p R hA hU hold
    FixedWidthBivariateReader.origin FixedWidthBivariateReader.origin_FP FixedWidthBivariateReboxBits.outer
    (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) (hV.comp FixedWidthBivariateReader.origin_FP)
    (FixedWidthSuffixLiftBits.spatial (D∘FixedWidthBivariateReader.origin) (V∘FixedWidthBivariateReader.origin)
      FixedWidthBivariateReboxBits.target) FixedWidthBivariateReboxBits.modulus
    (FixedWidthSuffixLiftBits.spatial_FP _ _ _ (hD.comp FixedWidthBivariateReader.origin_FP)
      (hV.comp FixedWidthBivariateReader.origin_FP) (by polytime [FixedWidthBivariateReboxBits.target]))
    (by polytime [FixedWidthBivariateReboxBits.modulus])
  have E:=FixedWidthSuffixLiftBits.evaluator (D∘FixedWidthBivariateReader.origin) (A∘FixedWidthBivariateReader.origin)
    (V∘FixedWidthBivariateReader.origin)
    (fun z=>(p (FixedWidthBivariateReader.origin z)).coeff (FixedWidthBivariateReboxBits.outer z))
    FixedWidthBivariateReboxBits.target FixedWidthBivariateReboxBits.modulus
    (hD.comp FixedWidthBivariateReader.origin_FP) (hV.comp FixedWidthBivariateReader.origin_FP)
    (by polytime [FixedWidthBivariateReboxBits.target]) EO
  exact E.congr (funext fun c=>by
    simp only [FixedWidthBivariateReboxBits.coefficient,coefficient]
    rfl)

noncomputable def reader
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A U p))
    (hA : UnaryFn A) (hU : UnaryFn U) (hold : ∀c y,((p c).coeff y).totalDegree<2^U c)
    (hD : UnaryFn D) (hV : UnaryFn V) (B : List Bool→ℕ)
    (hdegree : ∀c y,((p c).coeff y).totalDegree≤B c) (hfit : ∀c,B c<2^V c) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (fun c=>D c+A c) V (polynomial D A p)) :=
  FixedWidthBivariateReader.reader _ V (polynomial D A p)
    (FixedWidthBivariateReboxBits.coefficient _ V (polynomial D A p))
    (word_evaluator D A U V p R hA hU hold hD hV) (hD.add hA) hV B
    (fun c y=>(coefficient_degree D A p c y).trans (hdegree c y)) hfit
    (FixedWidthBivariateReboxBits.coefficient_packet _ V (polynomial D A p))

end LeanCanny.Algebra.FixedWidthBivariateSuffixBits
