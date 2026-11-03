/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthBivariateParameterPairSpace
public import LeanCanny.Algebra.MvTwoParameterEvaluation
/-! # Literal semantics of the common delta/epsilon/raw-variable layout -/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBivariateParameterPairBits
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem arity_eq (m : ℕ) : 1+(m+1)=m+2 :=by omega

private theorem embedding_zero (keep : Bool) (m : ℕ) :
    Fin.cast (arity_eq m) (embedding keep m 0)=if keep then 0 else (0 : Fin (m+1)).succ :=by
  cases keep
  · apply Fin.ext
    rfl
  · change Fin.cast (arity_eq m) (FixedWidthParameterSuffixBits.shift 1 (0 : Fin (m+1)))=0
    rw [FixedWidthParameterSuffixBits.shift_zero]
    rfl

private theorem embedding_succ (keep : Bool) (m : ℕ) (i : Fin m) :
    Fin.cast (arity_eq m) (embedding keep m i.succ)=i.succ.succ :=by
  cases keep
  · apply Fin.ext
    change 1+(i.val+1)=i.val+1+1
    omega
  · change Fin.cast (arity_eq m) (FixedWidthParameterSuffixBits.shift 1 i.succ)=i.succ.succ
    rw [FixedWidthParameterSuffixBits.shift_succ]
    apply Fin.ext
    change 1+(i.val+1)=i.val+1+1
    omega

noncomputable def common (keep : Bool) (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) :
    Polynomial (MvPolynomial (Fin (A c+2)) ℤ) :=
  (lift keep A p c).map (MvPolynomial.rename (Fin.cast (arity_eq (A c)))).toRingHom

theorem pointwise (keep : Bool) (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (c : List Bool) (z : Fin (A c)→ℝ) (ε δ : ℝ) :
    (common keep A p c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons δ (Fin.cons ε z)))=
      (p c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons (if keep then δ else ε) z)) :=by
  have HT : (fun i : Fin (A c+1)=>(Fin.cons δ (Fin.cons ε z) : Fin (A c+2)→ℝ) (Fin.cast (arity_eq (A c)) (embedding keep (A c) i)))=
      (Fin.cons (if keep then δ else ε) z : Fin (A c+1)→ℝ) :=by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · rw [embedding_zero]
      cases keep <;> rfl
    · rw [embedding_succ]
      rfl
  apply Polynomial.ext
  intro y
  simp only [common,lift,Polynomial.coeff_map,MvPolynomial.coe_eval₂Hom]
  change (MvPolynomial.rename (Fin.cast (arity_eq (A c)))
    (MvPolynomial.rename (embedding keep (A c)) ((p c).coeff y))).eval₂
      (Int.castRingHom ℝ) (Fin.cons δ (Fin.cons ε z))=_
  rw [MvPolynomial.eval₂_rename,MvPolynomial.eval₂_rename]
  exact congrArg (fun point=>MvPolynomial.eval₂ (Int.castRingHom ℝ) point ((p c).coeff y)) HT

theorem evaluated (keep : Bool) (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (c : List Bool) (z : Fin (A c)→ℝ) (ε δ : ℝ) :
    ((common keep A p c).map (MvTwoParameterCoefficient.evaluate (Int.castRingHom ℝ) z)).map
      (RealIteratedTarski.evaluate ε δ)=
        (p c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons (if keep then δ else ε) z)) :=by
  apply Polynomial.ext
  intro y
  simp only [Polynomial.coeff_map]
  rw [MvTwoParameterCoefficient.point_evaluate]
  have H:=congrArg (fun q : ℝ[X]=>q.coeff y) (pointwise keep A p c z ε δ)
  simpa only [Polynomial.coeff_map,MvPolynomial.coe_eval₂Hom] using H

end LeanCanny.Algebra.FixedWidthBivariateParameterPairBits
