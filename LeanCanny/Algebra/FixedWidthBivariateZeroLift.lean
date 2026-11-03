/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MvTwoParameterCoefficient
public import LeanCanny.Algebra.FixedWidthHeadLiftSpace
/-! # Zero specialization followed by two genuinely unused parameter axes

All old raw variables remain. The old first parameter is evaluated at zero;
two new dummy variables are added before the same raw tuple.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBivariateZeroLiftBits
open LeanCanny.Encoding LeanCanny.Computation Polynomial MvPolynomial
open scoped Classical

noncomputable def zeroHom (n : ℕ) : MvPolynomial (Fin (n+1)) ℤ→+*MvPolynomial (Fin n) ℤ :=
  (Polynomial.constantCoeff : Polynomial (MvPolynomial (Fin n) ℤ)→+*MvPolynomial (Fin n) ℤ).comp
    (MvPolynomial.finSuccEquiv ℤ n : MvPolynomial (Fin (n+1)) ℤ→+*Polynomial (MvPolynomial (Fin n) ℤ))

noncomputable def liftHom (n : ℕ) : MvPolynomial (Fin (n+1)) ℤ→+*MvPolynomial (Fin (n+2)) ℤ :=
  (MvPolynomial.rename Fin.succ).toRingHom.comp ((MvPolynomial.rename Fin.succ).toRingHom.comp (zeroHom n))

noncomputable def head (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) :=(p c).map (liftHom (A c))

noncomputable def epsilonHead (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) :=
  (p c).map (MvPolynomial.rename Fin.succ).toRingHom

theorem epsilon_coefficient (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    (epsilonHead A p c).coeff y=MvPolynomial.rename Fin.succ ((p c).coeff y):=Polynomial.coeff_map _ _
theorem epsilon_degree (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    ((epsilonHead A p c).coeff y).totalDegree≤((p c).coeff y).totalDegree:=by
  rw [epsilon_coefficient]
  exact MvPolynomial.totalDegree_rename_le _ _
theorem epsilon_mass (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    MvMass.mass ((epsilonHead A p c).coeff y)≤MvMass.mass ((p c).coeff y):=by
  rw [epsilon_coefficient]
  exact MvMass.rename_le _ _

theorem zeroHom_one {n : ℕ} (p : MvPolynomial (Fin (n+1)) ℤ) :zeroHom n p=MvTwoParameterCoefficient.one p 0:=rfl

theorem coefficient (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    ((head A p c).coeff y)=MvPolynomial.rename Fin.succ
      (MvPolynomial.rename Fin.succ (MvTwoParameterCoefficient.one ((p c).coeff y) 0)) :=by
  rw [head,Polynomial.coeff_map]
  rfl

theorem degree (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    ((head A p c).coeff y).totalDegree≤((p c).coeff y).totalDegree :=by
  rw [coefficient]
  exact (MvPolynomial.totalDegree_rename_le _ _).trans ((MvPolynomial.totalDegree_rename_le _ _).trans
    (MvTwoParameterCoefficient.one_degree _ _))

theorem mass (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) (y : ℕ) :
    MvMass.mass ((head A p c).coeff y)≤MvMass.mass ((p c).coeff y) :=by
  rw [coefficient]
  exact (MvMass.rename_le _ _).trans ((MvMass.rename_le _ _).trans (MvTwoParameterCoefficient.one_mass _ _))

theorem zero_evaluation {n : ℕ} (p : MvPolynomial (Fin (n+1)) ℤ) (z : Fin n→ℝ) :
    (zeroHom n p).eval₂ (Int.castRingHom ℝ) z=p.eval₂ (Int.castRingHom ℝ) (Fin.cons 0 z) :=by
  have H : (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) z).comp (zeroHom n)=
      MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons 0 z) :=by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [zeroHom]
    · intro i
      refine Fin.cases ?_ (fun j=>?_) i
      · simp [zeroHom,MvPolynomial.finSuccEquiv_X_zero]
      · simp [zeroHom,MvPolynomial.finSuccEquiv_X_succ]
  exact congrArg (fun f : MvPolynomial (Fin (n+1)) ℤ→+*ℝ=>f p) H

theorem lift_evaluation {n : ℕ} (p : MvPolynomial (Fin (n+1)) ℤ) (z : Fin n→ℝ) (δ ε : ℝ) :
    (liftHom n p).eval₂ (Int.castRingHom ℝ) (Fin.cons δ (Fin.cons ε z))=
      p.eval₂ (Int.castRingHom ℝ) (Fin.cons 0 z) :=by
  change (MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (zeroHom n p))).eval₂ _ _=_
  rw [MvPolynomial.eval₂_rename,MvPolynomial.eval₂_rename]
  exact zero_evaluation p z

theorem selected (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (c : List Bool) (z : Fin (A c)→ℝ) (δ ε : ℝ) :
    (head A p c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons δ (Fin.cons ε z)))=
      (p c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons 0 z)) :=by
  rw [head,Polynomial.map_map]
  apply congrArg (Polynomial.map · (p c))
  apply RingHom.ext
  intro f
  exact lift_evaluation f z δ ε

theorem epsilon_selected (A : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c+1)) ℤ))
    (c : List Bool) (z : Fin (A c)→ℝ) (δ ε : ℝ) :
    (epsilonHead A p c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons δ (Fin.cons ε z)))=
      (p c).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons ε z)) :=by
  apply Polynomial.ext
  intro y
  simp only [Polynomial.coeff_map,epsilon_coefficient,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_rename]
  rfl

end LeanCanny.Algebra.FixedWidthBivariateZeroLiftBits
