/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedLeadingTiltedGradient
public import LeanCanny.ETR.FinitePolynomialPadding
public import LeanCanny.Geometry.AuxiliaryTiltEnergy

/-! # The literal integer term for an auxiliary bounded tilt

The auxiliary variable is appended after the original coordinates. Its single
initial degree charge is explicit. The real polynomial is the evaluation of
this original syntax, not an assumed coefficient source.
-/
@[expose] public section
namespace LeanCanny.Algebra.AuxiliaryTiltedTerm
open LeanCanny.ETR MvPolynomial FixedLeadingTiltedGradient
open scoped Classical BigOperators

noncomputable def polynomial (n : ℕ) (t : Term) : MvPolynomial (Fin n) ℝ :=
  t.eval (coordinateVars n)

def term (n : ℕ) (t : Term) : Term := .add (.mul t t) (.mul (.var n) (.var n))

theorem arity (n : ℕ) (t : Term) : (term n t).arity=max t.arity (n+1) := by
  simp only [term,Term.arity,max_self]

theorem degreeBound (n : ℕ) (t : Term) : (term n t).degreeBound=max (2*t.degreeBound) 2 := by
  simp only [term,Term.degreeBound]
  omega

theorem polynomial_eq_map (n : ℕ) (t : Term) :
    polynomial n t=(t.finitePolynomial n).map (Int.castRingHom ℝ) := by
  induction t with
  | const c => simp [polynomial,Term.eval,Term.finitePolynomial]
  | var i =>
    by_cases hi : i<n
    · simp [polynomial,Term.eval,coordinateVars,Term.finitePolynomial,hi]
    · simp [polynomial,Term.eval,coordinateVars,Term.finitePolynomial,hi]
  | add t u ht hu => simpa only [polynomial,Term.eval,Term.finitePolynomial,map_add] using congrArg₂ (·+·) ht hu
  | mul t u ht hu => simpa only [polynomial,Term.eval,Term.finitePolynomial,map_mul] using congrArg₂ (·*·) ht hu

theorem polynomial_term (n : ℕ) (t : Term) (ha : t.arity≤n) :
    polynomial (n+1) (term n t)=LeanCanny.Geometry.AuxiliaryTiltEnergy.augmented (polynomial n t) := by
  have H := Term.rename_finitePolynomial t n (n+1) ha (by omega)
  have HE : (Fin.castLE (by omega : n≤n+1) : Fin n → Fin (n+1))=Fin.castSucc := by
    funext i
    apply Fin.ext
    rfl
  rw [HE] at H
  rw [polynomial_eq_map,polynomial_eq_map]
  simp only [term,Term.finitePolynomial,map_add,map_mul]
  rw [← H]
  simp only [MvPolynomial.map_rename,show n<n+1 by omega,dite_true,MvPolynomial.map_X,
    LeanCanny.Geometry.AuxiliaryTiltEnergy.augmented,pow_two]
  rfl

theorem penalty_split (k n D : ℕ) :
    FixedLeadingTiltedSource.freePenalty k n D (coordinateVars n : ℕ → MvPolynomial (Fin n) ℝ)+
      frozen (R:=ℝ) (n:=n) k D=∑ i : Fin n, X i^(4*D+2) := by
  rw [frozen,FixedLeadingTiltedSource.freePenalty,FixedLeadingTiltedSource.frozenPenalty,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coordinateVars,i.isLt,↓reduceDIte,FixedLeadingTiltedSource.degree]
  split_ifs <;> simp

theorem free_derivative_tilted (k D : ℕ) {n : ℕ} (u j : Fin n) (t : Term) (s : ℝ) (hj : k≤j.val) :
    pderiv j (tilted k D u t s)=
      pderiv j (LeanCanny.Geometry.TiltedCoerciveComponentSampling.polynomial (polynomial n t) (2*D) u (s^(D+1))) := by
  have HE : LeanCanny.Geometry.TiltedCoerciveComponentSampling.polynomial (polynomial n t) (2*D) u (s^(D+1))=
      tilted k D u t s+C (s^(2*D+2))*frozen k D := by
    have HS : (s^(D+1))^2=s^(2*D+2) := by rw [← pow_mul]; congr 1; omega
    rw [LeanCanny.Geometry.TiltedCoerciveComponentSampling.polynomial,
      LeanCanny.Geometry.CoercivePolynomialSampling.regularization,HS]
    change (polynomial n t)^2+C (s^(2*D+2))*(∑ i : Fin n, X i^(2*(2*D)+2))-C (s^(D+1))*X u=_
    rw [show 2*(2*D)+2=4*D+2 by omega,← penalty_split k n D]
    simp only [tilted,polynomial]
    ring
  rw [HE,map_add,pderiv_C_mul,frozen_derivative k D j hj,mul_zero,add_zero]

end LeanCanny.Algebra.AuxiliaryTiltedTerm
