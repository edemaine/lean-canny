/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SelectedMultivariatePolynomialLift
public import LeanCanny.Algebra.FixedWidthBivariateParameterSuffixSpace
/-! # A parameter head is evaluated on one literal enlarged scalar suffix -/
@[expose] public section
namespace LeanCanny.Algebra.SelectedParameterHeadEvaluation
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem point {m : ℕ} (p : MvPolynomial (Fin (m+1)) ℤ) (z : Fin m→ℝ) (η : ℝ) :
    (SelectedMultivariatePolynomialLift.evaluate (MvPolynomial.aeval z).toRingHom p).eval η=
      p.eval₂ (Int.castRingHom ℝ) (Fin.cons η z) :=by
  have H : (Polynomial.evalRingHom η).comp
      (SelectedMultivariatePolynomialLift.evaluate (MvPolynomial.aeval z).toRingHom)=
        MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons η z) :=by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [SelectedMultivariatePolynomialLift.evaluate]
    · intro i
      refine Fin.cases ?_ (fun j=>?_) i
      all_goals simp [SelectedMultivariatePolynomialLift.evaluate,MvPolynomial.finSuccEquiv_apply]
  exact congrArg (fun φ=>φ p) H

theorem map_point {m : ℕ} (p : Polynomial (MvPolynomial (Fin (m+1)) ℤ)) (z : Fin m→ℝ) (η : ℝ) :
    (p.map (SelectedMultivariatePolynomialLift.evaluate (MvPolynomial.aeval z).toRingHom)).map
      (Polynomial.evalRingHom η)=p.map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons η z)) :=by
  apply Polynomial.ext
  intro y
  simp only [Polynomial.coeff_map,Polynomial.coe_evalRingHom]
  exact point (p.coeff y) z η

theorem layout {a b : ℕ} (h : a≤b) : (b-a)+(a+1)=b+1 :=by omega

noncomputable def enlarged {a b : ℕ} (h : a≤b) (p : Polynomial (MvPolynomial (Fin (a+1)) ℤ)) :
    Polynomial (MvPolynomial (Fin (b+1)) ℤ) :=
  (p.map (MvPolynomial.rename (FixedWidthParameterSuffixBits.shift (b-a))).toRingHom).map
    (MvPolynomial.rename (Fin.cast (layout h))).toRingHom

theorem suffix {a b : ℕ} (h : a≤b) (p : Polynomial (MvPolynomial (Fin (a+1)) ℤ))
    (z : Fin b→ℝ) (η : ℝ) :
    (enlarged h p).map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ) (Fin.cons η z))=
      p.map (MvPolynomial.eval₂Hom (Int.castRingHom ℝ)
        (Fin.cons η (fun i=>z (UniformIntegralPowerSchedule.embed h i)))) :=by
  have HT : (fun i : Fin (a+1)=>(Fin.cons η z : Fin (b+1)→ℝ)
      (Fin.cast (layout h) (FixedWidthParameterSuffixBits.shift (b-a) i)))=
      (Fin.cons η (fun i=>z (UniformIntegralPowerSchedule.embed h i)) : Fin (a+1)→ℝ) :=by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · rw [FixedWidthParameterSuffixBits.shift_zero]
      rfl
    · rw [FixedWidthParameterSuffixBits.shift_succ]
      have HE : Fin.cast (layout h) (⟨b-a+(j.val+1),by omega⟩ : Fin ((b-a)+(a+1)))=
          (UniformIntegralPowerSchedule.embed h j).succ :=by
        apply Fin.ext
        change b-a+(j.val+1)=(b-a+j.val)+1
        omega
      rw [HE]
      rfl
  apply Polynomial.ext
  intro y
  simp only [enlarged,Polynomial.coeff_map,MvPolynomial.coe_eval₂Hom]
  change (MvPolynomial.rename (Fin.cast (layout h))
    (MvPolynomial.rename (FixedWidthParameterSuffixBits.shift (b-a)) (p.coeff y))).eval₂
      (Int.castRingHom ℝ) (Fin.cons η z)=_
  rw [MvPolynomial.eval₂_rename,MvPolynomial.eval₂_rename]
  exact congrArg (fun point=>MvPolynomial.eval₂ (Int.castRingHom ℝ) point (p.coeff y)) HT

end LeanCanny.Algebra.SelectedParameterHeadEvaluation
