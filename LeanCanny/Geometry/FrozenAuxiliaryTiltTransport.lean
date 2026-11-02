/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FrozenCoordinateSubstitution
public import Mathlib.Algebra.MvPolynomial.Funext

/-! # Frozen original values and the free auxiliary tilt

Substitution commutes with the auxiliary q²+z² construction. Free derivatives
of the actual augmented tilt agree exactly with those of the substituted source;
the discarded frozen penalty is constant in every free direction.
-/
@[expose] public section
namespace LeanCanny.Geometry.FrozenCoordinateSubstitution
open MvPolynomial AuxiliaryTiltEnergy CoercivePolynomialSampling
open scoped Classical BigOperators
variable {n : ℕ}

theorem substitute_C (k : ℕ) (a : Fin n → ℝ) (c : ℝ) : substitute k a (C c)=C c :=
  eval₂_C _ _ _

theorem substitute_X (k : ℕ) (a : Fin n → ℝ) (i : Fin n) :
    substitute k a (X i)=coordinates k a i := eval₂_X _ _ _

theorem substitute_augmented (k : ℕ) (hk : k≤n) (a : Fin n → ℝ) (q : MvPolynomial (Fin n) ℝ) :
    substitute k (Fin.snoc a 0) (augmented q)=augmented (substitute k a q) := by
  apply MvPolynomial.funext
  intro y
  rw [eval_substitute,eval_augmented,eval_augmented,eval_substitute]
  have HE : point k (Fin.snoc a 0) y ∘ Fin.castSucc=point k a (y ∘ Fin.castSucc) := by
    funext i
    simp only [Function.comp_def,point,Fin.val_castSucc,Fin.snoc_castSucc]
  rw [HE]
  have HL : point k (Fin.snoc a 0) y (Fin.last n)=y (Fin.last n) := by
    simp only [point,Fin.val_last,show ¬n<k by omega,ite_false]
  rw [HL]

theorem derivative_penalty (k D : ℕ) (a : Fin n → ℝ) (j : Fin n) (hj : k≤j.val) :
    pderiv j (substitute k a (∑ i : Fin n, X i^(2*D+2)))=
      pderiv j (∑ i : Fin n, X i^(2*D+2)) := by
  rw [map_sum,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_pow,substitute_X]
  by_cases hi : i.val<k
  · have hn : j≠i := by intro he; subst i; omega
    simp [coordinates,hi,Derivation.leibniz_pow,pderiv_X,hn]
  · simp only [coordinates,hi,ite_false]

theorem derivative_augmented_tilt (k : ℕ) (hk : k≤n) (a : Fin n → ℝ)
    (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (δ : ℝ) (j : Fin (n+1)) (hj : k≤j.val) :
    pderiv j (substitute k (Fin.snoc a 0)
      (TiltedCoerciveComponentSampling.polynomial (augmented q) D (Fin.last n) δ))=
    pderiv j (TiltedCoerciveComponentSampling.polynomial (augmented (substitute k a q)) D (Fin.last n) δ) := by
  simp only [TiltedCoerciveComponentSampling.polynomial,regularization,map_sub,map_add,map_pow,map_mul,
    substitute_C,substitute_augmented k hk,substitute_X,coordinates,Fin.val_last,
    show ¬n<k by omega,ite_false]
  simp only [← map_pow,pderiv_C_mul]
  rw [derivative_penalty k D (Fin.snoc a 0) j hj]

theorem eval_augmented_tilt_free (k : ℕ) (hk : k≤n) (a : Fin n → ℝ)
    (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (δ : ℝ) (y : Fin (n+1) → ℝ)
    (j : Fin (n+1)) (hj : k≤j.val) :
    (pderiv j (TiltedCoerciveComponentSampling.polynomial (augmented q) D (Fin.last n) δ)).eval
      (point k (Fin.snoc a 0) y)=
    (pderiv j (TiltedCoerciveComponentSampling.polynomial (augmented (substitute k a q)) D (Fin.last n) δ)).eval y := by
  rw [← eval_free_derivative k (Fin.snoc a 0) y j hj,derivative_augmented_tilt k hk a q D δ j hj]

end LeanCanny.Geometry.FrozenCoordinateSubstitution
