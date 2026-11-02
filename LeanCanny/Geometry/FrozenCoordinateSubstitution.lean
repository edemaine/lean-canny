/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.AuxiliaryTiltComponentSampling
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Literal frozen-coordinate substitution and free derivatives

The frozen values are real evaluations under a selected old hom. Substitution
changes polynomial coefficients, not the saved hom or the original coordinate
ordering. The auxiliary last coordinate is left free when k is at most n.
-/
@[expose] public section
namespace LeanCanny.Geometry.FrozenCoordinateSubstitution
open MvPolynomial
open scoped Classical
variable {n : ℕ}

def point (k : ℕ) (a x : Fin n → ℝ) : Fin n → ℝ := fun i => if i.val<k then a i else x i

noncomputable def coordinates (k : ℕ) (a : Fin n → ℝ) : Fin n → MvPolynomial (Fin n) ℝ :=
  fun i => if i.val<k then C (a i) else X i

noncomputable def substitute (k : ℕ) (a : Fin n → ℝ) :
    MvPolynomial (Fin n) ℝ →+* MvPolynomial (Fin n) ℝ := eval₂Hom C (coordinates k a)

theorem eval_substitute (k : ℕ) (a x : Fin n → ℝ) (q : MvPolynomial (Fin n) ℝ) :
    (substitute k a q).eval x=q.eval (point k a x) := by
  rw [substitute,coe_eval₂Hom,eval_eval₂]
  have HC : (eval x).comp C=RingHom.id ℝ := by ext; simp
  rw [HC]
  congr 1
  funext i
  simp only [coordinates,point]
  split_ifs <;> simp

theorem point_idempotent (k : ℕ) (a x : Fin n → ℝ) : point k a (point k a x)=point k a x := by
  funext i
  simp only [point]
  split_ifs <;> rfl

theorem point_fixed (k : ℕ) (a x : Fin n → ℝ) (h : ∀ i, i.val<k → x i=a i) : point k a x=x := by
  funext i
  by_cases hi : i.val<k
  · simp only [point,hi,ite_true,h i hi]
  · simp only [point,hi,ite_false]

theorem continuous_point (k : ℕ) (a : Fin n → ℝ) : Continuous (point k a) := by
  apply continuous_pi
  intro i
  by_cases hi : i.val<k
  · simpa only [point,hi,ite_true] using (continuous_const : Continuous (fun _ : Fin n → ℝ => a i))
  · simpa only [point,hi,ite_false] using (continuous_apply i : Continuous (fun x : Fin n → ℝ => x i))

theorem derivative_coordinates (k : ℕ) (a : Fin n → ℝ) (j : Fin n) (hj : k≤j.val) (i : Fin n) :
    pderiv j (coordinates k a i)=if i=j then 1 else 0 := by
  by_cases hi : i.val<k
  · have HN : j≠i := by intro he; subst i; omega
    have HN' : i≠j := Ne.symm HN
    simp [coordinates,hi,HN']
  · simp [coordinates,hi,pderiv_X,Pi.single_apply,eq_comm]

theorem derivative_substitute (k : ℕ) (a : Fin n → ℝ) (j : Fin n) (hj : k≤j.val)
    (q : MvPolynomial (Fin n) ℝ) :
    pderiv j (substitute k a q)=substitute k a (pderiv j q) := by
  induction q using MvPolynomial.induction_on with
  | C c => simp [substitute]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,Derivation.leibniz,smul_eq_mul,hp]
    have HX : substitute k a (X i)=coordinates k a i := eval₂_X _ _ _
    rw [HX,derivative_coordinates k a j hj i]
    simp only [pderiv_X,Pi.single_apply,map_add,map_mul]
    by_cases he : i=j
    · subst i
      simp only [ite_true,map_one,mul_one]
      rw [HX]
    · simp only [he,ite_false,map_zero,mul_zero]
      rw [HX]

theorem eval_free_derivative (k : ℕ) (a x : Fin n → ℝ) (j : Fin n) (hj : k≤j.val)
    (q : MvPolynomial (Fin n) ℝ) :
    (pderiv j (substitute k a q)).eval x=(pderiv j q).eval (point k a x) := by
  rw [derivative_substitute k a j hj,eval_substitute]

theorem point_snoc (k : ℕ) (hk : k≤n) (a x : Fin n → ℝ) (b z : ℝ) :
    point k (Fin.snoc a b) (Fin.snoc x z)=Fin.snoc (point k a x) z := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [point,Fin.val_last,Fin.snoc_last,show ¬n<k by omega,ite_false]
  · simp only [point,Fin.val_castSucc,Fin.snoc_castSucc]

end LeanCanny.Geometry.FrozenCoordinateSubstitution
