/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedLeadingTiltedSource
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Free-coordinate derivatives under the fixed-leading dilation -/
@[expose] public section
namespace LeanCanny.Algebra.FixedLeadingTiltedGradient
open MvPolynomial
open scoped Classical BigOperators
variable {R : Type*} [CommRing R] {n : ℕ}

noncomputable def dilation (k : ℕ) (s : R) : Fin (n+1) → MvPolynomial (Fin n) R :=
  Fin.cases (C s) (fun i => if i.val < k then X i else C s*X i)

theorem derivative_dilation (k : ℕ) (s : R) (j : Fin n) (hj : k ≤ j.val) (i : Fin (n+1)) :
    pderiv j (dilation k s i) = if i=j.succ then C s else 0 := by
  refine Fin.cases ?_ (fun a => ?_) i
  · have H : (0 : Fin (n+1)) ≠ j.succ := fun h => Fin.succ_ne_zero j h.symm
    simp [dilation,H]
  · by_cases H : a=j
    · subst a
      simp [dilation,show ¬j.val<k by omega]
    · have HJ : j≠a := Ne.symm H
      simp only [dilation,Fin.cases_succ,Fin.succ_inj,H,ite_false]
      split_ifs <;> simp [HJ]

theorem derivative_pullback (k : ℕ) (s : R) (j : Fin n) (hj : k ≤ j.val)
    (p : MvPolynomial (Fin (n+1)) R) :
    pderiv j (eval₂ C (dilation k s) p) =
      C s * eval₂ C (dilation k s) (pderiv j.succ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [eval₂_add,map_add,hp,hq,mul_add]
  | mul_X p i hp =>
      simp only [eval₂_mul,eval₂_X,Derivation.leibniz,smul_eq_mul,derivative_dilation k s j hj,
        hp,pderiv_X,Pi.single_apply,eval₂_add,eval₂_mul]
      by_cases H : i=j.succ
      · simp only [H,ite_true,eval₂_one]
        ring
      · simp only [H,ite_false,eval₂_zero,mul_zero,zero_add]
        ring

noncomputable def coordinateVars (n : ℕ) : ℕ → MvPolynomial (Fin n) R :=
  fun i => if h : i<n then X ⟨i,h⟩ else 0

theorem dilation_eq (k : ℕ) (s : R) :
    dilation k s = fun i : Fin (n+1) => ETR.PartialHomogenization.lifted k (C s) (coordinateVars n) i.val := by
  funext i
  refine Fin.cases rfl (fun a => ?_) i
  simp [dilation,ETR.PartialHomogenization.lifted,coordinateVars,a.isLt]

noncomputable def frozen (k D : ℕ) : MvPolynomial (Fin n) R :=
  FixedLeadingTiltedSource.frozenPenalty k n D (coordinateVars n)

noncomputable def tilted (k D : ℕ) (u : Fin n) (t : ETR.Term) (s : R) : MvPolynomial (Fin n) R :=
  (t.eval (coordinateVars n))^2-C (s^(D+1))*X u+
    C (s^(2*D+2))*FixedLeadingTiltedSource.freePenalty k n D (coordinateVars n)

theorem frozen_derivative (k D : ℕ) (j : Fin n) (hj : k ≤ j.val) :
    pderiv j (frozen (R:=R) (n:=n) k D)=0 := by
  rw [frozen,FixedLeadingTiltedSource.frozenPenalty,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases H : i.val<k
  · have HJ : j≠i := by intro HE; subst i; omega
    simp [H,coordinateVars,i.isLt,HJ]
  · simp [H]

theorem pullback_value (k D : ℕ) (u : Fin n) (t : ETR.Term) (ht : t.degreeBound ≤ D)
    (ha : t.arity ≤ n) (hu : k ≤ u.val) (s : R) :
    eval₂ (C.comp (Int.castRingHom R)) (dilation k s) (FixedLeadingTiltedSource.polynomial k D u t ht) =
      C (s^(2*D)) * tilted k D u t s + frozen k D + C (s^FixedLeadingTiltedSource.degree D) := by
  have H := FixedLeadingTiltedSource.eval_polynomial k D u t ht ha hu
    (C s : MvPolynomial (Fin n) R) (coordinateVars n)
  rw [← dilation_eq k s] at H
  have HC : Int.castRingHom (MvPolynomial (Fin n) R)=C.comp (Int.castRingHom R) := by ext; simp
  rw [HC] at H
  simpa only [tilted,frozen,coordinateVars,u.isLt,↓reduceDIte,← map_pow] using H

theorem derivative_source (k D : ℕ) (u j : Fin n) (t : ETR.Term) (ht : t.degreeBound ≤ D)
    (ha : t.arity ≤ n) (hu : k ≤ u.val) (hj : k ≤ j.val) (s : R) :
    C s * eval₂ (C.comp (Int.castRingHom R)) (dilation k s)
      (pderiv j.succ (FixedLeadingTiltedSource.polynomial k D u t ht)) =
      C (s^(2*D)) * pderiv j (tilted k D u t s) := by
  have H := congrArg (pderiv j) (pullback_value k D u t ht ha hu s)
  rw [show eval₂ (C.comp (Int.castRingHom R)) (dilation k s)
      (FixedLeadingTiltedSource.polynomial k D u t ht) =
      eval₂ C (dilation k s) ((FixedLeadingTiltedSource.polynomial k D u t ht).map (Int.castRingHom R))
    by rw [eval₂_map]] at H
  rw [derivative_pullback k s j hj,pderiv_map,eval₂_map] at H
  simpa only [map_add,pderiv_C_mul,frozen_derivative k D j hj,pderiv_C,add_zero] using H

def point (k : ℕ) (s : R) (x : Fin n → R) : Fin (n+1) → R :=
  Fin.cases s (fun i => if i.val < k then x i else s*x i)

theorem eval_dilation (k : ℕ) (s : R) (x : Fin n → R) :
    (fun i => eval x (dilation k s i)) = point k s x := by
  funext i
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [dilation,point]
  · simp only [dilation,point,Fin.cases_succ]
    split_ifs <;> simp

theorem eval_derivative_source (k D : ℕ) (u j : Fin n) (t : ETR.Term) (ht : t.degreeBound ≤ D)
    (ha : t.arity ≤ n) (hu : k ≤ u.val) (hj : k ≤ j.val) (s : R) (x : Fin n → R) :
    s * eval₂ (Int.castRingHom R) (point k s x)
      (pderiv j.succ (FixedLeadingTiltedSource.polynomial k D u t ht)) =
      s^(2*D) * eval x (pderiv j (tilted k D u t s)) := by
  have H := congrArg (eval x) (derivative_source k D u j t ht ha hu hj s)
  simp only [map_mul,eval_C,eval_eval₂,eval_dilation] at H
  have HC : (eval x).comp (C.comp (Int.castRingHom R)) = Int.castRingHom R := by
    ext z
    simp
  simpa only [HC] using H

theorem critical_iff [IsDomain R] (k D : ℕ) (u : Fin n) (t : ETR.Term)
    (ht : t.degreeBound ≤ D) (ha : t.arity ≤ n) (hu : k ≤ u.val)
    (s : R) (hs : s ≠ 0) (x : Fin n → R) :
    (∀ j : Fin n, k ≤ j.val → eval₂ (Int.castRingHom R) (point k s x)
      (pderiv j.succ (FixedLeadingTiltedSource.polynomial k D u t ht)) = 0) ↔
    (∀ j : Fin n, k ≤ j.val → eval x (pderiv j (tilted k D u t s)) = 0) := by
  constructor
  · intro H j hj
    have HE := eval_derivative_source k D u j t ht ha hu hj s x
    rw [H j hj,mul_zero] at HE
    exact (mul_eq_zero.mp HE.symm).resolve_left (pow_ne_zero _ hs)
  · intro H j hj
    have HE := eval_derivative_source k D u j t ht ha hu hj s x
    rw [H j hj,mul_zero] at HE
    exact (mul_eq_zero.mp HE).resolve_left hs

/-- The new E coordinate and every old coefficient parameter belong to the
frozen prefix. Its index is valid because the objective is a free coordinate. -/
def offset (k : ℕ) (u : Fin n) (hu : k ≤ u.val) : Fin (n+1) := ⟨k+1,by omega⟩

theorem parameter_retained (k : ℕ) (s : R) (x : Fin n → R) (i : Fin n) (hi : i.val < k) :
    point k s x i.succ = x i := by simp [point,hi]

theorem parameter_zero (k : ℕ) (s : R) (x : Fin n → R) : point k s x 0 = s := rfl

end LeanCanny.Algebra.FixedLeadingTiltedGradient
