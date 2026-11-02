/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.PartialHomogenization
public import LeanCanny.Algebra.IntegralMixedHistory

/-! # A fixed integer Fermat source for tilted coercive sampling

Dilation moves the small parameter out of the Fermat leading coefficient.
The new parameter is the first frozen coordinate; all previous parameters
shift by one and remain unscaled. No product of retained heights is needed.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedLeadingTiltedSource
open LeanCanny.ETR MvPolynomial
open ETR.PartialHomogenization
open scoped BigOperators

def degree (D : ℕ) : ℕ := 4*D+2

def lowTerm (k D u : ℕ) (t : Term) : Term :=
  .add (.mul (padded k D t) (padded k D t))
    (.mul (.const (-1)) (.mul ((Term.var 0).power (3*D)) (.var (u+1))))

theorem lowTerm_degree (k D u : ℕ) (t : Term) (ht : t.degreeBound ≤ D) :
    (lowTerm k D u t).degreeBound < degree D := by
  have H := degree_padded k D t ((physicalDegree_le k t).trans ht)
  simp only [lowTerm,Term.degreeBound,degree_power,Nat.mul_one,degree]
  omega

theorem lowTerm_arity (k D u : ℕ) (t : Term) :
    (lowTerm k D u t).arity ≤ max (t.arity+1) (u+2) := by
  have H := arity_padded k D t
  have HE := arity_power_le (Term.var 0) (3*D)
  simp only [lowTerm,Term.arity] at *
  omega

noncomputable def source (k D : ℕ) {n : ℕ} (u : Fin n) (t : Term) (ht : t.degreeBound ≤ D) :
    IntegralMixedHistory.SpatialSource n where
  low := (lowTerm k D u.val t).finitePolynomial (n+1)
  leading := 1
  degree := degree D
  degree_two := by simp only [degree]; omega
  low_degree := (Term.totalDegree_finitePolynomial _ _).trans_lt (lowTerm_degree k D u.val t ht)
  leading_ne_zero := one_ne_zero

noncomputable def polynomial (k D : ℕ) {n : ℕ} (u : Fin n) (t : Term) (ht : t.degreeBound ≤ D) :
    MvPolynomial (Fin (n+1)) ℤ :=
  (source k D u t ht).low + ∑ i, X i ^ degree D

theorem eval_lowTerm {R : Type*} [CommRing R] (k D u : ℕ) (t : Term)
    (ht : t.degreeBound ≤ D) (hu : k ≤ u) (s : R) (x : ℕ → R) :
    (lowTerm k D u t).eval (lifted k s x) =
      s^(2*D) * ((t.eval x)^2 - s^(D+1)*x u) := by
  have H := eval_padded k D t ((physicalDegree_le k t).trans ht) s x
  simp only [lowTerm,Term.eval,eval_power,lifted,H,ite_eq_right (by omega : ¬u<k),Int.cast_neg,Int.cast_one]
  rw [show 3*D=2*D+D by omega,pow_add,show D+1=D+1 by rfl,pow_succ,
    show s^(2*D)=(s^D)^2 by rw [mul_comm 2 D,pow_mul]]
  ring

noncomputable def frozenPenalty {R : Type*} [CommRing R] (k n D : ℕ) (x : ℕ → R) : R :=
  ∑ i : Fin n, if i.val < k then x i.val ^ degree D else 0

noncomputable def freePenalty {R : Type*} [CommRing R] (k n D : ℕ) (x : ℕ → R) : R :=
  ∑ i : Fin n, if i.val < k then 0 else x i.val ^ degree D

theorem eval_fermat {R : Type*} [CommRing R] (k n D : ℕ) (s : R) (x : ℕ → R) :
    (∑ i : Fin (n+1), lifted k s x i.val ^ degree D) =
      s ^ degree D + frozenPenalty k n D x + s ^ degree D * freePenalty k n D x := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,lifted,Fin.val_succ]
  rw [frozenPenalty,freePenalty,Finset.mul_sum,add_assoc,← Finset.sum_add_distrib]
  have H : (∑ i : Fin n, (if i.val < k then x i.val else s*x i.val)^degree D) =
      ∑ i : Fin n, ((if i.val<k then x i.val^degree D else 0)+
        s^degree D*(if i.val<k then 0 else x i.val^degree D)) := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [mul_pow]
  rw [H]

theorem eval_polynomial {R : Type*} [CommRing R] (k D : ℕ) {n : ℕ} (u : Fin n)
    (t : Term) (ht : t.degreeBound ≤ D) (ha : t.arity ≤ n) (hu : k ≤ u.val)
    (s : R) (x : ℕ → R) :
    (polynomial k D u t ht).eval₂ (Int.castRingHom R) (fun i => lifted k s x i.val) =
      s^(2*D) * ((t.eval x)^2 - s^(D+1)*x u.val + s^(2*D+2)*freePenalty k n D x) +
      frozenPenalty k n D x + s^degree D := by
  have HL : (lowTerm k D u.val t).arity ≤ n+1 :=
    (lowTerm_arity k D u.val t).trans (by omega)
  simp only [polynomial,source,eval₂_add,eval₂_sum,eval₂_pow,eval₂_X]
  rw [finite_eval _ _ _ HL,eval_lowTerm k D u.val t ht hu s x,eval_fermat]
  rw [show degree D=2*D+(2*D+2) by simp only [degree]; omega,pow_add]
  ring

end LeanCanny.Algebra.FixedLeadingTiltedSource
