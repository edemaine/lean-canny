/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.TermPowerFP

/-! # Division-free partial homogenization of integer expression trees

The new variable zero is the dilation parameter. Old variables shift by one;
variables below `k` remain coefficient parameters. Powers balance addition nodes
without expanding monomials. The degree allowance is charged to the original
expression, before any recursive sampling frame is built.
-/
@[expose] public section
namespace LeanCanny.ETR.PartialHomogenization
open Term

def physicalDegree (k : ℕ) : Term → ℕ
  | .const _ => 0
  | .var i => if i < k then 0 else 1
  | .add t u => max (physicalDegree k t) (physicalDegree k u)
  | .mul t u => physicalDegree k t + physicalDegree k u

def homogenize (k : ℕ) : Term → Term
  | .const z => .const z
  | .var i => .var (i + 1)
  | .add t u =>
      let d := max (physicalDegree k t) (physicalDegree k u)
      .add (.mul ((Term.var 0).power (d - physicalDegree k t)) (homogenize k t))
        (.mul ((Term.var 0).power (d - physicalDegree k u)) (homogenize k u))
  | .mul t u => .mul (homogenize k t) (homogenize k u)

def padded (k D : ℕ) (t : Term) : Term :=
  .mul ((Term.var 0).power (D - physicalDegree k t)) (homogenize k t)

def lifted {R : Type*} [CommRing R] (k : ℕ) (s : R) (x : ℕ → R) : ℕ → R
  | 0 => s
  | i + 1 => if i < k then x i else s * x i

theorem eval_power {R : Type*} [CommRing R] (x : ℕ → R) (t : Term) (n : ℕ) :
    (t.power n).eval x = (t.eval x) ^ n := by
  induction n with
  | zero => simp [Term.power,Term.eval]
  | succ n ih => simp only [Term.power,Term.eval,ih,pow_succ']

theorem degree_power (t : Term) (n : ℕ) : (t.power n).degreeBound = n * t.degreeBound := by
  induction n with
  | zero => simp [Term.power,Term.degreeBound]
  | succ n ih => simp only [Term.power,Term.degreeBound,ih,Nat.add_mul,Nat.one_mul]; omega

theorem physicalDegree_le (k : ℕ) (t : Term) : physicalDegree k t ≤ t.degreeBound := by
  induction t with
  | const z => rfl
  | var i => simp only [physicalDegree,Term.degreeBound]; split_ifs <;> omega
  | add t u ht hu => exact max_le_max ht hu
  | mul t u ht hu => exact Nat.add_le_add ht hu

theorem degree_homogenize (k : ℕ) (t : Term) :
    (homogenize k t).degreeBound ≤ physicalDegree k t + t.degreeBound := by
  induction t with
  | const z => simp [homogenize,physicalDegree,Term.degreeBound]
  | var i => simp only [homogenize,physicalDegree,Term.degreeBound]; split_ifs <;> omega
  | add t u ht hu =>
      simp only [homogenize,physicalDegree,Term.degreeBound,degree_power,Nat.mul_one] at *
      omega
  | mul t u ht hu =>
      simp only [homogenize,physicalDegree,Term.degreeBound] at *
      omega

theorem degree_padded (k D : ℕ) (t : Term) (h : physicalDegree k t ≤ D) :
    (padded k D t).degreeBound ≤ D + t.degreeBound := by
  have H := degree_homogenize k t
  simp only [padded,Term.degreeBound,degree_power,Nat.mul_one]
  omega

private theorem balance {R : Type*} [CommRing R] (s a : R) (d D : ℕ) (h : d ≤ D) :
    s ^ (D-d) * (s^d*a) = s^D*a := by
  rw [← mul_assoc,← pow_add,Nat.sub_add_cancel h]

theorem eval_homogenize {R : Type*} [CommRing R] (k : ℕ) (t : Term) (s : R) (x : ℕ → R) :
    (homogenize k t).eval (lifted k s x) = s ^ physicalDegree k t * t.eval x := by
  induction t with
  | const z => simp [homogenize,physicalDegree,Term.eval]
  | var i =>
      simp only [homogenize,physicalDegree,Term.eval,lifted]
      split_ifs <;> simp
  | add t u ht hu =>
      simp only [homogenize,Term.eval,eval_power,lifted,ht,hu,physicalDegree]
      rw [balance _ _ _ _ (Nat.le_max_left _ _),balance _ _ _ _ (Nat.le_max_right _ _),mul_add]
  | mul t u ht hu =>
      simp only [homogenize,Term.eval,ht,hu,physicalDegree,pow_add]
      ring

theorem eval_padded {R : Type*} [CommRing R] (k D : ℕ) (t : Term)
    (h : physicalDegree k t ≤ D) (s : R) (x : ℕ → R) :
    (padded k D t).eval (lifted k s x) = s^D * t.eval x := by
  simp only [padded,Term.eval,eval_power,lifted,eval_homogenize]
  exact balance s _ _ _ h

theorem arity_power_le (t : Term) (n : ℕ) : (t.power n).arity ≤ t.arity := by
  cases n with
  | zero => simp [Term.power,Term.arity]
  | succ n => exact (Term.arity_power t (n+1) (by omega)).le

theorem arity_homogenize (k : ℕ) (t : Term) : (homogenize k t).arity ≤ t.arity+1 := by
  induction t with
  | const z => simp [homogenize,Term.arity]
  | var i => simp [homogenize,Term.arity]
  | add t u ht hu =>
      have Ht := arity_power_le (Term.var 0) (max (physicalDegree k t) (physicalDegree k u)-physicalDegree k t)
      have Hu := arity_power_le (Term.var 0) (max (physicalDegree k t) (physicalDegree k u)-physicalDegree k u)
      simp only [homogenize,Term.arity] at *
      omega
  | mul t u ht hu => simp only [homogenize,Term.arity] at *; omega

theorem arity_padded (k D : ℕ) (t : Term) : (padded k D t).arity ≤ t.arity+1 := by
  have H := arity_homogenize k t
  have HE := arity_power_le (Term.var 0) (D-physicalDegree k t)
  simp only [padded,Term.arity] at *
  omega

theorem finite_eval {R : Type*} [CommRing R] (t : Term) (N : ℕ) (x : ℕ → R) (h : t.arity ≤ N) :
    (t.finitePolynomial N).eval₂ (Int.castRingHom R) (fun i => x i.val) = t.eval x := by
  induction t with
  | const z => exact MvPolynomial.eval₂_C (Int.castRingHom R) (fun i : Fin N => x i.val) z
  | var i =>
      have HI : i < N := by change i+1 ≤ N at h; omega
      simp [Term.finitePolynomial,Term.eval,HI]
  | add t u ht hu =>
      change max t.arity u.arity ≤ N at h
      simp only [Term.finitePolynomial,MvPolynomial.eval₂_add,Term.eval,
        ht (Nat.le_trans (Nat.le_max_left _ _) h),hu (Nat.le_trans (Nat.le_max_right _ _) h)]
  | mul t u ht hu =>
      change max t.arity u.arity ≤ N at h
      simp only [Term.finitePolynomial,MvPolynomial.eval₂_mul,Term.eval,
        ht (Nat.le_trans (Nat.le_max_left _ _) h),hu (Nat.le_trans (Nat.le_max_right _ _) h)]

end LeanCanny.ETR.PartialHomogenization
