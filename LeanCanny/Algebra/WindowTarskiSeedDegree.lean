/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PseudoRemainderParameterCoefficient
/-! # Window-query seeds have their declared outer degree

An independent window parameter supplies a nonzero highest coefficient in
every query power. Its seed coefficient is a nonzero multiple of the head
derivative. The underlying ring may itself retain another parameter.
-/
@[expose] public section
namespace LeanCanny.Algebra.WindowTarskiSeedDegree
open Polynomial PseudoRemainderParameterCoefficient
variable {R : Type*} [CommRing R]

noncomputable def affineQuery (q : R[X]) (a : R) : (R[X])[X] :=
  q.map Polynomial.C+Polynomial.C (Polynomial.C a*Polynomial.X)

theorem swap_affineQuery (q : R[X]) (a : R) :
    Polynomial.Bivariate.swap (affineQuery q a)=Polynomial.C q+Polynomial.C (Polynomial.C a)*Polynomial.X :=by
  simp only [affineQuery,map_add,Polynomial.Bivariate.swap_map_C,Polynomial.Bivariate.swap_C,
    Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X]

theorem coefficient_power (q : R[X]) (a : R) (e : ℕ) :
    coefficient ((affineQuery q a)^e) e=Polynomial.C (a^e) :=by
  have HD : (Polynomial.Bivariate.swap (affineQuery q a)).natDegree≤1 :=by
    rw [swap_affineQuery]
    exact (Polynomial.natDegree_add_le _ _).trans (max_le (by rw [Polynomial.natDegree_C]; omega)
      ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le))
  have HC : (Polynomial.Bivariate.swap (affineQuery q a)).coeff 1=Polynomial.C a :=by
    rw [swap_affineQuery]
    simp
  unfold coefficient
  rw [map_pow]
  have HE:=Polynomial.coeff_pow_of_natDegree_le (m:=e) HD
  simpa only [Nat.mul_one,HC,←map_pow] using HE

section Domain
variable [IsDomain R] [CharZero R]
attribute [local irreducible] PseudoRemainder.seed PseudoRemainderParameterCoefficient.coefficient

theorem seed_degree_of_constant_parameter_coefficient (p : R[X]) (f : (R[X])[X])
    (d D k : ℕ) (hd : 0<d) (hp : p.natDegree=d) (a : R) (ha : a≠0)
    (hf : coefficient f k=Polynomial.C a)
    (hD : (f*(p.map Polynomial.C).derivative).natDegree≤D) :
    (PseudoRemainder.seed (p.map Polynomial.C) f d D).natDegree=d-1 :=by
  have Hpn : p≠0 :=by intro H; rw [H,Polynomial.natDegree_zero] at hp; omega
  have Hpd : p.coeff d≠0 :=by rw [←hp,Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr Hpn
  have HS : d-1+1=d :=by omega
  have HS' :=congrArg (fun k : ℕ=>(k:R)) HS
  rw [Nat.cast_add,Nat.cast_one] at HS'
  have HCder : p.derivative.coeff (d-1)=p.coeff d*(d:R) :=by rw [Polynomial.coeff_derivative,HS,HS']
  have HderCoeff : p.derivative.coeff (d-1)≠0 :=by
    rw [HCder]
    exact mul_ne_zero Hpd (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd))
  have Hder : p.derivative≠0 :=by intro H; exact HderCoeff (by rw [H,Polynomial.coeff_zero])
  have HDerDegree : p.derivative.natDegree=d-1 :=
    le_antisymm ((Polynomial.natDegree_derivative_le p).trans (by omega))
      (Polynomial.le_natDegree_of_ne_zero HderCoeff)
  have HC : coefficient (PseudoRemainder.seed (p.map Polynomial.C) f d D) k=
      Polynomial.C (a*p.coeff d^(2*(D+1)))*p.derivative :=by
    rw [coefficient_seed p f d D hp.le,hf,PseudoRemainder.seed_constant p d D hd hp.le]
  have HN : a*p.coeff d^(2*(D+1))≠0:=mul_ne_zero ha (pow_ne_zero _ Hpd)
  have HL : d-1≤(PseudoRemainder.seed (p.map Polynomial.C) f d D).natDegree :=by
    have H:=PseudoRemainderParameterCoefficient.degree_le (PseudoRemainder.seed (p.map Polynomial.C) f d D) k
    rw [HC,Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr HN) Hder,
      Polynomial.natDegree_C,HDerDegree,Nat.zero_add] at H
    exact H
  have HU : (PseudoRemainder.seed (p.map Polynomial.C) f d D).natDegree<d :=
    PseudoRemainder.seed_natDegree_lt (R:=R[X]) (p.map Polynomial.C) f d D hd hD
  omega

theorem affine_power_seed_degree (p q : R[X]) (a : R) (ha : a≠0) (e d D : ℕ)
    (hd : 0<d) (hp : p.natDegree=d)
    (hD : ((affineQuery q a)^e*(p.map Polynomial.C).derivative).natDegree≤D) :
    (PseudoRemainder.seed (p.map Polynomial.C) ((affineQuery q a)^e) d D).natDegree=d-1 :=
  seed_degree_of_constant_parameter_coefficient p _ d D e hd hp (a^e) (pow_ne_zero _ ha)
    (coefficient_power q a e) hD

omit [IsDomain R] [CharZero R] in
theorem affineQuery_degree (q : R[X]) (a : R) (hq : q.natDegree≤1) :
    (affineQuery q a).natDegree≤1 :=
  (Polynomial.natDegree_add_le _ _).trans
    (max_le (Polynomial.natDegree_map_le.trans hq)
      (show (Polynomial.C (Polynomial.C a*Polynomial.X) : (R[X])[X]).natDegree≤1 by
        rw [Polynomial.natDegree_C]; omega))

theorem ternary_seed_degree (p q : R[X]) (a : R) (ha : a≠0) (e : Fin 3) (d : ℕ)
    (hd : 0<d) (hp : p.natDegree=d) (hq : q.natDegree≤1) :
    (PseudoRemainder.seed (p.map Polynomial.C) ((affineQuery q a)^e.val) d (d+2)).natDegree=d-1 :=by
  apply affine_power_seed_degree p q a ha e.val d (d+2) hd hp
  have HF : ((affineQuery q a)^e.val).natDegree≤e.val :=
    Polynomial.natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left e.val (affineQuery_degree q a hq))
  have HP : (p.map Polynomial.C).natDegree≤d:=Polynomial.natDegree_map_le.trans hp.le
  have HD : ((p.map Polynomial.C).derivative).natDegree≤d-1 :=
    (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le_sub_right HP 1)
  exact Polynomial.natDegree_mul_le.trans (by have HE:=e.isLt; omega)

end Domain
end LeanCanny.Algebra.WindowTarskiSeedDegree
