/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ClearedCoordinateCritical
public import LeanCanny.Algebra.PurePowerCommonScaling
/-! # Simultaneous scaling of actual frozen denominator and numerators

Degree-D clearing makes every critical lower row scale by s^D. The
spatial degree and the finite reduction basis are unchanged.
-/
@[expose] public section
namespace LeanCanny.Algebra.ClearedCoordinateCommonScaling
open MvPolynomial CommonDenominatorSpecialization
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {σ τ R : Type*} [Fintype σ] [CommRing R]

theorem factor (D : ℕ) (q s : R) (v : σ→MvPolynomial τ R) (e : σ→₀ℕ) (he : e.degree≤D) :
    CommonDenominatorSpecialization.factor D (s*q) (fun i=>C s*v i) e=
      C (s^D)*CommonDenominatorSpecialization.factor D q v e :=by
  simp only [CommonDenominatorSpecialization.factor,mul_pow,Finset.prod_mul_distrib,
    ←map_pow,←map_prod,Finset.prod_pow_eq_pow_sum,←Finsupp.degree_eq_sum]
  simp only [map_mul]
  calc
    _=(C (s^(D-e.degree))*C (s^e.degree))*(C (q^(D-e.degree))*∏ i,v i^e i):=by ring
    _=_:=by rw [←map_mul,←pow_add,Nat.sub_add_cancel he]

theorem clear (D : ℕ) (q s : R) (v : σ→MvPolynomial τ R) (p : MvPolynomial σ R)
    (hp : p.totalDegree≤D) :
    CommonDenominatorSpecialization.clear D (s*q) (fun i=>C s*v i) p=
      C (s^D)*CommonDenominatorSpecialization.clear D q v p :=by
  change (∑ e∈p.support,C (p.coeff e)*CommonDenominatorSpecialization.factor D (s*q) (fun i=>C s*v i) e)=
    C (s^D)*(∑ e∈p.support,C (p.coeff e)*CommonDenominatorSpecialization.factor D q v e)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [factor D q s v e ((MvPolynomial.le_totalDegree he).trans hp)]
  ring

variable {n dim : ℕ}

theorem coordinate (q s : R) (H : ℕ→R) (offset dim i : ℕ) :
    ClearedCoordinateBlock.coordinate (s*q) (fun i=>s*H i) offset dim i=
      C s*ClearedCoordinateBlock.coordinate q H offset dim i:=by
  unfold ClearedCoordinateBlock.coordinate
  split_ifs <;> simp only [map_mul,mul_assoc]

theorem specialize (D : ℕ) (q s : R) (H : ℕ→R) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) (hp : p.totalDegree≤D) :
    ClearedCoordinateBlock.specialize D (s*q) (fun i=>s*H i) offset dim p=
      C (s^D)*ClearedCoordinateBlock.specialize D q H offset dim p:=by
  unfold ClearedCoordinateBlock.specialize
  simp only [coordinate]
  exact clear D q s _ p hp

theorem frozenPower (s : R) (H : ℕ→R) (offset dim D : ℕ) :
    CoordinateBlockSpecialization.frozenPower (n:=n) (fun i=>s*H i) offset dim D=
      s^D*CoordinateBlockSpecialization.frozenPower (n:=n) H offset dim D:=by
  unfold CoordinateBlockSpecialization.frozenPower
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [mul_pow,mul_zero]

theorem block_lower (D : ℕ) (q s : R) (H : ℕ→R) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) (a : R) (hp : p.totalDegree≤D) :
    ClearedCoordinateBlock.lower D (s*q) (fun i=>s*H i) offset dim p a=
      C (s^D)*ClearedCoordinateBlock.lower D q H offset dim p a:=by
  unfold ClearedCoordinateBlock.lower
  rw [specialize D q s H offset dim p hp,frozenPower]
  simp only [map_mul]
  ring

end LeanCanny.Algebra.ClearedCoordinateCommonScaling
