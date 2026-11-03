/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralHistoryPhysicalRowMass
public import LeanCanny.Algebra.FixedWidthPolynomial
/-! # Original numeric budgets for full physical critical row mass

The ceiling uses a source coefficient box, degree, normal exponent and height
representative exponent. Its binary size never requires expanding an integer
coefficient or a powered physical row.
-/
@[expose] public section
namespace LeanCanny.Algebra.PhysicalCriticalMassBudget
open LeanCanny.Encoding LeanCanny.Computation MvPolynomial FixedWidthPolynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

theorem coefficient_box (A W C : ℕ) (p : MvPolynomial (Fin A) ℤ)
    (hs : ∀e∈p.support,∀i,e i<2^W) (hc : ∀e,(p.coeff e).natAbs≤2^C) :
    MvMass.mass p≤2^(A*W+C) := by
  calc
    _=MvMass.mass (∑r : Fin (count A W),monomial (vector A W r) (p.coeff (vector A W r))) :=
      congrArg MvMass.mass (sum_monomials_eq A W p hs).symm
    _≤∑r : Fin (count A W),MvMass.mass (monomial (vector A W r) (p.coeff (vector A W r))) := MvMass.sum_le _ _
    _≤∑_r : Fin (count A W),2^C := Finset.sum_le_sum (fun r _=>by rw [MvMass.monomial]; exact hc _)
    _=2^(A*W+C) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,count,←pow_mul,←pow_add]; congr 1; ring

def sourceExponent (A W C : ℕ) := A*W+C+A.size+1

theorem source_mass {n : ℕ} (low : MvPolynomial (Fin (n+1)) ℤ) (a : ℤ) (D W C : ℕ)
    (hd : low.totalDegree<D) (hw : D.size≤W)
    (hc : ∀e,(low.coeff e).natAbs≤2^C) (ha : a.natAbs≤2^C) :
    MvMass.mass (FermatCriticalHomogenization.polynomial low a D)≤2^sourceExponent (n+1) W C := by
  have HL : MvMass.mass low≤2^((n+1)*W+C) := coefficient_box _ _ _ _ (fun e he i=>
    ((monomial_le_degreeOf i he).trans (degreeOf_le_totalDegree _ i)).trans_lt
      (hd.trans_le ((Nat.lt_size_self D).le.trans (Nat.pow_le_pow_right (by decide) hw)))) hc
  have HP : MvMass.mass (∑i : Fin (n+1),(X i : MvPolynomial (Fin (n+1)) ℤ)^D)≤n+1 := by
    apply (MvMass.sum_le _ _).trans
    calc
      _≤∑_i : Fin (n+1),1 := Finset.sum_le_sum (fun i _=>by simpa only [MvMass.X,one_pow] using MvMass.pow_le (X i : MvPolynomial (Fin (n+1)) ℤ) D)
      _=n+1 := by simp
  have HM : MvMass.mass (MvPolynomial.C a*∑i : Fin (n+1),(X i : MvPolynomial (Fin (n+1)) ℤ)^D)≤2^C*(n+1) :=
    (MvMass.mul_le _ _).trans (Nat.mul_le_mul (by simpa only [MvMass.C] using ha) HP)
  have HN : 2^C*(n+1)≤2^((n+1)*W+C+(n+1).size) :=
    (Nat.mul_le_mul_left (2^C) (Nat.lt_size_self (n+1)).le).trans
      (by rw [←pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega))
  have HE : 2^((n+1)*W+C)≤2^((n+1)*W+C+(n+1).size) := Nat.pow_le_pow_right (by decide) (by omega)
  exact (MvMass.add_le low _).trans ((Nat.add_le_add (HL.trans HE) (HM.trans HN)).trans_eq (by
    unfold sourceExponent; rw [pow_succ]; omega))

def exponent (n A D U H : ℕ) := A+D.size+(n+1).size+U+H+2

theorem flat_bound {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (A D U H : ℕ)
    (hm : MvMass.mass p≤2^A) (hd : p.totalDegree≤D) :
    FlatAffineCriticalStage.massBound p (2^U) (2^H)≤2^exponent n A D U H := by
  let K:=A+D.size+(n+1).size+U+H
  let T:=2^K
  have HT : 1≤T := Nat.one_le_two_pow
  have HP : MvMass.mass p≤T := hm.trans (Nat.pow_le_pow_right (by decide) (by dsimp only [K]; omega))
  have HD : p.totalDegree*MvMass.mass p≤T :=
    (Nat.mul_le_mul (hd.trans (Nat.lt_size_self D).le) hm).trans
      (by rw [←pow_add]; exact Nat.pow_le_pow_right (by decide) (by dsimp only [K]; omega))
  have HN : (n+1)*2^U≤T :=
    (Nat.mul_le_mul_right (2^U) (Nat.lt_size_self (n+1)).le).trans
      (by rw [←pow_add]; exact Nat.pow_le_pow_right (by decide) (by dsimp only [K]; omega))
  have Hn : n*2^U≤T := (Nat.mul_le_mul_right (2^U) (Nat.le_succ n)).trans HN
  have HH : 2^H≤T := Nat.pow_le_pow_right (by decide) (by dsimp only [K]; omega)
  have HB : FlatAffineCriticalStage.massBound p (2^U) (2^H)≤4*T := by
    unfold FlatAffineCriticalStage.massBound
    omega
  exact HB.trans_eq (by
    change 4*2^K=2^(K+2)
    conv_rhs => rw [pow_add]
    norm_num
    exact Nat.mul_comm _ _)

theorem exponent_binary {n A D U H : List Bool→ℕ} (hn : UnaryFn n)
    (hA : BinaryFn A) (hD : BinaryFn D) (hU : BinaryFn U) (hH : BinaryFn H) :
    BinaryFn (fun q=>exponent (n q) (A q) (D q) (U q) (H q)) :=
  ((((hA.add hD.size).add (BinaryFn.ofUnary (hn.add (UnaryFn.const 1))).size).add hU).add hH).add (BinaryFn.const 2)

end LeanCanny.Algebra.PhysicalCriticalMassBudget
