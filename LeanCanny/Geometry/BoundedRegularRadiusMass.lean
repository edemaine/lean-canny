/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.BoundedRegularRadiusBounds

/-! # Integer height of the external radius family

Flattening the external parameter is used only to bound all integer
coefficients at once. It does not replace the original spatial source.
The bound is independent of the chosen radius.
-/
@[expose] public section
namespace LeanCanny.Geometry.BoundedRegularRadius
open LeanCanny.Algebra LeanCanny.Encoding
open scoped BigOperators Classical

noncomputable def flatten {ι : Type*} : Polynomial (MvPolynomial ι ℤ)→+*MvPolynomial (Option ι) ℤ :=
  Polynomial.eval₂RingHom (MvPolynomial.rename Option.some).toRingHom (MvPolynomial.X none)

noncomputable def expanded {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b : ℕ) := flatten (polynomial q D b)

def coefficientExponent (n D b : ℕ) :=
  BoundedRegularSource.regularizationExponent n D b 0+BoundedRegularSource.sourceMassExponent n D b 0+1

@[simp] theorem flatten_C {ι : Type*} (v : MvPolynomial ι ℤ) : flatten (Polynomial.C v)=MvPolynomial.rename Option.some v :=
  Polynomial.eval₂_C _ _

@[simp] theorem flatten_X {ι : Type*} : flatten (Polynomial.X : Polynomial (MvPolynomial ι ℤ))=MvPolynomial.X none :=
  Polynomial.eval₂_X _ _

theorem powerScalar_mass {ι : Type*} (offset slope : ℕ) :
    MvMass.mass (flatten (powerScalar (ι:=ι) offset slope))≤2^offset := by
  simp only [powerScalar,map_mul,map_pow,flatten_C,flatten_X,MvPolynomial.rename_C]
  have HP:=MvMass.pow_le (MvPolynomial.X (none : Option ι) : MvPolynomial (Option ι) ℤ) slope
  simp only [MvMass.X,one_pow] at HP
  have HC : MvMass.mass ((MvPolynomial.C (2 : ℤ) : MvPolynomial (Option ι) ℤ)^offset)≤2^offset := by
    simpa only [MvMass.C,show (2 : ℤ).natAbs=2 from rfl] using MvMass.pow_le (MvPolynomial.C (2 : ℤ) : MvPolynomial (Option ι) ℤ) offset
  simpa only [mul_one] using (MvMass.mul_le _ _).trans (Nat.mul_le_mul HC HP)

theorem sourcePolynomial_mass {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (b : ℕ) (hq : MvMass.mass q≤2^b) :
    MvMass.mass (flatten (sourcePolynomial q))≤2^BoundedZeroSource.massExponent n b 0 := by
  have HQ : MvMass.mass (MvPolynomial.rename Option.some
      (MvPolynomial.rename (Fin.castAdd 2) (MvPolynomial.rename (Fin.castAdd 2) q)))≤2^b :=
    (MvMass.rename_le _ _).trans ((MvMass.rename_le _ _).trans ((MvMass.rename_le _ _).trans hq))
  have HS : MvMass.mass (MvPolynomial.rename Option.some
      (∑ j : Fin (n+2),MvPolynomial.X (Fin.castAdd 2 j)^2 : MvPolynomial (Fin (n+4)) ℤ))≤n+2 := by
    apply (MvMass.rename_le _ _).trans
    apply (MvMass.sum_le _ _).trans
    calc
      _≤∑ _j : Fin (n+2),(1 : ℕ) := Finset.sum_le_sum (fun j _=>by simpa using MvMass.pow_le (MvPolynomial.X (Fin.castAdd 2 j)) 2)
      _=n+2 := by simp
  have HT : MvMass.mass ((MvPolynomial.X (none : Option (Fin (n+4))) : MvPolynomial _ ℤ)^2)≤1 := by
    simpa using MvMass.pow_le (MvPolynomial.X (none : Option (Fin (n+4)))) 2
  have HB : MvMass.mass (MvPolynomial.rename Option.some
      (∑ j : Fin (n+2),MvPolynomial.X (Fin.castAdd 2 j)^2 : MvPolynomial (Fin (n+4)) ℤ)-MvPolynomial.X none^2)≤2^(n+3).size :=
    ((MvMass.sub_le _ _).trans (Nat.add_le_add HS HT)).trans (by have H:=Nat.lt_size_self (n+3); omega)
  rw [sourcePolynomial,map_add,map_pow,map_pow,flatten_C,map_sub,flatten_C,map_pow,flatten_X]
  have H1:=(MvMass.pow_le _ 2).trans (Nat.pow_le_pow_left HQ 2)
  have H2:=(MvMass.pow_le _ 2).trans (Nat.pow_le_pow_left HB 2)
  rw [←pow_mul,Nat.mul_comm b 2] at H1
  rw [←pow_mul,Nat.mul_comm (n+3).size 2] at H2
  apply (MvMass.add_le _ _).trans ((Nat.add_le_add H1 H2).trans _)
  have H1' : 2^(2*b)≤2^(2*b+2*(n+3).size):=Nat.pow_le_pow_right (by decide) (by omega)
  have H2' : 2^(2*(n+3).size)≤2^(2*b+2*(n+3).size):=Nat.pow_le_pow_right (by decide) (by omega)
  simp only [BoundedZeroSource.massExponent,BoundedZeroSource.barrierMassExponent,mul_zero,zero_add,pow_succ]
  omega

theorem expanded_mass {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b : ℕ) (hq : MvMass.mass q≤2^b) :
    MvMass.mass (expanded q D b)≤2^coefficientExponent n D b := by
  have HL : MvMass.mass (flatten
      (powerScalar (BoundedZeroSource.perturbationExponent n D b 0) (perturbationSlope n D)*sourcePolynomial q-
        powerScalar (BoundedZeroSource.penaltyExponent n D 0) (BoundedZeroSource.powerDegree D)))≤
      2^BoundedRegularSource.lowMassExponent n D b 0 := by
    rw [map_sub,map_mul]
    have HP : MvMass.mass (flatten (powerScalar (BoundedZeroSource.perturbationExponent n D b 0) (perturbationSlope n D))*flatten (sourcePolynomial q))≤
        2^BoundedZeroSource.perturbationExponent n D b 0*2^BoundedZeroSource.massExponent n b 0 :=
      (MvMass.mul_le _ _).trans (Nat.mul_le_mul (powerScalar_mass _ _) (sourcePolynomial_mass q b hq))
    rw [←pow_add] at HP
    apply (MvMass.sub_le _ _).trans ((Nat.add_le_add HP (powerScalar_mass _ _)).trans _)
    have H1 : 2^(BoundedZeroSource.perturbationExponent n D b 0+BoundedZeroSource.massExponent n b 0)≤
        2^(BoundedZeroSource.perturbationExponent n D b 0+BoundedZeroSource.massExponent n b 0+BoundedZeroSource.penaltyExponent n D 0):=
      Nat.pow_le_pow_right (by decide) (by omega)
    have H2 : 2^BoundedZeroSource.penaltyExponent n D 0≤
        2^(BoundedZeroSource.perturbationExponent n D b 0+BoundedZeroSource.massExponent n b 0+BoundedZeroSource.penaltyExponent n D 0):=
      Nat.pow_le_pow_right (by decide) (by omega)
    unfold BoundedRegularSource.lowMassExponent
    rw [pow_succ]
    omega
  have HF : MvMass.mass (flatten (Polynomial.C
      (∑ j : Fin (n+4),MvPolynomial.X j^BoundedZeroSource.powerDegree D)))≤n+4 := by
    rw [flatten_C]
    apply (MvMass.rename_le _ _).trans
    apply (MvMass.sum_le _ _).trans
    calc
      _≤∑ _j : Fin (n+4),(1 : ℕ) := Finset.sum_le_sum (fun j _=>by simpa using MvMass.pow_le (MvPolynomial.X j) (BoundedZeroSource.powerDegree D))
      _=n+4 := by simp
  have HS : MvMass.mass (flatten
      (powerScalar (BoundedZeroSource.perturbationExponent n D b 0) (perturbationSlope n D)*sourcePolynomial q-
        powerScalar (BoundedZeroSource.penaltyExponent n D 0) (BoundedZeroSource.powerDegree D)+
        Polynomial.C (∑ j : Fin (n+4),MvPolynomial.X j^BoundedZeroSource.powerDegree D)))≤
      2^BoundedRegularSource.sourceMassExponent n D b 0 := by
    rw [map_add]
    apply (MvMass.add_le _ _).trans ((Nat.add_le_add HL HF).trans _)
    calc
      _≤(n+5)*2^BoundedRegularSource.lowMassExponent n D b 0 := by
        nlinarith [Nat.one_le_two_pow (n:=BoundedRegularSource.lowMassExponent n D b 0)]
      _≤2^(n+5).size*2^BoundedRegularSource.lowMassExponent n D b 0 :=
        Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
      _=_ := by rw [←pow_add,Nat.add_comm]; rfl
  unfold expanded polynomial
  rw [map_sub,map_mul,map_one]
  apply (MvMass.sub_le _ _).trans
  have HM : MvMass.mass (flatten (powerScalar (BoundedRegularSource.regularizationExponent n D b 0) (regularizationSlope n D))*_)≤
      2^BoundedRegularSource.regularizationExponent n D b 0*2^BoundedRegularSource.sourceMassExponent n D b 0 :=
    (MvMass.mul_le _ _).trans (Nat.mul_le_mul (powerScalar_mass _ _) HS)
  rw [←pow_add] at HM
  simp only [MvMass.one]
  unfold coefficientExponent
  rw [pow_succ]
  have HP:=Nat.one_le_two_pow (n:=BoundedRegularSource.regularizationExponent n D b 0+BoundedRegularSource.sourceMassExponent n D b 0)
  omega

theorem expanded_coefficient {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b : ℕ) (hq : MvMass.mass q≤2^b)
    (a : Option (Fin (n+4))→₀ℕ) :
    ((expanded q D b).coeff a).natAbs≤2^coefficientExponent n D b :=
  (MvMass.coeff_le _ _).trans (expanded_mass q D b hq)

theorem flatten_eq_symm {ι : Type*} (p : Polynomial (MvPolynomial ι ℤ)) :
    flatten p=(MvPolynomial.optionEquivLeft ℤ ι).symm p := rfl

theorem unflatten_flatten {ι : Type*} (p : Polynomial (MvPolynomial ι ℤ)) :
    MvPolynomial.optionEquivLeft ℤ ι (flatten p)=p := by
  rw [flatten_eq_symm]
  exact (MvPolynomial.optionEquivLeft ℤ ι).apply_symm_apply p

theorem coefficient_bound {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b : ℕ) (hq : MvMass.mass q≤2^b)
    (k : ℕ) (a : Fin (n+4)→₀ℕ) :
    (((polynomial q D b).coeff k).coeff a).natAbs≤2^coefficientExponent n D b := by
  have H:=expanded_coefficient q D b hq (a.optionElim k)
  rw [←MvPolynomial.optionEquivLeft_coeff_some_coeff_none] at H
  simpa only [expanded,unflatten_flatten,Finsupp.optionElim_apply_none,Finsupp.some_optionElim] using H

theorem coefficientExponent_binary {n D b : List Bool→ℕ} (hn : UnaryFn n) (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (fun q=>coefficientExponent (n q) (D q) (b q)) :=
  ((BoundedRegularControls.regularizationExponent_binary hn hD hb (BinaryFn.const 0)).add
    (BoundedRegularControls.sourceMassExponent_binary hn hD hb (BinaryFn.const 0))).add (BinaryFn.const 1)

end LeanCanny.Geometry.BoundedRegularRadius
