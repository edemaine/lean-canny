/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MultivariateTarskiDegreeBounds
public import LeanCanny.Algebra.MvCoefficientMass
public import LeanCanny.Algebra.PrincipalParameterMass
/-! # Actual integer MV mass of selected principal test circuits

A whole-output exponent box permits exact coefficient decoding. Integer
principal mass is inherited from the two original head/query coefficient
bounds, then charged once for the finite MV exponent box.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthTarskiMass
open Polynomial LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open scoped Classical BigOperators

theorem encode_mass_le (A W : ℕ) (p : MvPolynomial (Fin A) ℤ) :
    coefficientMass (FixedWidthKronecker.encode A W p)≤MvMass.mass p :=by
  conv_lhs=>rw [p.as_sum,map_sum]
  apply (coefficientMass_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro e _
  rw [FixedWidthKronecker.monomial,coefficientMass_monomial]

theorem mass_le_encoded (A W : ℕ) (p : MvPolynomial (Fin A) ℤ)
    (hp : ∀ e∈p.support,∀ i,e i<2^W) :
    MvMass.mass p≤count A W*coefficientMass (FixedWidthKronecker.encode A W p) :=by
  calc
    _=MvMass.mass (∑r : Fin (count A W),MvPolynomial.monomial (vector A W r) (p.coeff (vector A W r))) :=
      congrArg MvMass.mass (sum_monomials_eq A W p hp).symm
    _≤∑r : Fin (count A W),MvMass.mass (MvPolynomial.monomial (vector A W r) (p.coeff (vector A W r))) :=MvMass.sum_le _ _
    _≤∑_r : Fin (count A W),coefficientMass (FixedWidthKronecker.encode A W p) :=by
      apply Finset.sum_le_sum
      intro r _
      rw [MvMass.monomial,←FixedWidthKronecker.coefficient A W p hp r]
      exact coeff_natAbs_le_coefficientMass _ r.val
    _=count A W*coefficientMass (FixedWidthKronecker.encode A W p) :=by simp

theorem mass_le_pow (A W H : ℕ) (p : MvPolynomial (Fin A) ℤ)
    (hp : ∀ e∈p.support,∀ i,e i<2^W)
    (hM : coefficientMass (FixedWidthKronecker.encode A W p)≤2^H) :
    MvMass.mass p≤2^(A*W+H) :=by
  apply (mass_le_encoded A W p hp).trans
  apply (Nat.mul_le_mul_left _ hM).trans_eq
  unfold count
  rw [←pow_mul,←pow_add,Nat.mul_comm W A]

def headMass (dp bp : ℕ) :=bp+(dp+1).size
def seedMass (D dp dq bp bq : ℕ) :=PseudoRemainder.fixedSeedMassBound D dp (headMass dp bp) (headMass dq bq)
def principalMass (d s D dp dq bp bq : ℕ) :=
  PrincipalSubresultant.parameterMassBound (d+s) (max (headMass dp bp) (seedMass D dp dq bp bq))

theorem encoded_seed_mass (p q : (ℤ[X])[X]) (d D dp dq bp bq : ℕ)
    (hp : p.natDegree≤dp) (hq : q.natDegree≤dq)
    (hP : ∀ i,coefficientMass (p.coeff i)≤2^bp) (hQ : ∀ i,coefficientMass (q.coeff i)≤2^bq) :
    NestedMass.mass (PseudoRemainder.seed p q d D)≤2^seedMass D dp dq bp bq :=
  PseudoRemainder.seed_mass_le_pow p q d D dp (headMass dp bp) (headMass dq bq) hp
    (NestedMass.le_pow p dp bp hp hP) (NestedMass.le_pow q dq bq hq hQ)

theorem encoded_principal_mass (p q : (ℤ[X])[X]) (d s j D dp dq bp bq : ℕ)
    (hp : p.natDegree≤dp) (hq : q.natDegree≤dq)
    (hP : ∀ i,coefficientMass (p.coeff i)≤2^bp) (hQ : ∀ i,coefficientMass (q.coeff i)≤2^bq) :
    coefficientMass (PrincipalSubresultant.signedPsc p (PseudoRemainder.seed p q d D) d s j)≤
      2^principalMass d s D dp dq bp bq :=by
  apply PrincipalSubresultant.signedPsc_mass_le _ _ d s j (d+s) _ le_rfl
  · intro i
    apply (NestedMass.coeff_le p i).trans
    exact (NestedMass.le_pow p dp bp hp hP).trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  · intro i
    apply (NestedMass.coeff_le _ i).trans
    exact (encoded_seed_mass p q d D dp dq bp bq hp hq hP hQ).trans
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))

theorem principal_mass (F : FixedWidthTarskiPrincipalBits.Family) (c : List Bool) (j dp dq bp bq H : ℕ)
    (hp : (F.head c).natDegree≤dp) (hq : (F.query c).natDegree≤dq)
    (hP : ∀ i,MvMass.mass ((F.head c).coeff i)≤2^bp)
    (hQ : ∀ i,MvMass.mass ((F.query c).coeff i)≤2^bq)
    (hD : (FixedWidthTarskiPrincipalBits.polynomial F c j).totalDegree≤H) (hW : H<2^F.width c) :
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial F c j)≤
      2^(F.arity c*F.width c+principalMass (F.degree c) (F.seedDegree c) (F.bound c) dp dq bp bq) :=by
  apply mass_le_pow
  · intro e he i
    exact ((MvPolynomial.monomial_le_degreeOf i he).trans
      ((MvPolynomial.degreeOf_le_totalDegree _ i).trans hD)).trans_lt hW
  · have HE : FixedWidthTarskiPrincipalBits.encode F c (FixedWidthTarskiPrincipalBits.polynomial F c j)=
        PrincipalSubresultant.signedPsc (FixedWidthTarskiPrincipalBits.head F c)
          (PseudoRemainder.seed (FixedWidthTarskiPrincipalBits.head F c) (FixedWidthTarskiPrincipalBits.query F c)
            (F.degree c) (F.bound c)) (F.degree c) (F.seedDegree c) j :=by
      rw [FixedWidthTarskiPrincipalBits.polynomial,←PrincipalSubresultant.signedPsc_map_map,←PseudoRemainder.seed_map]
      rfl
    rw [show FixedWidthKronecker.encode (F.arity c) (F.width c)
      (FixedWidthTarskiPrincipalBits.polynomial F c j)=_ from HE]
    apply encoded_principal_mass _ _ _ _ _ _ dp dq bp bq
    · exact Polynomial.natDegree_map_le.trans hp
    · exact Polynomial.natDegree_map_le.trans hq
    · intro i
      change coefficientMass (((F.head c).map (FixedWidthTarskiPrincipalBits.encode F c)).coeff i)≤_
      rw [Polynomial.coeff_map]
      exact (encode_mass_le _ _ _).trans (hP i)
    · intro i
      change coefficientMass (((F.query c).map (FixedWidthTarskiPrincipalBits.encode F c)).coeff i)≤_
      rw [Polynomial.coeff_map]
      exact (encode_mass_le _ _ _).trans (hQ i)

theorem headMass_binary {dp bp : List Bool→ℕ} (hd : BinaryFn dp) (hb : BinaryFn bp) :
    BinaryFn (fun c=>headMass (dp c) (bp c)) :=hb.add ((hd.add (BinaryFn.const 1)).size)

theorem seedMass_binary {D dp dq bp bq : List Bool→ℕ}
    (hD : BinaryFn D) (hdp : BinaryFn dp) (hdq : BinaryFn dq) (hbp : BinaryFn bp) (hbq : BinaryFn bq) :
    BinaryFn (fun c=>seedMass (D c) (dp c) (dq c) (bp c) (bq c)) :=by
  have HP:=headMass_binary hdp hbp
  have HQ:=headMass_binary hdq hbq
  exact (((((BinaryFn.const 2).mul (hD.add (BinaryFn.const 1))).mul (HP.add (BinaryFn.const 1))).add HQ).add hdp.size).add HP

theorem principalMass_binary {d s D dp dq bp bq : List Bool→ℕ}
    (hd : BinaryFn d) (hs : BinaryFn s) (hD : BinaryFn D) (hdp : BinaryFn dp) (hdq : BinaryFn dq)
    (hbp : BinaryFn bp) (hbq : BinaryFn bq) :
    BinaryFn (fun c=>principalMass (d c) (s c) (D c) (dp c) (dq c) (bp c) (bq c)) :=by
  have HP:=headMass_binary hdp hbp
  have HT:=seedMass_binary hD hdp hdq hbp hbq
  have HM : BinaryFn (fun c=>max (headMass (dp c) (bp c)) (seedMass (D c) (dp c) (dq c) (bp c) (bq c))) :=
    (BinaryFn.ite (HP.le HT) HT HP).of_eq (fun c=>(Nat.max_def : max _ _=if _ then _ else _).symm)
  have HR:=hd.add hs
  exact ((HR.size.mul HR).add (HR.mul HM)).add HM

end LeanCanny.Algebra.FixedWidthTarskiMass
