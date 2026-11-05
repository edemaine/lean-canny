/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardProfile
/-! # The literal sparse critical correlation recipe over a coefficient ring -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientCriticalCorrelationQuery
open LeanCanny.Encoding Polynomial
open scoped Classical

structure Metadata where
  count:ℕ
  age:ℕ
  scalar:ℕ
  physical:ℕ
  scalarPower:ℕ
  physicalPower:ℕ
  active:Bool

noncomputable def nativeMetadata (P:IntegralCriticalHistoryTask.Parameters)
    (T:IntegralMixedHeaderTablesBits.Tables) (key:List Bool) (stage:ℕ):Metadata:=
  let k:=fun _ : List Bool=>key
  let j:=fun _ : List Bool=>stage
  ⟨IntegralMixedFramedCriticalGuardBits.count P T k [],
    IntegralMixedFramedCriticalGuardBits.age P k j [],
    IntegralMixedFramedCriticalGuardBits.scalar P T k j [],
    IntegralMixedFramedCriticalGuardBits.physical P T k j [],
    IntegralMixedFramedCriticalGuardBits.scalarPower P k j [],
    IntegralMixedFramedCriticalGuardBits.physicalPower P k j [],
    decide (IntegralMixedFramedCriticalGuardBits.Active P T k j [])⟩

theorem nativeMetadata_planned (P:IntegralCriticalHistoryTask.Parameters)
    (T:IntegralMixedHeaderTablesBits.Tables) (L F C:List Bool→ℕ) (key:List Bool) (stage:ℕ):
    nativeMetadata (IntegralMixedFramedNormalizationBits.planned P L F C) T key stage=
      nativeMetadata P T key stage:=rfl

noncomputable def monomial {R:Type*} [CommRing R] (N i w:ℕ) (a:R):MvPolynomial (Fin N) R:=
  if hi:i<N then MvPolynomial.monomial (Finsupp.single ⟨i,hi⟩ w) a else 0

noncomputable def polynomial {R:Type*} [CommRing R] (M:Metadata) (d:R):MvPolynomial (Fin M.count) R:=
  if M.active then monomial M.count M.scalar M.scalarPower 1-
    monomial M.count M.physical M.physicalPower d else 0

theorem monomial_map {R S:Type*} [CommRing R] [CommRing S] (φ:R→+*S) (N i w:ℕ) (a:R):
    MvPolynomial.map φ (monomial N i w a)=monomial N i w (φ a):=by
  unfold monomial
  split_ifs
  · exact MvPolynomial.map_monomial _ _ _
  · exact map_zero _

theorem polynomial_map {R S:Type*} [CommRing R] [CommRing S] (φ:R→+*S) (M:Metadata) (d:R):
    MvPolynomial.map φ (polynomial M d)=polynomial M (φ d):=by
  unfold polynomial
  split_ifs
  · simp only [map_sub,monomial_map,map_one]
  · exact map_zero _

theorem polynomial_heq_of_eq {R:Type*} [CommRing R] (M N:Metadata) (h:M=N) (d:R):
    HEq (polynomial M d) (polynomial N d):=by
  cases h
  rfl

theorem polynomial_native (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T:IntegralMixedHeaderTablesBits.Tables) (key:List Bool) (stage:ℕ):
    polynomial (nativeMetadata P T key stage)
      (IntegralMixedFramedCriticalGuardBits.atKey (IntegralMixedFramedHistoryFamilyBits.family P D H) key
        (nativeMetadata P T key stage).age)=
      IntegralMixedFramedCriticalGuardBits.polynomial P D H T (fun _=>key) (fun _=>stage) []:=by
  unfold polynomial nativeMetadata IntegralMixedFramedCriticalGuardBits.polynomial
  simp only [decide_eq_true_eq]
  rfl

private theorem monomial_coeff_bounds (N i w:ℕ) (a:ℤ[X]) (K B:ℕ)
    (hD:a.natDegree≤K) (hM:coefficientMass a≤2^B) (e:Fin N→₀ ℕ):
    ((monomial N i w a).coeff e).natDegree≤K ∧ coefficientMass ((monomial N i w a).coeff e)≤2^B:=by
  unfold monomial
  split_ifs
  · rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact ⟨hD,hM⟩
    · simp only [Polynomial.natDegree_zero,coefficientMass_zero,Nat.zero_le,and_self]
  · simp only [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,Polynomial.natDegree_zero,coefficientMass_zero,Nat.zero_le,and_self]

theorem coefficient_degree_mass (M:Metadata) (d:ℤ[X]) (K B:ℕ)
    (hD:d.natDegree≤K) (hM:coefficientMass d≤2^B) (e:Fin M.count→₀ ℕ):
    ((polynomial M d).coeff e).natDegree≤K ∧
      coefficientMass ((polynomial M d).coeff e)≤2^(B+1):=by
  unfold polynomial
  split_ifs
  · rw [MvPolynomial.coeff_sub]
    have H1:=monomial_coeff_bounds M.count M.scalar M.scalarPower 1 K B
      (by simp only [Polynomial.natDegree_one,Nat.zero_le])
      (by rw [show (1:ℤ[X])=C (1:ℤ) from rfl,coefficientMass_C];exact Nat.one_le_two_pow) e
    have H2:=monomial_coeff_bounds M.count M.physical M.physicalPower d K B hD hM e
    refine ⟨(Polynomial.natDegree_sub_le _ _).trans (max_le H1.1 H2.1),?_⟩
    exact (coefficientMass_sub_le _ _).trans ((Nat.add_le_add H1.2 H2.2).trans_eq (by rw [pow_succ];omega))
  · simp only [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,Polynomial.natDegree_zero,coefficientMass_zero,Nat.zero_le,and_self]

end LeanCanny.Algebra.CoefficientCriticalCorrelationQuery
