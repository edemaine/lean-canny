/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientIndexedRationalClearing
public import LeanCanny.Algebra.CoefficientHeightBankNaturalProducts
public import LeanCanny.Algebra.IntegralMixedFramedBankTermPolynomial
/-! # Literal common-bank term clearing at the actual physical columns -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientBankTermQuery
open LeanCanny.Encoding IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Arguments (R:Type*) where
  horizon:ℕ
  width:ℕ
  birth:ℕ
  dimension:ℕ
  common:R
  cofactor:ℕ→R
  column:Fin birth→Fin dimension

variable {R S:Type*} [CommRing R] [CommRing S]

noncomputable def Arguments.map (φ:R→+*S) (A:Arguments R):Arguments S:=
  ⟨A.horizon,A.width,A.birth,A.dimension,φ A.common,fun i=>φ (A.cofactor i),A.column⟩

noncomputable def numerator (A:Arguments R) (i:ℕ):MvPolynomial (Fin A.dimension) R:=
  if hi:i<A.birth then
    MvPolynomial.C (A.cofactor (A.birth-1-i))*
      MvPolynomial.X (A.column ⟨A.birth-1-i,by omega⟩)^
        UniformIntegralPowerSchedule.birth A.horizon (2^A.width) i
  else 0

noncomputable def denominator (A:Arguments R) (_i:ℕ):MvPolynomial (Fin A.dimension) R:=
  MvPolynomial.C A.common

noncomputable def polynomial (A:Arguments R) (p:LeanCanny.ETR.Term):MvPolynomial (Fin A.dimension) R:=
  CoefficientIndexedRationalClearing.term p (numerator A) (denominator A)

theorem numerator_map (φ:R→+*S) (A:Arguments R) (i:ℕ):
    MvPolynomial.map φ (numerator A i)=numerator (A.map φ) i:=by
  unfold numerator Arguments.map
  split_ifs
  · simp only [map_mul,map_pow,MvPolynomial.map_C,MvPolynomial.map_X]
  · exact map_zero _

theorem denominator_map (φ:R→+*S) (A:Arguments R) (i:ℕ):
    MvPolynomial.map φ (denominator A i)=denominator (A.map φ) i:=by
  exact MvPolynomial.map_C _ _

theorem polynomial_map (φ:R→+*S) (A:Arguments R) (p:LeanCanny.ETR.Term):
    MvPolynomial.map φ (polynomial A p)=polynomial (A.map φ) p:=by
  simp only [polynomial,CoefficientIndexedRationalClearing.term_map,numerator_map,denominator_map]

theorem polynomial_heq_of_eq (A B:Arguments R) (h:A=B) (p:LeanCanny.ETR.Term):
    HEq (polynomial A p) (polynomial B p):=by
  cases h
  rfl

noncomputable def ofBank {B:Type*} [CommRing B] {m:ℕ} (bank:CoefficientHeightBank R B m)
    (horizon width dimension:ℕ) (column:Fin m→Fin dimension):Arguments R:=
  ⟨horizon,width,m,dimension,bank.commonDenominator,bank.totalCofactor,column⟩

theorem ofBank_map {A B:Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra S B]
    {m:ℕ} (φ:R→+*S) (ψ:A→+*B) {x:CoefficientHeightBank R A m} {y:CoefficientHeightBank S B m}
    (H:x.Specializes φ ψ y) (horizon width dimension:ℕ) (column:Fin m→Fin dimension):
    (ofBank x horizon width dimension column).map φ=ofBank y horizon width dimension column:=
  congrArg₂ (fun q c=>(⟨horizon,width,m,dimension,q,c,column⟩:Arguments S))
    H.commonDenominator (funext H.totalCofactor)

noncomputable def ofSnapshot (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool) (N:ℕ) (column:Fin (IntegralMixedFramedBankSnapshotBits.atKey P D H key).count→Fin N):Arguments ℤ:=
  let s:=IntegralMixedFramedBankSnapshotBits.atKey P D H key
  ⟨P.cap (pairFst key)+1,P.width (pairFst key),s.count,N,s.common,s.cofactor,column⟩

private theorem numerator_snapshot (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool) (N:ℕ) (column:Fin (IntegralMixedFramedBankSnapshotBits.atKey P D H key).count→Fin N) (i:ℕ):
    numerator (ofSnapshot P D H key N column) i=
      MvPolynomial.rename column (IntegralMixedFramedBankTermBits.numeratorPolynomial P D H key i):=by
  unfold numerator ofSnapshot IntegralMixedFramedBankTermBits.numeratorPolynomial
  split_ifs
  · simp only [map_mul,map_pow,MvPolynomial.rename_C,MvPolynomial.rename_X]
    rfl
  · exact (map_zero _).symm

private theorem denominator_snapshot (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool) (N:ℕ) (column:Fin (IntegralMixedFramedBankSnapshotBits.atKey P D H key).count→Fin N) (i:ℕ):
    denominator (ofSnapshot P D H key N column) i=
      MvPolynomial.rename column (IntegralMixedFramedBankTermBits.denominatorPolynomial P D H key i):=by
  exact (MvPolynomial.rename_C _ _).symm

/-- Exact native clearing, including chronological reversal and zero extension. -/
theorem polynomial_native (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key:List Bool) (N:ℕ) (column:Fin (IntegralMixedFramedBankSnapshotBits.atKey P D H key).count→Fin N)
    (word:List Bool→List Bool):
    polynomial (ofSnapshot P D H key N column) ((IntegralMixedFramedBankTermBits.source word).syntax key)=
      MvPolynomial.rename column (IntegralMixedFramedBankTermBits.polynomial P D H word key):=by
  have Hn:=funext (numerator_snapshot P D H key N column)
  have Hd:=funext (denominator_snapshot P D H key N column)
  unfold ofSnapshot at Hn Hd
  unfold polynomial ofSnapshot
  rw [Hn,Hd,←CoefficientIndexedRationalClearing.term_rename,CoefficientIndexedRationalClearing.term_int]
  rfl

end LeanCanny.Algebra.CoefficientBankTermQuery
