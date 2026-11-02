/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankTermBounds
public import LeanCanny.Algebra.FixedWidthCommonDenominatorSpace
/-! # Native dense coefficients of the actual joint-bank original-term test

Repacking preserves every selected exponent while removing unused high rank
bits. Thus the total coefficient reader agrees with the dense polynomial
definition even on malformed coefficient-rank words.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
attribute [local irreducible] polynomial

noncomputable def coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (q : List Bool) :=
  let key := RationalSubstitution.IntegerBits.context q
  residueBits (((polynomial P D H word key).coeff
    (nativeExponent (Equiv.refl (Fin (atKey P D H key).count)) (width P D H word key)
      (Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree q))) : ℤ) : ZMod (RationalSubstitution.IntegerBits.mValue q))

theorem coefficient_std (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (key rankWord modulusWord : List Bool) :
    coefficient P D H word (pair (pair key rankWord) modulusWord)=
      residueBits (((polynomial P D H word key).coeff
        (nativeExponent (Equiv.refl (Fin (atKey P D H key).count)) (width P D H word key) (Nat.fromBitsLE rankWord)) : ℤ) :
          ZMod (Nat.fromBitsLE modulusWord+1)) := by
  generalize hz : pair (pair key rankWord) modulusWord=q
  have HC : RationalSubstitution.IntegerBits.context q=key := by rw [←hz,RationalSubstitution.IntegerBits.context,pairFst_pair,pairFst_pair]
  have HR : RationalSubstitution.IntegerBits.selectedDegree q=rankWord := by rw [←hz,RationalSubstitution.IntegerBits.selectedDegree,pairFst_pair,pairSnd_pair]
  have HM : pairSnd q=modulusWord := by rw [←hz,pairSnd_pair]
  subst key
  subst rankWord
  subst modulusWord
  rfl

noncomputable def rankCode (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) :=
  FixedWidthQuery.repack (fun q => (atKey P D H (RationalSubstitution.IntegerBits.context q)).count)
    (fun q => width P D H word (RationalSubstitution.IntegerBits.context q))
    (fun q => (atKey P D H (RationalSubstitution.IntegerBits.context q)).count)
    (fun q => width P D H word (RationalSubstitution.IntegerBits.context q)) RationalSubstitution.IntegerBits.selectedDegree

theorem rankCode_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (hw : word∈FP) : rankCode P D H word∈FP :=
  FixedWidthQuery.repack_mem_FP
    ((IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp RationalSubstitution.IntegerBits.context_mem_FP)
    ((width_unary P a D H word hw).comp RationalSubstitution.IntegerBits.context_mem_FP)
    ((IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp RationalSubstitution.IntegerBits.context_mem_FP)
    ((width_unary P a D H word hw).comp RationalSubstitution.IntegerBits.context_mem_FP)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP

noncomputable def coefficientQuery (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (q : List Bool) :=
  pair (pair (RationalSubstitution.IntegerBits.context q) (rankCode P D H word q)) (pairSnd q)
theorem coefficientQuery_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (hw : word∈FP) : coefficientQuery P D H word∈FP :=
  mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP (rankCode_FP P a D H word hw)) pairSnd_mem_FP

theorem coefficient_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (q : List Bool) :
    PrimitivePairBits.coefficient (coordinates P D H word).family.polynomial (coefficientQuery P D H word q)=
      coefficient P D H word q := by
  let key := RationalSubstitution.IntegerBits.context q
  let A := (atKey P D H key).count
  let W := width P D H word key
  let r := Nat.fromBitsLE (rankCode P D H word q)
  have HR : r<count A W := by
    have HT := Nat.fromBitsLE_lt_pow_length (rankCode P D H word q)
    rw [rankCode,FixedWidthQuery.repack_length] at HT
    simpa only [r,A,W,key,rankCode,count,← pow_mul,Nat.mul_comm] using HT
  have HV : vector A W ⟨r,HR⟩=nativeExponent (Equiv.refl (Fin A)) W
      (Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree q)) := by
    calc
      _ = nativeExponent (Equiv.refl (Fin A)) W r := ((nativeExponent_refl _ _ _).trans (entry_vector _ _ ⟨r,HR⟩)).symm
      _ = _ := nativeExponent_repack (Equiv.refl (Fin A))
        (fun z => width P D H word (RationalSubstitution.IntegerBits.context z))
        (fun z => width P D H word (RationalSubstitution.IntegerBits.context z))
        RationalSubstitution.IntegerBits.selectedDegree q le_rfl
  have HF : ∀ e ∈ (polynomial P D H word key).support,∀ i,e i<2^W := by
    intro e he i
    exact ((MvPolynomial.monomial_le_degreeOf i he).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt
      ((polynomial_degree P D H word key).trans_lt (Nat.lt_size_self _))
  have HC := FixedWidthKronecker.coefficient A W (polynomial P D H word key) HF ⟨r,HR⟩
  rw [polynomial_encode P D H word key,HV] at HC
  unfold coefficientQuery
  rw [FixedWidthCommonDenominatorBits.primitive_packet]
  exact congrArg (fun a : ℤ => residueBits (a : ZMod (RationalSubstitution.IntegerBits.mValue q))) HC

theorem coefficient_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed)
    (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
    (word : List Bool → List Bool) (hw : word∈FP) : SpaceFunction (coefficient P D H word) := by
  have E := encoded_evaluator P a D H s hs hF hL word hw
  have EP : SpaceFunction (PrimitivePairBits.coefficient (coordinates P D H word).family.polynomial) :=
    E.congr (funext fun _ => rfl)
  exact (EP.precompose _ (coefficientQuery_FP P a D H word hw)).congr (funext fun q => coefficient_packet P D H word q)

end LeanCanny.Algebra.IntegralMixedFramedBankTermBits
