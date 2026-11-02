/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankTermReaders
public import LeanCanny.Algebra.MvIndexedRationalClearing
/-! # The actual cleared original term on one joint bank tuple

The polynomial uses the literal original monomial expansion. Every source
variable is reversed into the same newest-first bank, with zero extension.
Encoding it gives exactly the native rational-substitution polynomial.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankTermBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical

theorem arity_eq_size (word : List Bool → List Bool) (key : List Bool) :
    Nat.fromBitsLE ((source word).arity key)=size word key := by
  simp only [source,ETR.RationalSubstitutionBits.Source.ofTerm,ETR.TermView.normalize_eq_term,Data.length_toBits,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,size,ETR.RationalSubstitutionBits.Source.syntax]

noncomputable def numeratorPolynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : ℕ) : MvPolynomial (Fin (atKey P D H key).count) ℤ :=
  if hi : i<(atKey P D H key).count then
    MvPolynomial.C ((atKey P D H key).cofactor (reverseIndex P D H key i))*
      MvPolynomial.X ⟨reverseIndex P D H key i,reverse_lt P D H key i hi⟩^
        UniformIntegralPowerSchedule.birth (P.cap (pairFst key)+1) (2^P.width (pairFst key)) i
  else 0
noncomputable def denominatorPolynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (_i : ℕ) : MvPolynomial (Fin (atKey P D H key).count) ℤ :=
  MvPolynomial.C ((atKey P D H key).common)

theorem numerator_encode (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (key : List Bool) (i : ℕ) :
    FixedWidthKronecker.encode (atKey P D H key).count (width P D H word key) (numeratorPolynomial P D H key i)=
      numerator P D H word key i := by
  unfold numeratorPolynomial numerator
  split_ifs
  · rw [map_mul,map_pow]
    simp only [FixedWidthKronecker.encode,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_C,MvPolynomial.eval₂_X]
    rw [← pow_mul,Polynomial.C_mul_X_pow_eq_monomial,Nat.mul_comm (2^_)]
  · exact map_zero _

theorem denominator_encode (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (key : List Bool) (i : ℕ) :
    FixedWidthKronecker.encode (atKey P D H key).count (width P D H word key) (denominatorPolynomial P D H key i)=
      denominator P D H key i := by
  simp only [denominatorPolynomial,denominator,FixedWidthKronecker.encode,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_C]

noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (key : List Bool) : MvPolynomial (Fin (atKey P D H key).count) ℤ :=
  MvIndexedRationalClearing.cleared (size word key) ((source word).syntax key).monomialCount (2*size word key)
    ((source word).syntax key).monomialCoefficient ((source word).syntax key).monomialExponent
    (numeratorPolynomial P D H key) (denominatorPolynomial P D H key)

theorem polynomial_encode (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (key : List Bool) :
    FixedWidthKronecker.encode (atKey P D H key).count (width P D H word key) (polynomial P D H word key)=
      (coordinates P D H word).family.polynomial key := by
  unfold polynomial
  rw [MvIndexedRationalClearing.encode]
  simp only [numerator_encode,denominator_encode]
  unfold ETR.RationalSubstitutionBits.Coordinates.family ETR.RationalSubstitutionBits.Source.family
    RationalSubstitution.IntegerBits.Family.polynomial
  dsimp only [coordinates]
  rw [arity_eq_size]
  rfl

theorem numerator_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : ℕ) : (numeratorPolynomial P D H key i).totalDegree≤maxPower P D H key := by
  unfold numeratorPolynomial
  split_ifs with hi
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X_pow,Nat.zero_add]
    exact MonicParameterPowerSchedule.weight_mono _ _ (by omega : i≤(atKey P D H key).count-1)
  · simp

theorem denominator_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (i : ℕ) : (denominatorPolynomial P D H key i).totalDegree≤maxPower P D H key := by
  rw [denominatorPolynomial,MvPolynomial.totalDegree_C]
  exact Nat.zero_le _

theorem exponent_le (word : List Bool → List Bool) (key : List Bool) (r i : ℕ) :
    ((source word).syntax key).monomialExponent r i≤2*size word key := by
  have HE := ((source word).syntax key).monomialExponent_le r i
  have HD := ((source word).syntax key).degreeBound_le_dataSize
  change ((source word).syntax key).monomialExponent r i≤2*((source word).syntax key).toData.size
  omega

theorem polynomial_degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (key : List Bool) :
    (polynomial P D H word key).totalDegree≤degree P D H word key :=
  MvIndexedRationalClearing.totalDegree _ _ _ _ _ _ _ _ (fun r _ i _ => exponent_le word key r i)
    (fun i _ => numerator_degree P D H key i) (fun i _ => denominator_degree P D H key i)

end LeanCanny.Algebra.IntegralMixedFramedBankTermBits
