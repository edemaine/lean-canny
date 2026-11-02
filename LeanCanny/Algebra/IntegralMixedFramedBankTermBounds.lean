/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankTermPolynomial
/-! # Original syntax bounds the actual joint-bank term test

The old bank height is derived from the complete literal script and its
default instruction. Common-denominator products change coefficient mass,
while the fixed joint power schedule controls variable degree.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankTermBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (Snapshot atKey)
open scoped Classical BigOperators

theorem snapshot_common_bound (s : Snapshot) (G : ℕ) (h : ∀ i,(s.denominator i).natAbs≤2^G) :
    s.common.natAbs≤2^(s.count*G) := by
  simpa only [Snapshot.common,CommonIntegerDenominator.denominator,Finset.card_univ,Fintype.card_fin] using
    CommonIntegerDenominator.denominator_height Finset.univ s.denominator G (fun i _ => h i)

theorem snapshot_cofactor_bound (s : Snapshot) (G : ℕ) (h : ∀ i,(s.denominator i).natAbs≤2^G) (k : ℕ) :
    (s.cofactor k).natAbs≤2^(s.count*G) := by
  have HF : ∀ i : Fin s.count,(if i.val=k then (1 : ℤ) else s.denominator i).natAbs≤2^G := by
    intro i
    split_ifs
    · exact Nat.one_le_two_pow
    · exact h i
  simpa only [Snapshot.cofactor,CommonIntegerDenominator.denominator,Finset.card_univ,Fintype.card_fin] using
    CommonIntegerDenominator.denominator_height Finset.univ (fun i => if i.val=k then 1 else s.denominator i) G (fun i _ => HF i)

noncomputable def coordinateMass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) : ℕ :=
  (atKey P D H key).count*IntegralMixedFramedStepHeight.familyHeight P L F C key

theorem coordinateMass_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {L F C : List Bool → ℕ} (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (coordinateMass P D H L F C) :=
  (BinaryFn.ofUnary (IntegralMixedFramedBankSnapshotBits.count_unary P a D H)).mul
    (IntegralMixedFramedStepHeight.familyHeight_binary P a hL hF hC)

theorem numerator_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool) (i : ℕ) :
    MvMass.mass (numeratorPolynomial P D H key i)≤2^coordinateMass P D H L F C key := by
  have HB := IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C hs key
  have HC := snapshot_cofactor_bound (atKey P D H key) (IntegralMixedFramedStepHeight.familyHeight P L F C key)
    (fun j => HB.denominator j) (reverseIndex P D H key i)
  unfold numeratorPolynomial
  split_ifs with hi
  · rw [MvPolynomial.C_mul_X_pow_eq_monomial,MvMass.monomial]
    exact HC
  · simpa only [MvMass.zero] using Nat.zero_le (2^coordinateMass P D H L F C key)

theorem denominator_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool) (i : ℕ) :
    MvMass.mass (denominatorPolynomial P D H key i)≤2^coordinateMass P D H L F C key := by
  have HB := IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C hs key
  rw [denominatorPolynomial,MvMass.C]
  exact snapshot_common_bound (atKey P D H key) _ (fun j => HB.denominator j)

noncomputable def monomialSize (word : List Bool → List Bool) (key : List Bool) := ((source word).syntax key).monomialCount.size
theorem monomialSize_unary (word : List Bool → List Bool) (hw : word∈FP) : UnaryFn (monomialSize word) :=
  (UnaryFn.length ((source word).countCode_mem_FP (ETR.RationalSubstitutionBits.Source.ofTerm_polyTime (wordAt_FP word hw)))).of_eq
    (fun key => by rw [ETR.RationalSubstitutionBits.Source.countCode_eq,BinaryNatCode.length_encode]; rfl)

noncomputable def mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (L F C : List Bool → ℕ) (key : List Bool) :=
  monomialSize word key+size word key+size word key*(2*size word key)*coordinateMass P D H L F C key

theorem mass_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (hw : word∈FP) {L F C : List Bool → ℕ}
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (mass P D H word L F C) :=
  ((BinaryFn.ofUnary (monomialSize_unary word hw)).add (BinaryFn.ofUnary (size_unary word hw))).add
    (((BinaryFn.ofUnary (size_unary word hw)).mul ((BinaryFn.const 2).mul (BinaryFn.ofUnary (size_unary word hw)))).mul
      (coordinateMass_binary P a D H hL hF hC))

theorem polynomial_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (L F C : List Bool → ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool) :
    MvMass.mass (polynomial P D H word key)≤2^mass P D H word L F C key :=
  MvIndexedRationalClearing.mass _ _ _ _ _ _ _ _ _ (fun r _ i _ => exponent_le word key r i)
    (fun r _ => ((source word).syntax key).monomialCoefficient_natAbs_le_pow_dataSize r)
    (fun i _ => numerator_mass P D H L F C hs key i) (fun i _ => denominator_mass P D H L F C hs key i)

end LeanCanny.Algebra.IntegralMixedFramedBankTermBits
