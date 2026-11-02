/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankCoordinateSpace
public import LeanCanny.Algebra.MvCoefficientMass
/-! # Original-only degree and mass metadata for cleared bank coordinates -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankCoordinateBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankDenominatorBits (count count_unary index state)
open scoped Classical

noncomputable def massBound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (q : List Bool) : ℕ :=
  count P D H q*IntegralMixedFramedStepHeight.familyHeight P L F C (PaddedIntegralGeneratorSource.base q)

theorem massBound_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {L F C : List Bool → ℕ} (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :
    BinaryFn (massBound P D H L F C) :=
  (BinaryFn.ofUnary (count_unary P a D H)).mul
    ((IntegralMixedFramedStepHeight.familyHeight_binary P a hL hF hC).comp PaddedIntegralGeneratorSource.base_FP)

theorem polynomial_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (q : List Bool) :
    MvMass.mass (polynomial P D H q)≤2^massBound P D H L F C q := by
  unfold polynomial
  split_ifs with hi
  · let i : Fin (count P D H q) := ⟨index q,hi⟩
    have HC := IntegralMixedFramedBankProductBits.integer_cofactor P D H index q i rfl
    have HB := IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C hs (PaddedIntegralGeneratorSource.base q)
    have HH := CommonIntegerDenominator.denominator_height (Finset.univ.erase i) (state P D H q).bank.denominator
      (IntegralMixedFramedStepHeight.familyHeight P L F C (PaddedIntegralGeneratorSource.base q))
      (fun j _ => HB.denominator j)
    have HD : (IntegralMixedFramedBankProductBits.integer P D H index q).natAbs≤2^massBound P D H L F C q := by
      rw [HC]
      exact HH.trans (Nat.pow_le_pow_right (by decide)
        (Nat.mul_le_mul_right _ ((Finset.card_erase_le).trans_eq (by simp))))
    have HP : MvMass.mass ((MvPolynomial.X i : MvPolynomial (Fin (count P D H q)) ℤ)^weight P D H q)≤1 := by
      simpa only [MvMass.X,one_pow] using MvMass.pow_le (MvPolynomial.X i : MvPolynomial (Fin (count P D H q)) ℤ) (weight P D H q)
    have HE := (MvMass.mul_le (MvPolynomial.C (IntegralMixedFramedBankProductBits.integer P D H index q))
      ((MvPolynomial.X i : MvPolynomial (Fin (count P D H q)) ℤ)^weight P D H q)).trans
      (Nat.mul_le_mul_left _ HP)
    have HM : MvMass.mass (MvPolynomial.C (IntegralMixedFramedBankProductBits.integer P D H index q)*
        (MvPolynomial.X i : MvPolynomial (Fin (count P D H q)) ℤ)^weight P D H q)≤
        (IntegralMixedFramedBankProductBits.integer P D H index q).natAbs := by
      simpa only [MvMass.C,Nat.mul_one] using HE
    exact HM.trans HD
  · exact (by simp only [MvMass.zero]; exact Nat.zero_le _)

end LeanCanny.Algebra.IntegralMixedFramedBankCoordinateBits
