/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicSource
public import LeanCanny.Algebra.IntegralMixedBankCoordinateBounds
/-! # Degree and mass of the literal old-coordinate characteristic source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask Polynomial
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] matrix count dimension IntegralMixedFramedOldHeightBankBits.sourceEntry

theorem common_ne_zero (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
    common P D H c ≠ 0 := IntegralMixedHistory.commonDenominator_ne_zero ((family P D H).state (key c))

theorem degree (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
    (polynomial P D H c).natDegree=dimension P D H c := by
  rw [polynomial,ScaledGradedReductionAnnihilator.polynomial,pow_one,Polynomial.natDegree_comp,
    Matrix.charpoly_natDegree_eq_dim,Polynomial.natDegree_C_mul_X _ (common_ne_zero P D H c),Nat.mul_one]
  exact Fintype.card_fin _

theorem leading (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
    (polynomial P D H c).leadingCoeff=common P D H c^dimension P D H c := by
  have HD : (Polynomial.C (common P D H c)*Polynomial.X).natDegree≠0 := by
    rw [Polynomial.natDegree_C_mul_X _ (common_ne_zero P D H c)]
    decide
  rw [polynomial,ScaledGradedReductionAnnihilator.polynomial,pow_one,Polynomial.leadingCoeff_comp HD,
    (Matrix.charpoly_monic (matrix P D H c)).leadingCoeff,one_mul,
    Polynomial.leadingCoeff_C_mul_X,Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin]

theorem nonzero (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
    polynomial P D H c ≠ 0 := by
  intro h
  have HH := congrArg Polynomial.leadingCoeff h
  rw [leading,Polynomial.leadingCoeff_zero] at HH
  exact pow_ne_zero _ (common_ne_zero P D H c) HH

theorem common_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (G : ℕ) (HG : ((family P D H).state (key c)).bank.Bounds G) :
    (common P D H c).natAbs≤2^(count P D H c*G) :=
  by simpa only [common,count] using IntegralMixedBankCoordinatePolynomial.common_bound ((family P D H).state (key c)) HG

theorem matrix_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (G : ℕ) (HG : ((family P D H).state (key c)).bank.Bounds G)
    (r t : Fin (dimension P D H c)) : (matrix P D H c r t).natAbs≤2^(G+count P D H c*G) := by
  rw [matrix]
  split_ifs with ha
  · unfold IntegralMixedFramedOldHeightBankBits.sourceEntry
    split_ifs with hv
    · simpa only [IntegralMixedBankCoordinatePolynomial.matrix,count] using IntegralMixedBankCoordinatePolynomial.matrix_bound ((family P D H).state (key c)) HG
        ⟨min (index c) (count P D H c),hv.1⟩ ⟨r.val,hv.2.1⟩ ⟨t.val,hv.2.2⟩
    · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem coefficient_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (G : ℕ) (HG : ((family P D H).state (key c)).bank.Bounds G) (k : ℕ) :
    ((polynomial P D H c).coeff k).natAbs≤2^(CharacteristicIntegerBounds.budget (dimension P D H c)
      (G+count P D H c*G)+count P D H c*G*dimension P D H c) := by
  by_cases hk : k≤dimension P D H c
  · have HC := (Nat.lt_size_self ((matrix P D H c).charpoly.coeff k).natAbs).le.trans
      (Nat.pow_le_pow_right (by decide) (CharacteristicIntegerBounds.coefficient_bits
        (matrix P D H c) (G+count P D H c*G) (matrix_bound P D H c G HG) k))
    rw [polynomial,ScaledGradedReductionAnnihilator.coefficient,Nat.one_mul,Int.natAbs_mul,Int.natAbs_pow]
    calc
      _ ≤ 2^CharacteristicIntegerBounds.budget (dimension P D H c) (G+count P D H c*G)*
          (2^(count P D H c*G))^k := Nat.mul_le_mul HC (Nat.pow_le_pow_left (common_bound P D H c G HG) k)
      _ = 2^(CharacteristicIntegerBounds.budget (dimension P D H c) (G+count P D H c*G)+count P D H c*G*k) := by
        rw [←pow_mul,←pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_left (count P D H c*G) hk) _)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [degree]; omega),Int.natAbs_zero]
    exact Nat.zero_le _

noncomputable def massBound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (c : List Bool) :=
  IntegralMixedBankCoordinatePolynomial.massBudget (count P D H c) ((family P D H).width (key c))
    (IntegralMixedFramedStepHeight.familyHeight P L F C (key c))

theorem massBound_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {L F C : List Bool → ℕ} (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : BinaryFn (massBound P D H L F C) :=
  IntegralMixedBankCoordinatePolynomial.massBudget_binary (count_unary P a D H)
    (a.width.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))
    ((IntegralMixedFramedStepHeight.familyHeight_binary P a hL hF hC).comp pairFst_mem_FP)

theorem polynomial_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (c : List Bool) :
    coefficientMass (polynomial P D H c)≤2^massBound P D H L F C c := by
  let G := IntegralMixedFramedStepHeight.familyHeight P L F C (key c)
  have HG := IntegralMixedFramedStepHeight.family_bank_bounds P D H L F C hs (key c)
  have HC := coefficientMass_le (polynomial P D H c) (dimension P D H c)
    (2^(CharacteristicIntegerBounds.budget (dimension P D H c) (G+count P D H c*G)+count P D H c*G*dimension P D H c))
    (degree P D H c).le (coefficient_bound P D H c G HG)
  have HR : dimension P D H c+1≤2^(dimension P D H c).size := by
    have HH := Nat.lt_size_self (dimension P D H c)
    omega
  apply HC.trans
  have HD : FixedWidthPolynomial.count (count P D H c) ((family P D H).width (key c))=dimension P D H c := by rw [dimension]
  simp only [massBound,IntegralMixedBankCoordinatePolynomial.massBudget,IntegralMixedBankCoordinatePolynomial.coefficientBudget,HD]
  change _ ≤ 2^((dimension P D H c).size+
    (CharacteristicIntegerBounds.budget (dimension P D H c) (G+count P D H c*G)+count P D H c*G*dimension P D H c))
  simpa only [pow_add,mul_assoc] using Nat.mul_le_mul_right
    (2^(CharacteristicIntegerBounds.budget (dimension P D H c) (G+count P D H c*G)+count P D H c*G*dimension P D H c)) HR

end LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
