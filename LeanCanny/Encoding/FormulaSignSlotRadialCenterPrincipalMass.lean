/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalFamily
public import LeanCanny.Algebra.FixedWidthTarskiMass
/-! # Original integer bounds for actual retained-center principal tests -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalMass
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial PrincipalSubresultant
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotRadialCenterPrincipalFamily
open scoped Classical
set_option backward.isDefEq.respectTransparency false

local instance centerPrincipalMassArityNeZero (c : List Bool) : NeZero (arity c) :=
  ⟨by unfold arity; omega⟩

noncomputable def inputMass (c : List Bool) := arity c * width c + FormulaSignSlotRadialEliminantFormalMass.budget (original c)
noncomputable def derivativeMass (c : List Bool) := (degree c).size + inputMass c + (degree c + 1).size
noncomputable def budget (c : List Bool) := arity c * width c + parameterMassBound (2 * degree c) (derivativeMass c)

theorem inputMass_binary : BinaryFn inputMass :=
  (BinaryFn.ofUnary (arity_unary.mul width_unary)).add (FormulaSignSlotRadialEliminantFormalMass.budget_binary.comp original_FP)
theorem derivativeMass_binary : BinaryFn derivativeMass :=
  (degree_binary.size.add inputMass_binary).add ((degree_binary.add (BinaryFn.const 1)).size)
theorem budget_binary : BinaryFn budget := by
  have H := (BinaryFn.const 2).mul degree_binary
  exact (BinaryFn.ofUnary (arity_unary.mul width_unary)).add
    (((H.size.mul H).add (H.mul derivativeMass_binary)).add derivativeMass_binary)

theorem input_mass (c : List Bool) (j : ℕ) : MvMass.mass ((polynomial c).coeff j) ≤ 2 ^ inputMass c := by
  apply PhysicalCriticalMassBudget.coefficient_box
  · intro e he i
    exact ((MvPolynomial.monomial_le_degreeOf i he).trans ((MvPolynomial.degreeOf_le_totalDegree _ i).trans
      (polynomial_degree c j))).trans_lt (input_fit c)
  · intro e
    dsimp only [arity] at e
    have HC := coefficient c j (e 0) e.tail
    simp only [Finsupp.cons_tail] at HC
    change (((polynomial c).coeff j).coeff e).natAbs ≤ _
    rw [HC]
    split_ifs
    · exact FormulaSignSlotRadialEliminantFormalMass.nested_abs (original c) (tau c) j (e 0) e.tail
    · exact Nat.zero_le _

noncomputable def encoded (c : List Bool) := FixedWidthBivariateReader.polynomial arity width polynomial c

theorem encoded_degree (c : List Bool) : (encoded c).natDegree ≤ degree c :=
  Polynomial.natDegree_map_le.trans (Polynomial.natDegree_map_le.trans
    (FormulaSignSlotRadialCenterSquarefreeSelection.truncate_degree _ _))

theorem encoded_coefficient_mass (c : List Bool) (j : ℕ) : coefficientMass ((encoded c).coeff j) ≤ 2 ^ inputMass c := by
  rw [encoded, FixedWidthBivariateReader.polynomial, Polynomial.coeff_map]
  exact (FixedWidthTarskiMass.encode_mass_le _ _ _).trans (input_mass c j)

theorem encoded_derivative_mass (c : List Bool) (j : ℕ) :
    coefficientMass ((encoded c).derivative.coeff j) ≤ 2 ^ derivativeMass c := by
  apply (NestedMass.coeff_le _ j).trans
  apply (NestedMass.derivative_le _).trans
  apply (Nat.mul_le_mul (encoded_degree c)
    (NestedMass.le_pow _ _ _ (encoded_degree c) (encoded_coefficient_mass c))).trans
  apply (Nat.mul_le_mul_right _ (Nat.lt_size_self (degree c)).le).trans
  rw [← pow_add]
  simp only [derivativeMass, Nat.add_assoc, le_refl]

theorem mass (c : List Bool) (j : ℕ) : MvMass.mass (principal c j) ≤ 2 ^ budget c := by
  apply FixedWidthTarskiMass.mass_le_pow
  · intro e he i
    exact ((MvPolynomial.monomial_le_degreeOf i he).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt
      (principal_fit c j)
  · have HE : FixedWidthKronecker.encode (arity c) (width c) (principal c j) =
        signedPsc (encoded c) (encoded c).derivative (degree c) (degree c - 1) j := by
      rw [principal, ← signedPsc_map_map, ← Polynomial.derivative_map]
      rfl
    rw [HE]
    apply signedPsc_mass_le _ _ _ _ _ (2 * degree c) _ (by omega)
    · intro i
      exact (encoded_coefficient_mass c i).trans (Nat.pow_le_pow_right (by decide) (by unfold derivativeMass; omega))
    · exact encoded_derivative_mass c

end LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalMass
