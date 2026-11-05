/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCut
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalMass
/-! # Original integer degree and mass for the actual branch cut

Radius and all center variables remain formal. The larger output box accounts
for the full selected-principal power, rather than wrapping an old PSC box.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutFamily
open LeanCanny.Algebra LeanCanny.Computation Polynomial PrincipalSubresultant
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def degreeBound (c : List Bool) := 2 * FormulaSignSlotRadialCenterPrincipalFamily.inputBound c + (FormulaSignSlotRadialCenterPrincipalFamily.degree c + 1) * FormulaSignSlotRadialCenterPrincipalFamily.degreeBound c
noncomputable def width (c : List Bool) := (degreeBound c).size
noncomputable def massBound (c : List Bool) := 2 * FormulaSignSlotRadialCenterPrincipalMass.inputMass c + (FormulaSignSlotRadialCenterPrincipalFamily.degree c + 1) * FormulaSignSlotRadialCenterPrincipalMass.budget c

theorem degreeBound_binary : BinaryFn degreeBound :=
  ((BinaryFn.const 2).mul FormulaSignSlotRadialCenterPrincipalFamily.inputBound_binary).add
    ((FormulaSignSlotRadialCenterPrincipalFamily.degree_binary.add (BinaryFn.const 1)).mul FormulaSignSlotRadialCenterPrincipalFamily.degreeBound_binary)
theorem width_unary : UnaryFn width :=
  (UnaryFn.length degreeBound_binary.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
theorem massBound_binary : BinaryFn massBound :=
  ((BinaryFn.const 2).mul FormulaSignSlotRadialCenterPrincipalMass.inputMass_binary).add
    ((FormulaSignSlotRadialCenterPrincipalFamily.degree_binary.add (BinaryFn.const 1)).mul FormulaSignSlotRadialCenterPrincipalMass.budget_binary)

noncomputable def principal (c : List Bool) (k : ℕ) :=
  psc (FormulaSignSlotRadialCenterPrincipalFamily.polynomial c) (FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).derivative (FormulaSignSlotRadialCenterPrincipalFamily.degree c) (FormulaSignSlotRadialCenterPrincipalFamily.degree c - 1) k
noncomputable def polynomial (c : List Bool) (k : ℕ) : MvPolynomial (Fin (FormulaSignSlotRadialCenterPrincipalFamily.arity c)) ℤ :=
  if FormulaSignSlotRadialCenterPrincipalFamily.degree c = 0 then (FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).coeff 0 else if k < FormulaSignSlotRadialCenterPrincipalFamily.degree c then
    (FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).coeff (FormulaSignSlotRadialCenterPrincipalFamily.degree c) ^ 2 * principal c k ^ (FormulaSignSlotRadialCenterPrincipalFamily.degree c - k + 1) else 0

private theorem principal_eq (c : List Bool) (k : ℕ) (hk : k < FormulaSignSlotRadialCenterPrincipalFamily.degree c) :
    principal c k = (-1) ^ (FormulaSignSlotRadialCenterPrincipalFamily.degree c - k).choose 2 * FormulaSignSlotRadialCenterPrincipalFamily.principal c k := by
  rw [FormulaSignSlotRadialCenterPrincipalFamily.principal, signedPsc_of_le _ _ (by omega)]
  change _ = (-1) ^ _ * ((-1) ^ _ * principal c k)
  rw [← mul_assoc, ← mul_pow]
  simp

private theorem sign_degree (c : List Bool) (j : ℕ) :
    ((-1 : MvPolynomial (Fin (FormulaSignSlotRadialCenterPrincipalFamily.arity c)) ℤ) ^ j).totalDegree = 0 := by
  have H : (-1 : MvPolynomial (Fin (FormulaSignSlotRadialCenterPrincipalFamily.arity c)) ℤ) = MvPolynomial.C (-1 : ℤ) := by simp
  rw [H, ← map_pow, MvPolynomial.totalDegree_C]
private theorem sign_mass (c : List Bool) (j : ℕ) :
    MvMass.mass ((-1 : MvPolynomial (Fin (FormulaSignSlotRadialCenterPrincipalFamily.arity c)) ℤ) ^ j) = 1 := by
  have H : (-1 : MvPolynomial (Fin (FormulaSignSlotRadialCenterPrincipalFamily.arity c)) ℤ) = MvPolynomial.C (-1 : ℤ) := by simp
  rw [H, ← map_pow, MvMass.C, Int.natAbs_pow]
  simp

theorem principal_degree (c : List Bool) (k : ℕ) (hk : k < FormulaSignSlotRadialCenterPrincipalFamily.degree c) :
    (principal c k).totalDegree ≤ FormulaSignSlotRadialCenterPrincipalFamily.degreeBound c := by
  rw [principal_eq c k hk]
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    rw [sign_degree, Nat.zero_add]; exact FormulaSignSlotRadialCenterPrincipalFamily.principal_degree c k)
theorem principal_mass (c : List Bool) (k : ℕ) (hk : k < FormulaSignSlotRadialCenterPrincipalFamily.degree c) :
    MvMass.mass (principal c k) ≤ 2 ^ FormulaSignSlotRadialCenterPrincipalMass.budget c := by
  rw [principal_eq c k hk]
  exact (MvMass.mul_le _ _).trans (by rw [sign_mass, Nat.one_mul]; exact FormulaSignSlotRadialCenterPrincipalMass.mass c k)

theorem input_fit (c : List Bool) : FormulaSignSlotRadialCenterPrincipalFamily.inputBound c < 2 ^ width c := by
  exact (by unfold degreeBound; omega : FormulaSignSlotRadialCenterPrincipalFamily.inputBound c ≤ degreeBound c).trans_lt (Nat.lt_size_self _)

theorem polynomial_degree (c : List Bool) (k : ℕ) :
    (polynomial c k).totalDegree ≤ degreeBound c := by
  rw [polynomial]
  split_ifs with HZ HK
  · exact (FormulaSignSlotRadialCenterPrincipalFamily.polynomial_degree c 0).trans (by unfold degreeBound; omega)
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    have HL := (MvPolynomial.totalDegree_pow ((FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).coeff (FormulaSignSlotRadialCenterPrincipalFamily.degree c)) 2).trans
      (Nat.mul_le_mul_left 2 (FormulaSignSlotRadialCenterPrincipalFamily.polynomial_degree c (FormulaSignSlotRadialCenterPrincipalFamily.degree c)))
    have HP := (MvPolynomial.totalDegree_pow (principal c k) (FormulaSignSlotRadialCenterPrincipalFamily.degree c - k + 1)).trans
      (Nat.mul_le_mul_left _ (principal_degree c k HK))
    exact (Nat.add_le_add HL HP).trans (by
      unfold degreeBound
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _)
  · simp

theorem polynomial_mass (c : List Bool) (k : ℕ) :
    MvMass.mass (polynomial c k) ≤ 2 ^ massBound c := by
  rw [polynomial]
  split_ifs with HZ HK
  · exact (FormulaSignSlotRadialCenterPrincipalMass.input_mass c 0).trans (Nat.pow_le_pow_right (by decide) (by unfold massBound; omega))
  · apply (MvMass.mul_le _ _).trans
    have HL := (MvMass.pow_le ((FormulaSignSlotRadialCenterPrincipalFamily.polynomial c).coeff (FormulaSignSlotRadialCenterPrincipalFamily.degree c)) 2).trans
      (Nat.pow_le_pow_left (FormulaSignSlotRadialCenterPrincipalMass.input_mass c (FormulaSignSlotRadialCenterPrincipalFamily.degree c)) 2)
    have HP := (MvMass.pow_le (principal c k) (FormulaSignSlotRadialCenterPrincipalFamily.degree c - k + 1)).trans
      (Nat.pow_le_pow_left (principal_mass c k HK) _)
    apply (Nat.mul_le_mul HL HP).trans
    rw [← pow_mul, ← pow_mul, ← pow_add]
    apply Nat.pow_le_pow_right (by decide)
    unfold massBound
    nlinarith [Nat.sub_le (FormulaSignSlotRadialCenterPrincipalFamily.degree c) k]
  · simp

theorem polynomial_map (c : List Bool) (k : ℕ) : polynomial c k =
    TriplePolynomialParameterFlatten.one (FormulaSignSlotRadialCenterBranchCut.polynomial
      (FormulaSignSlotRadialCenterPrincipalFamily.original c) (FormulaSignSlotRadialCenterPrincipalFamily.tau c) (FormulaSignSlotRadialCenterPrincipalFamily.degree c) k) := by
  dsimp only [FormulaSignSlotRadialCenterPrincipalFamily.arity]
  rw [polynomial, FormulaSignSlotRadialCenterBranchCut.polynomial]
  split_ifs
  · rw [← Polynomial.coeff_map]; rfl
  · rw [map_mul, map_pow, map_pow, principal,
      FormulaSignSlotRadialCenterSquarefreeSelection.principal]
    simp only [FormulaSignSlotRadialCenterPrincipalFamily.polynomial, Polynomial.coeff_map,
      Polynomial.derivative_map, psc_map_map]
    rfl
  · rw [map_zero]

end LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutFamily
