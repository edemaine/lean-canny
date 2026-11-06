/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily
public import LeanCanny.Algebra.FixedWidthTarskiAffineMass
/-! # Charged actual radius-window principal masses -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily
open LeanCanny.Algebra LeanCanny.Computation Polynomial MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance radiusTarskiMassArityNeZero (c:List Bool):NeZero (arity c):=⟨by unfold arity;omega⟩

noncomputable def headInputMass (c:List Bool):=
  FormulaSignSlotRadialCenterCoefficient.massBudget (pairFst (original c))
noncomputable def massBudget (c:List Bool):=
  FixedWidthTarskiMass.principalMass (degree c) (seedDegree c) (bound c) (inputBound c) 4 (headInputMass c) 2

theorem headInputMass_binary :BinaryFn headInputMass:=FormulaSignSlotRadialCenterCoefficient.massBudget_binary.comp
  (mem_FP_comp original_FP pairFst_mem_FP)
theorem massBudget_binary :BinaryFn massBudget:=FixedWidthTarskiMass.principalMass_binary
  degree_binary seedDegree_binary bound_binary inputBound_binary (BinaryFn.const 4) headInputMass_binary (BinaryFn.const 2)

theorem head_coefficient_mass (c:List Bool) (i:ℕ) :MvMass.mass ((head c).coeff i)≤2^headInputMass c:=by
  rw [head,Polynomial.coeff_map]
  apply (MvMass.rename_le _ _).trans
  have HM:=FormulaSignSlotRadialCenterCoefficient.mass (pairFst (original c))
    (Nat.fromBitsLE (FormulaSignSlotRadialRadiusHeadReader.tau (original c)))
    (Nat.fromBitsLE (FormulaSignSlotRadialRadiusHeadReader.eta (original c))) i
  rw [←FormulaSignSlotRadialRadiusHeadEvaluation.coefficient] at HM
  exact HM

private theorem window_monomials (c:List Bool) :window c=
    Polynomial.monomial 1 (MvPolynomial.X (0:Fin (arity c)))-Polynomial.monomial 2 1:=by
  simp only [window,←Polynomial.C_mul_X_pow_eq_monomial,pow_one,Polynomial.C_1]
  ring
private theorem window_square_monomials (c:List Bool) :(window c)^2=
    Polynomial.monomial 2 ((MvPolynomial.X (0:Fin (arity c)))^2)-
      Polynomial.monomial 3 (MvPolynomial.C 2*MvPolynomial.X (0:Fin (arity c)))+
        Polynomial.monomial 4 1:=by
  simp only [window,←Polynomial.C_mul_X_pow_eq_monomial,map_pow,map_mul,map_ofNat,map_one]
  ring

private theorem window_coefficient_mass (c:List Bool) (i:ℕ) :MvMass.mass ((window c).coeff i)≤2:=by
  rw [window_monomials,Polynomial.coeff_sub,Polynomial.coeff_monomial,Polynomial.coeff_monomial]
  apply (MvMass.sub_le _ _).trans
  have HA:MvMass.mass (if 1=i then MvPolynomial.X (0:Fin (arity c)) else 0)≤1:=by split_ifs <;> simp
  have HB:MvMass.mass (if 2=i then (1:MvPolynomial (Fin (arity c)) ℤ) else 0)≤1:=by split_ifs <;> simp
  exact Nat.add_le_add HA HB

private theorem window_square_coefficient_mass (c:List Bool) (i:ℕ) :MvMass.mass (((window c)^2).coeff i)≤4:=by
  rw [window_square_monomials,Polynomial.coeff_add,Polynomial.coeff_sub,
    Polynomial.coeff_monomial,Polynomial.coeff_monomial,Polynomial.coeff_monomial]
  apply (MvMass.add_le _ _).trans
  apply (Nat.add_le_add_right (MvMass.sub_le _ _) _).trans
  have HA:MvMass.mass (if 2=i then (MvPolynomial.X (0:Fin (arity c)))^2 else 0)≤1:=by
    split_ifs
    · simpa only [MvMass.X,one_pow] using MvMass.pow_le (MvPolynomial.X (0:Fin (arity c))) 2
    · simp
  have HB:MvMass.mass (if 3=i then MvPolynomial.C 2*MvPolynomial.X (0:Fin (arity c)) else 0)≤2:=by
    split_ifs
    · apply (MvMass.mul_le _ _).trans
      rw [MvMass.C,MvMass.X]
      decide
    · simp
  have HC:MvMass.mass (if 4=i then (1:MvPolynomial (Fin (arity c)) ℤ) else 0)≤1:=by split_ifs <;> simp
  omega

theorem query_coefficient_mass (c:List Bool) (i:ℕ):MvMass.mass ((query c).coeff i)≤2^2:=by
  unfold query moment
  split_ifs
  · simpa only [pow_one] using (window_coefficient_mass c i).trans (by decide:2≤2^2)
  · exact window_square_coefficient_mass c i

theorem polynomial_mass (c:List Bool) (j:ℕ):
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial family c j)≤2^massBudget c:=
  FixedWidthTarskiMass.principal_mass_direct family c j (inputBound c) 4 (headInputMass c) 2
    (head_degree c) (query_degree c) (head_coefficient_mass c) (query_coefficient_mass c)

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiFamily
