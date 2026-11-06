/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiFamily
/-! # Derived window-principal and seed mass from actual source mass -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialWindowTarski
open LeanCanny.Algebra LeanCanny.Computation Polynomial MvPolynomial MatrixPower FixedWidthPolynomial
open IntegralFramedBankPolynomialModel (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local instance windowTarskiMassArityNeZero (N:List Bool→ℕ) (c:List Bool):NeZero (arity N c):=⟨by unfold arity;omega⟩

noncomputable def seed (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool):=
  PseudoRemainder.seed (head S N hd c) (query N c) (degree S c) (bound S c)
noncomputable def seedCoefficientDegree (S:Source) (c:List Bool):=
  MultivariateTarskiDegreeBounds.seedDegreeBound (bound S c) (inputBound S c) 2
noncomputable def seedInputMass (S:Source) (c:List Bool):=
  FixedWidthTarskiMass.seedMass (bound S c) (inputBound S c) 4 (S.mass (original c)) 2
noncomputable def massBudget (S:Source) (c:List Bool):=
  FixedWidthTarskiMass.principalMass (degree S c) (seedDegree S c) (bound S c) (inputBound S c) 4 (S.mass (original c)) 2
noncomputable def selectionMass (S:Source) (c:List Bool):=S.mass (original c)+seedInputMass S c

theorem seedInputMass_binary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):BinaryFn (seedInputMass S):=
  FixedWidthTarskiMass.seedMass_binary (bound_binary S A) (inputBound_binary S A) (BinaryFn.const 4)
    (A.mass.comp FormulaSignSlotRadialRadiusTarskiFamily.original_FP) (BinaryFn.const 2)
theorem massBudget_binary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):BinaryFn (massBudget S):=
  FixedWidthTarskiMass.principalMass_binary (degree_binary S A) (seedDegree_binary S A) (bound_binary S A)
    (inputBound_binary S A) (BinaryFn.const 4) (A.mass.comp FormulaSignSlotRadialRadiusTarskiFamily.original_FP) (BinaryFn.const 2)
theorem selectionMass_binary (S:Source) (A:IntegralFramedBankPolynomialModel.Access S):BinaryFn (selectionMass S):=
  by
    have HH:BinaryFn (fun c=>S.mass (original c)):=A.mass.comp FormulaSignSlotRadialRadiusTarskiFamily.original_FP
    exact HH.add (seedInputMass_binary S A)

private theorem window_square (N:List Bool→ℕ) (c:List Bool):(window N c)^2=
    Polynomial.monomial 2 (MvPolynomial.X (0:Fin (arity N c))^2)-
      Polynomial.monomial 3 (MvPolynomial.C 2*MvPolynomial.X (0:Fin (arity N c)))+Polynomial.monomial 4 1:=by
  simp only [window,←Polynomial.C_mul_X_pow_eq_monomial,map_pow,map_mul,map_ofNat,map_one]
  ring
private theorem window_mass (N:List Bool→ℕ) (c:List Bool) (i:ℕ):MvMass.mass ((window N c).coeff i) ≤ 2:=by
  rw [window_monomials,Polynomial.coeff_sub,Polynomial.coeff_monomial,Polynomial.coeff_monomial]
  apply (MvMass.sub_le _ _).trans
  have HA:MvMass.mass (if 1=i then MvPolynomial.X (0:Fin (arity N c)) else 0) ≤ 1:=by split_ifs <;> simp
  have HB:MvMass.mass (if 2=i then (1:MvPolynomial (Fin (arity N c)) ℤ) else 0) ≤ 1:=by split_ifs <;> simp
  exact Nat.add_le_add HA HB
private theorem window_square_mass (N:List Bool→ℕ) (c:List Bool) (i:ℕ):MvMass.mass (((window N c)^2).coeff i) ≤ 4:=by
  rw [window_square,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_monomial,
    Polynomial.coeff_monomial,Polynomial.coeff_monomial]
  apply (MvMass.add_le _ _).trans
  apply (Nat.add_le_add_right (MvMass.sub_le _ _) _).trans
  have HA:MvMass.mass (if 2=i then MvPolynomial.X (0:Fin (arity N c))^2 else 0) ≤ 1:=by
    split_ifs
    · simpa only [MvMass.X,one_pow] using MvMass.pow_le (MvPolynomial.X (0:Fin (arity N c))) 2
    · simp
  have HB:MvMass.mass (if 3=i then MvPolynomial.C 2*MvPolynomial.X (0:Fin (arity N c)) else 0) ≤ 2:=by
    split_ifs
    · apply (MvMass.mul_le _ _).trans
      rw [MvMass.C,MvMass.X]
      decide
    · simp
  have HC:MvMass.mass (if 4=i then (1:MvPolynomial (Fin (arity N c)) ℤ) else 0) ≤ 1:=by split_ifs <;> simp
  omega

theorem query_coefficient_mass (N:List Bool→ℕ) (c:List Bool) (i:ℕ):MvMass.mass ((query N c).coeff i) ≤ 2^2:=by
  unfold query moment FormulaSignSlotRadialRadiusTarskiFamily.moment
  split_ifs
  · simpa only [pow_one] using (window_mass N c i).trans (by decide:2 ≤ 2^2)
  · exact window_square_mass N c i

theorem polynomial_mass (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool) (j:ℕ):
    MvMass.mass (FixedWidthTarskiPrincipalBits.polynomial (family S N hd) c j) ≤ 2^massBudget S c:=
  FixedWidthTarskiMass.principal_mass_direct (family S N hd) c j (inputBound S c) 4 (S.mass (original c)) 2
    (head_degree S N hd c) (query_degree N c) (head_coefficient_mass S N hd c) (query_coefficient_mass N c)

theorem seed_degree (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool):
    (seed S N hd c).natDegree < degree S c:=
  PseudoRemainder.seed_natDegree_lt _ _ _ _ ((family S N hd).degree_pos c) (input_degree S N hd c)
theorem seed_coefficient_degree (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool) (i:ℕ):
    ((seed S N hd c).coeff i).totalDegree ≤ seedCoefficientDegree S c:=
  MultivariateTarskiDegreeBounds.seed_coefficient _ _ _ _ _ _ (head_coefficient_degree S N hd c) (query_coefficient_degree N c) i

attribute [local irreducible] head seed query arity inputBound degree seedDegree bound

theorem seed_coefficient_mass (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (c:List Bool) (i:ℕ):
    MvMass.mass ((seed S N hd c).coeff i) ≤ 2^seedInputMass S c:=by
  let p:=(seed S N hd c).coeff i
  let W:=p.totalDegree.size
  let enc:MvPolynomial (Fin (arity N c)) ℤ→+*ℤ[X]:=FixedWidthKronecker.encode (arity N c) W
  apply (FixedWidthTarskiMass.mass_le_encoded_exact (arity N c) W p ?_).trans
  · change coefficientMass (enc p) ≤ _
    have HE:enc p=(PseudoRemainder.seed ((head S N hd c).map enc) ((query N c).map enc) (degree S c) (bound S c)).coeff i:=by
      rw [PseudoRemainder.seed_map,Polynomial.coeff_map]
      simp only [p,seed]
    rw [HE]
    apply (NestedMass.coeff_le _ i).trans
    apply FixedWidthTarskiMass.encoded_seed_mass _ _ _ _ (inputBound S c) 4 (S.mass (original c)) 2
    · exact Polynomial.natDegree_map_le.trans (head_degree S N hd c)
    · exact Polynomial.natDegree_map_le.trans (query_degree N c)
    · intro k
      rw [Polynomial.coeff_map]
      exact (FixedWidthTarskiMass.encode_mass_le _ _ _).trans (head_coefficient_mass S N hd c k)
    · intro k
      rw [Polynomial.coeff_map]
      exact (FixedWidthTarskiMass.encode_mass_le _ _ _).trans (query_coefficient_mass N c k)
  · intro e he j
    exact ((MvPolynomial.monomial_le_degreeOf j he).trans (MvPolynomial.degreeOf_le_totalDegree _ j)).trans_lt (Nat.lt_size_self _)

theorem input_le_output (S:Source) (c:List Bool):inputBound S c ≤ outputBound S c:=by
  unfold outputBound MultivariateTarskiDegreeBounds.principalDegreeBound
  exact (le_max_left _ _).trans (Nat.le_mul_of_pos_left _ (by omega))
theorem seed_le_output (S:Source) (c:List Bool):seedCoefficientDegree S c ≤ outputBound S c:=by
  unfold seedCoefficientDegree outputBound MultivariateTarskiDegreeBounds.principalDegreeBound
  exact (le_max_right _ _).trans (Nat.le_mul_of_pos_left _ (by omega))

end LeanCanny.Encoding.IntegralPolynomialWindowTarski
