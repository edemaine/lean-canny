/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiSelectionSource
/-! # One actual source dispatches radius head, seed and principal coefficients

The leading role word is empty for a principal, [false] for a head, and
anything else for a seed. The payload is the unchanged coefficient context.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiKernelSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open RationalSubstitution.IntegerBits (context selectedDegree context_mem_FP selectedDegree_mem_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def payload (z:List Bool):=pairSnd z
def principal (z:List Bool):Prop:=pairFst z=[]
def headOnly (z:List Bool):Prop:=pairFst z=[false]
theorem payload_FP:payload∈FP:=pairSnd_mem_FP
theorem principal_FP:FPPred principal:=Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])
theorem headOnly_FP:FPPred headOnly:=Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [false])

local notation "A"=>FormulaSignSlotRadialRadiusTarskiSource.arity
local notation "W"=>FormulaSignSlotRadialRadiusTarskiSource.width
local notation "D"=>FormulaSignSlotRadialRadiusTarskiSource.degree
attribute [local irreducible] FormulaSignSlotRadialRadiusTarskiSource.arity
  FormulaSignSlotRadialRadiusTarskiSource.width FormulaSignSlotRadialRadiusTarskiSource.degree
  FormulaSignSlotRadialRadiusTarskiSource.polynomial
  FormulaSignSlotRadialRadiusTarskiSource.mass FormulaSignSlotRadialRadiusTarskiSelectionSource.polynomial
  FormulaSignSlotRadialRadiusTarskiSelectionSource.mass

noncomputable def polynomial (z:List Bool):MvPolynomial (Fin (A (payload z))) ℤ:=
  if principal z then FormulaSignSlotRadialRadiusTarskiSource.polynomial (payload z)
  else FormulaSignSlotRadialRadiusTarskiSelectionSource.polynomial (decide (headOnly z)) (payload z)
noncomputable def mass (z:List Bool):=FormulaSignSlotRadialRadiusTarskiSource.mass (payload z)+
  FormulaSignSlotRadialRadiusTarskiSelectionSource.mass (payload z)

theorem polynomial_degree (z:List Bool):(polynomial z).totalDegree≤D (payload z):=by
  unfold polynomial
  split_ifs
  · exact FormulaSignSlotRadialRadiusTarskiSource.polynomial_degree _
  · exact FormulaSignSlotRadialRadiusTarskiSelectionSource.polynomial_degree _ _
theorem polynomial_mass (z:List Bool):MvMass.mass (polynomial z)≤2^mass z:=by
  unfold polynomial
  split_ifs
  · exact (FormulaSignSlotRadialRadiusTarskiSource.polynomial_mass _).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · exact (FormulaSignSlotRadialRadiusTarskiSelectionSource.polynomial_mass _ _).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))

noncomputable def source:IntegralFramedBankPolynomialModel.Source where
  arity z:=A (payload z)
  width z:=W (payload z)
  degree z:=D (payload z)
  mass:=mass
  polynomial:=polynomial
  fit z i:=(MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((polynomial_degree z).trans_lt (FormulaSignSlotRadialRadiusTarskiSource.degree_fit _))
  polynomial_degree:=polynomial_degree
  polynomial_mass:=polynomial_mass

def request (q:List Bool):=pair (pair (payload (context q)) (selectedDegree q)) (pairSnd q)
theorem request_FP:request∈FP:=mem_FP_pair
  (mem_FP_pair (mem_FP_comp context_mem_FP payload_FP) selectedDegree_mem_FP) pairSnd_mem_FP
theorem request_packet (z bits modulus:List Bool):request (pair (pair z bits) modulus)=pair (pair (payload z) bits) modulus:=by
  simp only [request,context,RationalSubstitution.IntegerBits.selectedDegree,pairFst_pair,pairSnd_pair]

noncomputable def coefficient (q:List Bool):=
  if principal (context q) then FormulaSignSlotRadialRadiusTarskiSource.coefficient (request q)
  else if headOnly (context q) then FormulaSignSlotRadialRadiusTarskiSelectionSource.coefficient true (request q)
  else FormulaSignSlotRadialRadiusTarskiSelectionSource.coefficient false (request q)

theorem evaluator:SpaceFunction coefficient:=by
  have EP:=FormulaSignSlotRadialRadiusTarskiSource.evaluator.precompose request request_FP
  have EH:=(FormulaSignSlotRadialRadiusTarskiSelectionSource.evaluator true).precompose request request_FP
  have ES:=(FormulaSignSlotRadialRadiusTarskiSelectionSource.evaluator false).precompose request request_FP
  have E1:=SpaceFunction.branch (fun q=>decide (headOnly (context q)))
    (headOnly_FP.comp context_mem_FP).flag_mem_FP EH ES
  have E:=SpaceFunction.branch (fun q=>decide (principal (context q)))
    (principal_FP.comp context_mem_FP).flag_mem_FP EP E1
  exact E.congr (funext fun q=>by simp only [coefficient,decide_eq_true_eq,Function.comp_apply])

theorem packet (z bits modulus:List Bool):coefficient (pair (pair z bits) modulus)=
    residueBits (((source.polynomial z).coeff (nativeExponent (Equiv.refl _) (source.width z)
      (Nat.fromBitsLE bits)):ℤ):ZMod (Nat.fromBitsLE modulus+1)):=by
  unfold coefficient
  simp only [context,pairFst_pair]
  rw [request_packet]
  by_cases HP:principal z
  · rw [ite_eq_left HP,FormulaSignSlotRadialRadiusTarskiSource.packet]
    simp only [source,polynomial,HP,ite_true,FormulaSignSlotRadialRadiusTarskiSource.source]
  · rw [ite_eq_right HP]
    by_cases HH:headOnly z
    · rw [ite_eq_left HH,FormulaSignSlotRadialRadiusTarskiSelectionSource.packet]
      simp only [source,polynomial,HP,HH,ite_false,decide_true,FormulaSignSlotRadialRadiusTarskiSelectionSource.source]
    · rw [ite_eq_right HH,FormulaSignSlotRadialRadiusTarskiSelectionSource.packet]
      simp only [source,polynomial,HP,HH,ite_false,decide_false,FormulaSignSlotRadialRadiusTarskiSelectionSource.source]

noncomputable def access:IntegralFramedBankPolynomialModel.Access source where
  arity:=FormulaSignSlotRadialRadiusTarskiSource.arity_unary.comp payload_FP
  width:=FormulaSignSlotRadialRadiusTarskiSource.width_unary.comp payload_FP
  degree:=FormulaSignSlotRadialRadiusTarskiSource.degree_binary.comp payload_FP
  mass:=by
    have HP:BinaryFn (fun z=>FormulaSignSlotRadialRadiusTarskiSource.mass (payload z)):=
      FormulaSignSlotRadialRadiusTarskiSource.mass_binary.comp payload_FP
    have HS:BinaryFn (fun z=>FormulaSignSlotRadialRadiusTarskiSelectionSource.mass (payload z)):=by
      unfold FormulaSignSlotRadialRadiusTarskiSelectionSource.mass
      exact FormulaSignSlotRadialRadiusTarskiFamily.selectionMass_binary.comp
        (mem_FP_comp payload_FP FormulaSignSlotRadialRadiusTarskiSource.original_FP)
    exact HP.add HS
  coefficient:=coefficient
  evaluator:=evaluator
  packet:=packet

theorem degree_fit (z:List Bool):source.degree z<2^source.width z:=
  FormulaSignSlotRadialRadiusTarskiSource.degree_fit (payload z)

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiKernelSource
