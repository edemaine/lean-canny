/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiAccess
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiMass
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
/-! # Actual formal-center/endpoint principal sources

Context is pair radius-Tarski-context principal-order. The source variables
are the endpoint followed by all center coordinates, without sampled words.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open RationalSubstitution.IntegerBits (context context_mem_FP selectedDegree selectedDegree_mem_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthTarskiPrincipalBits.polynomial FixedWidthTarskiPrincipalBits.value
  FormulaSignSlotRadialRadiusTarskiFamily.arity FormulaSignSlotRadialRadiusTarskiFamily.width
  FormulaSignSlotRadialRadiusTarskiFamily.head FormulaSignSlotRadialRadiusTarskiFamily.query
  FormulaSignSlotRadialRadiusTarskiFamily.outputBound FormulaSignSlotRadialRadiusTarskiFamily.inputBound
  FormulaSignSlotRadialRadiusTarskiFamily.degree FormulaSignSlotRadialRadiusTarskiFamily.seedDegree
  FormulaSignSlotRadialRadiusTarskiFamily.bound

private theorem principal_row_evaluator (F:FixedWidthTarskiPrincipalBits.Family)
    (A:FixedWidthTarskiPrincipalBits.Access F) (hA:UnaryFn F.arity) (hW:UnaryFn F.width)
    (read:List Bool→List Bool) (j:List Bool→ℕ) (hr:read∈FP) (hj:BinaryFn j)
    (hfit:∀z,(FixedWidthTarskiPrincipalBits.polynomial F (read z) (j z)).totalDegree<2^F.width (read z))
    (target modulus:List Bool→List Bool) (ht:target∈FP) (hm:modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (F.arity∘read) (F.width∘read)
      (fun z=>FixedWidthTarskiPrincipalBits.polynomial F (read z) (j z)) target modulus):=by
  let B:=F.arity∘read
  let W:=F.width∘read
  let rank:=FixedWidthQuery.repack B W B W target
  have HB:UnaryFn B:=hA.comp hr
  have HW:UnaryFn W:=hW.comp hr
  have HR:rank∈FP:=FixedWidthQuery.repack_mem_FP HB HW HB HW ht
  have HCode:(fun z=>BinaryNatCode.encode (Nat.fromBitsLE (rank z)))∈FP:=(BinaryFn.fromBits HR).bits_mem_FP
  let request:=fun z=>FixedWidthTarskiPrincipalBits.packet (read z) (j z) (Nat.fromBitsLE (rank z)) (modulus z)
  have HRequest:request∈FP:=mem_FP_pair (mem_FP_pair (mem_FP_pair hr hj.bits_mem_FP) HCode) hm
  have E:=(FixedWidthTarskiPrincipalBits.evaluator A).precompose request HRequest
  refine E.congr (funext fun z=>?_)
  have HRank:Nat.fromBitsLE (rank z)<count (F.arity (read z)) (F.width (read z)):=by
    have H:=Nat.fromBitsLE_lt_pow_length (rank z)
    dsimp only [rank] at H
    rw [FixedWidthQuery.repack_length] at H
    simpa only [B,W,Function.comp_apply,count,←pow_mul,Nat.mul_comm] using H
  change FixedWidthTarskiPrincipalBits.value A (FixedWidthTarskiPrincipalBits.packet _ _ _ _)=_
  rw [FixedWidthTarskiPrincipalBits.packet_coefficient A (read z) (j z) _
    (FixedWidthTarskiPrincipalBits.polynomial F (read z) (j z)).totalDegree (modulus z) le_rfl (hfit z) HRank]
  unfold FixedWidthRowBits.value
  apply congrArg (fun e=>residueBits (((FixedWidthTarskiPrincipalBits.polynomial F (read z) (j z)).coeff e:ℤ):
    ZMod (Nat.fromBitsLE (modulus z)+1)))
  exact nativeExponent_repack (Equiv.refl _) W W target z le_rfl

theorem row_packet_at (A W:List Bool→ℕ) (p:(z:List Bool)→MvPolynomial (Fin (A z)) ℤ)
    (q z bits modulus:List Bool) (HC:context q=z) (HD:selectedDegree q=bits) (HM:pairSnd q=modulus):
    FixedWidthRowBits.value (A∘context) (W∘context) (fun v=>p (context v)) selectedDegree pairSnd q=
      residueBits (((p z).coeff (nativeExponent (Equiv.refl _) (W z)
        (Nat.fromBitsLE bits)):ℤ):ZMod (Nat.fromBitsLE modulus+1)):=by
  cases HC
  cases HD
  cases HM
  rfl

theorem row_packet (A W:List Bool→ℕ) (p:(z:List Bool)→MvPolynomial (Fin (A z)) ℤ)
    (z bits modulus:List Bool):
    FixedWidthRowBits.value (A∘context) (W∘context) (fun q=>p (context q)) selectedDegree pairSnd
      (pair (pair z bits) modulus)=residueBits (((p z).coeff (nativeExponent (Equiv.refl _) (W z)
        (Nat.fromBitsLE bits)):ℤ):ZMod (Nat.fromBitsLE modulus+1)):=by
  exact row_packet_at A W p _ z bits modulus
    (by simp only [context,pairFst_pair])
    (by simp only [RationalSubstitution.IntegerBits.selectedDegree,pairFst_pair,pairSnd_pair])
    (pairSnd_pair _ _)

local notation "F"=>FormulaSignSlotRadialRadiusTarskiFamily.family

def original (z:List Bool):=pairFst z
def order (z:List Bool):=Nat.fromBitsLE (pairSnd z)
noncomputable def arity (z:List Bool):=FormulaSignSlotRadialRadiusTarskiFamily.arity (original z)
noncomputable def width (z:List Bool):=FormulaSignSlotRadialRadiusTarskiFamily.width (original z)
noncomputable def degree (z:List Bool):=FormulaSignSlotRadialRadiusTarskiFamily.outputBound (original z)
noncomputable def mass (z:List Bool):=FormulaSignSlotRadialRadiusTarskiFamily.massBudget (original z)
noncomputable def polynomial (z:List Bool):MvPolynomial (Fin (arity z)) ℤ:=
  FixedWidthTarskiPrincipalBits.polynomial F (original z) (order z)

theorem original_FP :original∈FP:=pairFst_mem_FP
theorem order_binary :BinaryFn order:=BinaryFn.fromBits pairSnd_mem_FP
theorem arity_unary :UnaryFn arity:=FormulaSignSlotRadialRadiusTarskiFamily.arity_unary.comp original_FP
theorem width_unary :UnaryFn width:=FormulaSignSlotRadialRadiusTarskiFamily.width_unary.comp original_FP
theorem degree_binary :BinaryFn degree:=FormulaSignSlotRadialRadiusTarskiFamily.outputBound_binary.comp original_FP
theorem mass_binary :BinaryFn mass:=FormulaSignSlotRadialRadiusTarskiFamily.massBudget_binary.comp original_FP
theorem polynomial_degree (z:List Bool):(polynomial z).totalDegree≤degree z:=
  FormulaSignSlotRadialRadiusTarskiFamily.polynomial_degree _ _
theorem polynomial_mass (z:List Bool):MvMass.mass (polynomial z)≤2^mass z:=
  FormulaSignSlotRadialRadiusTarskiFamily.polynomial_mass _ _
theorem degree_fit (z:List Bool):degree z<2^width z:=by
  unfold degree width FormulaSignSlotRadialRadiusTarskiFamily.width
  exact (by omega:FormulaSignSlotRadialRadiusTarskiFamily.outputBound (original z)≤
    FormulaSignSlotRadialRadiusTarskiFamily.outputBound (original z)+
      FormulaSignSlotRadialRadiusTarskiFamily.inputBound (original z)+1).trans_lt (Nat.lt_size_self _)

noncomputable def source:IntegralFramedBankPolynomialModel.Source where
  arity:=arity
  width:=width
  degree:=degree
  mass:=mass
  polynomial:=polynomial
  fit z i:=(MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt ((polynomial_degree z).trans_lt (degree_fit z))
  polynomial_degree:=polynomial_degree
  polynomial_mass:=polynomial_mass

noncomputable def coefficient:=FixedWidthRowBits.value (arity∘context) (width∘context)
  (fun q=>polynomial (context q)) selectedDegree pairSnd

theorem evaluator:SpaceFunction coefficient:=
  principal_row_evaluator F FormulaSignSlotRadialRadiusTarskiFamily.access
    FormulaSignSlotRadialRadiusTarskiFamily.arity_unary FormulaSignSlotRadialRadiusTarskiFamily.width_unary
    (original∘context) (order∘context) (mem_FP_comp context_mem_FP original_FP) (order_binary.comp context_mem_FP)
    (fun q=>(polynomial_degree (context q)).trans_lt (degree_fit (context q)))
    selectedDegree pairSnd selectedDegree_mem_FP pairSnd_mem_FP

theorem packet (z bits modulus:List Bool):coefficient (pair (pair z bits) modulus)=
    residueBits (((source.polynomial z).coeff (nativeExponent (Equiv.refl _) (source.width z)
      (Nat.fromBitsLE bits)):ℤ):ZMod (Nat.fromBitsLE modulus+1)):=by
  exact row_packet arity width polynomial z bits modulus

noncomputable def access:IntegralFramedBankPolynomialModel.Access source where
  arity:=arity_unary
  width:=width_unary
  degree:=degree_binary
  mass:=mass_binary
  coefficient:=coefficient
  evaluator:=evaluator
  packet:=packet

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiSource
