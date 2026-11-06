/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPolynomialWindowTarskiMass
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusTarskiSelectionSource
/-! # Actual-source window head, seed and principal coefficient access

Context is pair role (pair window-context selected-order), with role zero
principal, role one head, and every other role seed. No sampled word occurs.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralPolynomialWindowTarski
open LeanCanny.Algebra LeanCanny.Computation Polynomial MvPolynomial MatrixPower FixedWidthPolynomial
open IntegralFramedBankPolynomialModel (Source)
open RationalSubstitution.IntegerBits (context context_mem_FP selectedDegree selectedDegree_mem_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def control (z:List Bool):=pairFst (pairSnd z)
def index (z:List Bool):=Nat.fromBitsLE (pairSnd (pairSnd z))
def role (z:List Bool):=Nat.fromBitsLE (pairFst z)
theorem control_FP:control∈FP:=mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem index_binary:BinaryFn index:=BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
theorem role_binary:BinaryFn role:=BinaryFn.fromBits pairFst_mem_FP

noncomputable def rowArity (N:List Bool→ℕ) (z:List Bool):=arity N (control z)
noncomputable def rowWidth (S:Source) (z:List Bool):=width S (control z)
noncomputable def rowDegree (S:Source) (z:List Bool):=outputBound S (control z)
noncomputable def rowMass (S:Source) (z:List Bool):=massBudget S (control z)+selectionMass S (control z)
noncomputable def polynomial (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (z:List Bool):
    MvPolynomial (Fin (rowArity N z)) ℤ:=
  if role z=0 then FixedWidthTarskiPrincipalBits.polynomial (family S N hd) (control z) (index z)
  else if role z=1 then (head S N hd (control z)).coeff (index z)
  else (seed S N hd (control z)).coeff (index z)

theorem row_polynomial_degree (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (z:List Bool):
    (polynomial S N hd z).totalDegree ≤ rowDegree S z:=by
  unfold polynomial
  split_ifs
  · exact polynomial_degree S N hd _ _
  · exact (head_coefficient_degree S N hd _ _).trans (input_le_output S _)
  · exact (seed_coefficient_degree S N hd _ _).trans (seed_le_output S _)
theorem row_polynomial_mass (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (z:List Bool):
    MvMass.mass (polynomial S N hd z) ≤ 2^rowMass S z:=by
  unfold polynomial
  split_ifs
  · exact (polynomial_mass S N hd _ _).trans (Nat.pow_le_pow_right (by decide) (by unfold rowMass;omega))
  · exact (head_coefficient_mass S N hd _ _).trans
      (Nat.pow_le_pow_right (by decide) (by unfold rowMass selectionMass;omega))
  · exact (seed_coefficient_mass S N hd _ _).trans
      (Nat.pow_le_pow_right (by decide) (by unfold rowMass selectionMass;omega))

noncomputable def source (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1):Source where
  arity:=rowArity N
  width:=rowWidth S
  degree:=rowDegree S
  mass:=rowMass S
  polynomial:=polynomial S N hd
  fit z i:=(MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((row_polynomial_degree S N hd z).trans_lt (output_fit S (control z)))
  polynomial_degree:=row_polynomial_degree S N hd
  polynomial_mass:=row_polynomial_mass S N hd

theorem degree_fit (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (z:List Bool):
    (source S N hd).degree z < 2^(source S N hd).width z:=output_fit S (control z)

attribute [local irreducible] FixedWidthTarskiPrincipalBits.polynomial FixedWidthTarskiPrincipalBits.value
  head seed query arity width inputBound outputBound degree seedDegree bound

private theorem principal_rows (F:FixedWidthTarskiPrincipalBits.Family) (A:FixedWidthTarskiPrincipalBits.Access F)
    (hA:UnaryFn F.arity) (hW:UnaryFn F.width) (read:List Bool→List Bool) (j:List Bool→ℕ)
    (hr:read∈FP) (hj:BinaryFn j)
    (hfit:∀z,(FixedWidthTarskiPrincipalBits.polynomial F (read z) (j z)).totalDegree < 2^F.width (read z))
    (target modulus:List Bool→List Bool) (ht:target∈FP) (hm:modulus∈FP):
    SpaceFunction (FixedWidthRowBits.value (F.arity∘read) (F.width∘read)
      (fun z=>FixedWidthTarskiPrincipalBits.polynomial F (read z) (j z)) target modulus):=by
  let B:=F.arity∘read
  let W:=F.width∘read
  let rank:=FixedWidthQuery.repack B W B W target
  have HR:rank∈FP:=FixedWidthQuery.repack_mem_FP (hA.comp hr) (hW.comp hr) (hA.comp hr) (hW.comp hr) ht
  have HC:(fun z=>BinaryNatCode.encode (Nat.fromBitsLE (rank z)))∈FP:=(BinaryFn.fromBits HR).bits_mem_FP
  let request:=fun z=>FixedWidthTarskiPrincipalBits.packet (read z) (j z) (Nat.fromBitsLE (rank z)) (modulus z)
  have HQ:request∈FP:=mem_FP_pair (mem_FP_pair (mem_FP_pair hr hj.bits_mem_FP) HC) hm
  have E:=(FixedWidthTarskiPrincipalBits.evaluator A).precompose request HQ
  refine E.congr (funext fun z=>?_)
  have HRank:Nat.fromBitsLE (rank z) < count (F.arity (read z)) (F.width (read z)):=by
    have H:=Nat.fromBitsLE_lt_pow_length (rank z)
    dsimp only [rank] at H
    rw [FixedWidthQuery.repack_length] at H
    simpa only [B,W,Function.comp_apply,count,←pow_mul,Nat.mul_comm] using H
  change FixedWidthTarskiPrincipalBits.value A (FixedWidthTarskiPrincipalBits.packet _ _ _ _)=_
  rw [FixedWidthTarskiPrincipalBits.packet_coefficient A (read z) (j z) _
    (FixedWidthTarskiPrincipalBits.polynomial F (read z) (j z)).totalDegree (modulus z) le_rfl (hfit z) HRank]
  unfold FixedWidthRowBits.value
  apply congrArg (fun e=>residueBits (((FixedWidthTarskiPrincipalBits.polynomial F (read z) (j z)).coeff e:ℤ):ZMod (Nat.fromBitsLE (modulus z)+1)))
  exact nativeExponent_repack (Equiv.refl _) W W target z le_rfl

noncomputable def seedReader (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1)
    (A:IntegralFramedBankPolynomialModel.Access S) (HN:UnaryFn N) (hfit:∀c,S.degree c < 2^S.width c):
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial (arity N) (width S) (seed S N hd)):=by
  unfold seed
  exact FormulaSignSlotRadialRadiusTarskiFamily.decodedSeedReader (family S N hd) (access S N hd A HN hfit)

noncomputable def coefficient (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1):=
  FixedWidthRowBits.value (rowArity N∘context) (rowWidth S∘context)
    (fun q=>polynomial S N hd (context q)) selectedDegree pairSnd

theorem evaluator (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1)
    (A:IntegralFramedBankPolynomialModel.Access S) (HN:UnaryFn N) (hfit:∀c,S.degree c < 2^S.width c):
    SpaceFunction (coefficient S N hd):=by
  let read:=control∘context
  let j:=index∘context
  have HR:read∈FP:=mem_FP_comp context_mem_FP control_FP
  have HJ:BinaryFn j:=index_binary.comp context_mem_FP
  let AR:=arity N∘read
  let WR:=width S∘read
  let PP:=fun q=>FixedWidthTarskiPrincipalBits.polynomial (family S N hd) (read q) (j q)
  let PH:=fun q=>(head S N hd (read q)).coeff (j q)
  let PS:=fun q=>(seed S N hd (read q)).coeff (j q)
  have EP:SpaceFunction (FixedWidthRowBits.value AR WR PP selectedDegree pairSnd):=
    principal_rows (family S N hd) (access S N hd A HN hfit) (arity_unary N HN) (width_unary S A)
      read j HR HJ (fun q=>(polynomial_degree S N hd (read q) (j q)).trans_lt (output_fit S (read q)))
      selectedDegree pairSnd selectedDegree_mem_FP pairSnd_mem_FP
  have EH:SpaceFunction (FixedWidthRowBits.value AR WR PH selectedDegree pairSnd):=
    FixedWidthBivariateRowBits.evaluator (arity N) (width S) (head S N hd) (headReader S N hd A HN hfit)
      (arity_unary N HN) (width_unary S A) (fun c i=>((head_coefficient_degree S N hd c i).trans
        (input_le_output S c)).trans_lt (output_fit S c)) read HR j HJ
      selectedDegree pairSnd selectedDegree_mem_FP pairSnd_mem_FP
  have ES:SpaceFunction (FixedWidthRowBits.value AR WR PS selectedDegree pairSnd):=
    FixedWidthBivariateRowBits.evaluator (arity N) (width S) (seed S N hd) (seedReader S N hd A HN hfit)
      (arity_unary N HN) (width_unary S A) (fun c i=>((seed_coefficient_degree S N hd c i).trans
        (seed_le_output S c)).trans_lt (output_fit S c)) read HR j HJ
      selectedDegree pairSnd selectedDegree_mem_FP pairSnd_mem_FP
  have HRole:BinaryFn (fun q=>role (context q)):=role_binary.comp context_mem_FP
  have H0:FPPred (fun q=>role (context q)=0):=HRole.eq (BinaryFn.const 0)
  have H1:FPPred (fun q=>role (context q)=1):=HRole.eq (BinaryFn.const 1)
  have E1:=FixedWidthRowBits.branch_evaluator AR WR PH PS selectedDegree pairSnd
    (fun q=>role (context q)=1) H1 EH ES
  have E:=FixedWidthRowBits.branch_evaluator AR WR PP (fun q=>if role (context q)=1 then PH q else PS q)
    selectedDegree pairSnd (fun q=>role (context q)=0) H0 EP E1
  exact E.congr (funext fun q=>by
    dsimp only [coefficient,polynomial,rowArity,rowWidth,AR,WR,PP,PH,PS,read,j,FixedWidthRowBits.value,Function.comp_apply])

theorem packet (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1) (z bits modulus:List Bool):
    coefficient S N hd (pair (pair z bits) modulus)=residueBits
      ((((source S N hd).polynomial z).coeff (nativeExponent (Equiv.refl _) ((source S N hd).width z)
        (Nat.fromBitsLE bits)):ℤ):ZMod (Nat.fromBitsLE modulus+1)):=
  FormulaSignSlotRadialRadiusTarskiSource.row_packet (rowArity N) (rowWidth S) (polynomial S N hd) z bits modulus

noncomputable def sourceAccess (S:Source) (N:List Bool→ℕ) (hd:∀c,S.arity c=N c+1)
    (A:IntegralFramedBankPolynomialModel.Access S) (HN:UnaryFn N) (hfit:∀c,S.degree c < 2^S.width c):
    IntegralFramedBankPolynomialModel.Access (source S N hd) where
  arity:=(arity_unary N HN).comp control_FP
  width:=(width_unary S A).comp control_FP
  degree:=(outputBound_binary S A).comp control_FP
  mass:=by
    have HM:BinaryFn (fun z=>massBudget S (control z)):=(massBudget_binary S A).comp control_FP
    have HS:BinaryFn (fun z=>selectionMass S (control z)):=(selectionMass_binary S A).comp control_FP
    exact HM.add HS
  coefficient:=coefficient S N hd
  evaluator:=evaluator S N hd A HN hfit
  packet:=packet S N hd

end LeanCanny.Encoding.IntegralPolynomialWindowTarski
