/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitPrincipalWindow
/-! # Native same-word principal zero tests choose the actual squarefree index -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitSquarefreeSelection
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Polynomial PrincipalSubresultant Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input
local notation "Raw"=>FormulaSignSlotRadialPrincipalRadiusSource.source
local notation "N"=>FormulaSignSlotRadialCutWindowSources.principalCenters
local notation "HD"=>FormulaSignSlotRadialCutWindowSources.principal_dimension
open FormulaSignSlotRadialImplicitPrincipalWindow (packet env Zero Empty coordinateWord tauWord degreeWord orderWord sample)
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialPrincipalRadiusSource.source

private noncomputable def head (z:List Bool) (v:ℕ→ℝ):=
  IntegralPolynomialWindowTarski.baseHead Raw N HD z (fun i=>v (4*i.val))
private theorem head_selected (u:List Bool) (v:ℕ→ℝ) (t d k:ℕ)
    (HS:FormulaSignSlotRadialCenterSelection.Guards u (fun i=>v (4*i.val)) t d):
    head (FormulaSignSlotRadialPrincipalWindowBounds.rawContext u t d k) v=
      signedPsc (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate u (fun i=>v (4*i.val)))
        (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate u (fun i=>v (4*i.val))).derivative d (d-1) k:=
  FormulaSignSlotRadialJointSquarefreeIndexRetention.principal_polynomial u v t d k HS
private theorem signed_zero (p:Polynomial (Polynomial ℝ)) (d k:ℕ) (hk:k<d):
    signedPsc p p.derivative d (d-1) k=0 ↔ psc p p.derivative d (d-1) k=0:=by
  rw [signedPsc_of_le p p.derivative (by omega : k≤min d (d-1)),mul_eq_zero,
    or_iff_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))]
private theorem head_value (z:List Bool) (v:ℕ→ℝ):
    IntegralPolynomialWindowTarski.baseHead Raw N HD z (fun i=>v (4*i.val))=head z v:=rfl
attribute [local irreducible] head

theorem selected_polynomial_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j t d k:ℕ)
    (HS:FormulaSignSlotRadialCenterSelection.Guards
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j)
      (fun i=>env c w hw (4*i.val)) t d):
    IntegralPolynomialWindowTarski.baseHead Raw N HD
      (FormulaSignSlotRadialImplicitPrincipalWindow.rawContext (packet c w j t d k)) (fun i=>env c w hw (4*i.val))=
      signedPsc (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate
        (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j)
        (fun i=>env c w hw (4*i.val)))
        (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate
          (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j)
          (fun i=>env c w hw (4*i.val))).derivative d (d-1) k:=by
  rw [head_value,FormulaSignSlotRadialImplicitPrincipalWindow.raw_packet,head_selected _ _ t d k HS]

theorem zero_unsigned_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j t d k:ℕ)
    (HS:FormulaSignSlotRadialCenterSelection.Guards
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j)
      (fun i=>env c w hw (4*i.val)) t d) (hk:k<d):
    Zero (packet c w j t d k) ↔
      (FormulaSignSlotRadialFormalCenter.radiusMap
        (pairFst (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j))
        (fun i=>env c w hw (4*i.val)))
        (FormulaSignSlotRadialCenterSquarefreeSelection.principal
          (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j) t d k)=0:=by
  have H:=FormulaSignSlotRadialImplicitPrincipalWindow.zero_packet c w hw j t d k
  rw [head_value] at H
  rw [FormulaSignSlotRadialImplicitPrincipalWindow.raw_packet,head_selected _ _ t d k HS] at H
  rw [FormulaSignSlotRadialCenterSquarefreeSelection.principal_map _ _ t d k HS]
  exact H.trans (signed_zero _ d k hk)

def order (z:List Bool):=Nat.fromBitsLE (orderWord z)
def declared (z:List Bool):=Nat.fromBitsLE (degreeWord z)
def selectionQuery (z:List Bool):=pair (pair (sample z) (coordinateWord z)) (pair (tauWord z) (degreeWord z))
def withOrder (z:List Bool) (k:ℕ):=pair (sample z)
  (pair (coordinateWord z) (pair (tauWord z) (pair (degreeWord z) (BinaryNatCode.encode k))))
def lowerQuery (q:List Bool):=withOrder (pairFst q) (Nat.fromBitsLE (pairSnd q))
theorem order_binary:BinaryFn order:=BinaryFn.fromBits (show orderWord∈FP by polytime [FormulaSignSlotRadialImplicitPrincipalWindow.orderWord])
theorem declared_binary:BinaryFn declared:=BinaryFn.fromBits (show degreeWord∈FP by polytime [FormulaSignSlotRadialImplicitPrincipalWindow.degreeWord])
theorem selectionQuery_FP:selectionQuery∈FP:=by
  polytime [selectionQuery,FormulaSignSlotRadialImplicitPrincipalWindow.sample,
    FormulaSignSlotRadialImplicitPrincipalWindow.coordinateWord,FormulaSignSlotRadialImplicitPrincipalWindow.tauWord,
    FormulaSignSlotRadialImplicitPrincipalWindow.degreeWord]
theorem lowerQuery_FP:lowerQuery∈FP:=by
  unfold lowerQuery withOrder
  exact mem_FP_pair (by polytime [FormulaSignSlotRadialImplicitPrincipalWindow.sample])
    (mem_FP_pair (by polytime [FormulaSignSlotRadialImplicitPrincipalWindow.coordinateWord])
      (mem_FP_pair (by polytime [FormulaSignSlotRadialImplicitPrincipalWindow.tauWord])
        (mem_FP_pair (by polytime [FormulaSignSlotRadialImplicitPrincipalWindow.degreeWord])
          (BinaryFn.fromBits pairSnd_mem_FP).bits_mem_FP)))
noncomputable def Lower (z:List Bool):Prop:=∀k<order z,Zero (withOrder z k)
noncomputable def IndexGuards (z:List Bool):Prop:=if declared z=0 then order z=0 else
  order z<declared z ∧Lower z ∧¬Zero z
noncomputable def Guards (z:List Bool):Prop:=
  FormulaSignSlotRadialImplicitCenterSelection.Guards (selectionQuery z) ∧IndexGuards z

private theorem fp_flag (P:List Bool→Prop) (h:FPPred P):SpaceFunction (fun z=>[decide (P z)]):=
  SpaceFunction.ofFP _ h.flag_mem_FP

theorem lower_evaluator:SpaceFunction (fun z=>[decide (Lower z)]):=by
  have E:=FormulaSignSlotRadialImplicitPrincipalWindow.zero_evaluator.precompose lowerQuery lowerQuery_FP
  exact (E.forall_binary order_binary).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Lower,Function.comp_apply,lowerQuery,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
      List.cons.injEq,and_true,decide_eq_true_eq])
theorem index_evaluator:SpaceFunction (fun z=>[decide (IndexGuards z)]):=by
  have E:=IntegralPolynomialWindowTarskiDecision.flag_and _ _
    (fp_flag _ (order_binary.lt declared_binary))
    (IntegralPolynomialWindowTarskiDecision.flag_and _ _ lower_evaluator
      (IntegralPolynomialWindowTarskiDecision.flag_not _ FormulaSignSlotRadialImplicitPrincipalWindow.zero_evaluator))
  have H:=SpaceFunction.branch (fun z=>decide (declared z=0))
    (declared_binary.eq (BinaryFn.const 0)).flag_mem_FP
    (SpaceFunction.ofFP _ (order_binary.eq (BinaryFn.const 0)).flag_mem_FP) E
  exact H.congr (funext fun z=>by
    by_cases H0:declared z=0 <;>simp only [IndexGuards,H0,decide_true,decide_false,ite_true,ite_false,Bool.false_eq_true]
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq])
theorem evaluator:SpaceFunction (fun z=>[decide (Guards z)]):=
  IntegralPolynomialWindowTarskiDecision.flag_and _ _
    (FormulaSignSlotRadialImplicitCenterSelection.evaluator.precompose selectionQuery selectionQuery_FP) index_evaluator

private theorem selection_packet (c w:List Bool) (j t d k:ℕ):
    selectionQuery (packet c w j t d k)=FormulaSignSlotRadialImplicitCenterSelection.packet c w j t d:=by
  simp only [selectionQuery,packet,FormulaSignSlotRadialImplicitPrincipalWindow.sample,
    FormulaSignSlotRadialImplicitPrincipalWindow.coordinateWord,FormulaSignSlotRadialImplicitPrincipalWindow.tauWord,
    FormulaSignSlotRadialImplicitPrincipalWindow.degreeWord,FormulaSignSlotRadialImplicitCenterSelection.packet,
    pairFst_pair,pairSnd_pair]
private theorem withOrder_packet (c w:List Bool) (j t d k i:ℕ):
    withOrder (packet c w j t d k) i=packet c w j t d i:=by
  simp only [withOrder,packet,FormulaSignSlotRadialImplicitPrincipalWindow.sample,
    FormulaSignSlotRadialImplicitPrincipalWindow.coordinateWord,FormulaSignSlotRadialImplicitPrincipalWindow.tauWord,
    FormulaSignSlotRadialImplicitPrincipalWindow.degreeWord,pairFst_pair,pairSnd_pair]
private theorem order_packet (c w:List Bool) (j t d k:ℕ):order (packet c w j t d k)=k:=by
  simp only [order,packet,FormulaSignSlotRadialImplicitPrincipalWindow.orderWord,
    pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
private theorem declared_packet (c w:List Bool) (j t d k:ℕ):declared (packet c w j t d k)=d:=by
  simp only [declared,packet,FormulaSignSlotRadialImplicitPrincipalWindow.degreeWord,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

/-- Actual lower-zero and selected-nonzero tests pick the genuine domain squarefree index. -/
theorem guards_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j t d k:ℕ):
    Guards (packet c w j t d k) ↔ FormulaSignSlotRadialCenterSquarefreeSelection.Guards
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j)
      (fun i=>env c w hw (4*i.val)) t d k:=by
  rw [Guards,selection_packet,FormulaSignSlotRadialImplicitCenterSelection.guards_packet c w hw j t d]
  unfold FormulaSignSlotRadialCenterSquarefreeSelection.Guards
  apply and_congr_right
  intro HS
  rw [IndexGuards,order_packet,declared_packet]
  by_cases H0:d=0
  · rw [ite_eq_left H0,ite_eq_left H0]
  · rw [ite_eq_right H0,ite_eq_right H0]
    apply and_congr_right
    intro hk
    have HL:Lower (packet c w j t d k) ↔ ∀i<k,
        (FormulaSignSlotRadialFormalCenter.radiusMap
          (pairFst (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j))
          (fun a=>env c w hw (4*a.val)))
          (FormulaSignSlotRadialCenterSquarefreeSelection.principal
            (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j) t d i)=0:=by
      unfold Lower
      rw [order_packet]
      apply forall_congr'
      intro i
      apply forall_congr'
      intro hi
      rw [withOrder_packet]
      exact zero_unsigned_packet c w hw j t d i HS (lt_trans hi hk)
    exact and_congr HL (not_congr (zero_unsigned_packet c w hw j t d k HS hk))

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitSquarefreeSelection
