/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitSquarefreeSelection
public import LeanCanny.Encoding.FormulaSignSlotRadialJointBranchCutRetention
public import LeanCanny.Computation.SpaceFunctionBinaryExistence
/-! # Bounded native principal-cut checking on the same implicit own word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitBranchCutTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry Polynomial PrincipalSubresultant Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input
open FormulaSignSlotRadialImplicitPrincipalWindow (packet env Empty)
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialParameterEliminant.coordinate

private theorem fp_flag (P:List Bool→Prop) (h:FPPred P):SpaceFunction (fun z=>[decide (P z)]):=
  SpaceFunction.ofFP _ h.flag_mem_FP
noncomputable def Candidate (z:List Bool):Prop:=FormulaSignSlotRadialImplicitSquarefreeSelection.Guards z ∧
  (FormulaSignSlotRadialImplicitSquarefreeSelection.declared z=0 ∨Empty z)
theorem candidate_evaluator:SpaceFunction (fun z=>[decide (Candidate z)]):=
  IntegralPolynomialWindowTarskiDecision.flag_and _ _ FormulaSignSlotRadialImplicitSquarefreeSelection.evaluator
    (IntegralPolynomialWindowTarskiDecision.flag_or _ _
      (fp_flag _ (FormulaSignSlotRadialImplicitSquarefreeSelection.declared_binary.eq (BinaryFn.const 0)))
      FormulaSignSlotRadialImplicitPrincipalWindow.empty_evaluator)

noncomputable def coordinate (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j:ℕ):=
  FormulaSignSlotRadialCenterSquarefreeSelection.coordinate
    (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j)
    (fun i=>env c w hw (4*i.val))
private theorem signed_interval (p:Polynomial (Polynomial ℝ)) (d k:ℕ) (hk:k<d) (b:ℝ):
    (∀r,(signedPsc p p.derivative d (d-1) k).eval r=0 → r ∉ Ioo 0 b) ↔
      RealParameterRootBranches.NoRoots (psc p p.derivative d (d-1) k) b:=by
  unfold RealParameterRootBranches.NoRoots
  apply forall_congr'
  intro r
  rw [signedPsc_of_le p p.derivative (by omega : k≤min d (d-1)),Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_neg,Polynomial.eval_one,mul_eq_zero,
    or_iff_right (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))]

theorem empty_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j t d k:ℕ)
    (HS:FormulaSignSlotRadialCenterSelection.Guards
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j)
      (fun i=>env c w hw (4*i.val)) t d) (hk:k<d) (hb:0<env c w hw 3):
    Empty (packet c w j t d k) ↔ RealParameterRootBranches.NoRoots
      (psc (coordinate c w hw j) (coordinate c w hw j).derivative d (d-1) k) (env c w hw 3):=by
  have H:=FormulaSignSlotRadialImplicitPrincipalWindow.empty_packet c w hw j t d k hb
  rw [FormulaSignSlotRadialImplicitSquarefreeSelection.selected_polynomial_packet c w hw j t d k HS] at H
  exact H.trans (signed_interval _ d k hk _)
private theorem declared_packet (c w:List Bool) (j t d k:ℕ):
    FormulaSignSlotRadialImplicitSquarefreeSelection.declared (packet c w j t d k)=d:=by
  simp only [FormulaSignSlotRadialImplicitSquarefreeSelection.declared,
    FormulaSignSlotRadialImplicitPrincipalWindow.degreeWord,packet,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem candidate_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j t d k:ℕ)
    (hb:0<env c w hw 3):
    Candidate (packet c w j t d k) ↔
      FormulaSignSlotRadialCenterSquarefreeSelection.Guards
        (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j)
        (fun i=>env c w hw (4*i.val)) t d k ∧
      (d=0 ∨RealParameterRootBranches.NoRoots
        (psc (coordinate c w hw j) (coordinate c w hw j).derivative d (d-1) k) (env c w hw 3)):=by
  rw [Candidate,FormulaSignSlotRadialImplicitSquarefreeSelection.guards_packet c w hw j t d k,declared_packet]
  apply and_congr_right
  intro HS
  by_cases H0:d=0
  · simp only [H0,true_or]
  · rw [or_iff_right H0,or_iff_right H0]
    exact empty_packet c w hw j t d k HS.1 (by have HK:=HS.2;rw [ite_eq_right H0] at HK;exact HK.1) hb

def context (p:List Bool):=pairFst (pairFst p)
noncomputable def limit (p:List Bool):=FormulaSignSlotRadialJointCoefficientCatalogue.limit
  (FormulaSignSlotRadialImplicitPrincipalWindow.header (context p))
theorem limit_binary:BinaryFn limit:=FormulaSignSlotRadialJointCoefficientCatalogue.limit_binary.comp
  (mem_FP_comp (f:=context) (g:=FormulaSignSlotRadialImplicitPrincipalWindow.header)
    (show context∈FP by polytime [context]) FormulaSignSlotRadialImplicitGridTest.header_FP)
def selectedQuery (q:List Bool):=pair (pairFst (pairFst (pairFst (pairFst q))))
  (pair (pairSnd (pairFst (pairFst (pairFst q))))
    (pair (pairSnd (pairFst (pairFst q))) (pair (pairSnd (pairFst q)) (pairSnd q))))
theorem selectedQuery_FP:selectedQuery∈FP:=by polytime [selectedQuery]
noncomputable def At (p:List Bool):Prop:=∃t<limit p,∃d<limit p,∃k<limit p,
  Candidate (selectedQuery (pair (pair (pair p (BinaryNatCode.encode t)) (BinaryNatCode.encode d)) (BinaryNatCode.encode k)))
theorem at_evaluator:SpaceFunction (fun p=>[decide (At p)]):=by
  have E:=candidate_evaluator.precompose selectedQuery selectedQuery_FP
  have EK:=E.exists_binary (limit_binary.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))
  have ED:=EK.exists_binary (limit_binary.comp pairFst_mem_FP)
  have ET:=ED.exists_binary limit_binary
  exact ET.congr (funext fun p=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [At,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq,pairFst_pair])

private theorem selected_packet (c w:List Bool) (j t d k:ℕ):
    selectedQuery (pair (pair (pair (pair (pair c w) (BinaryNatCode.encode j)) (BinaryNatCode.encode t))
      (BinaryNatCode.encode d)) (BinaryNatCode.encode k))=packet c w j t d k:=by
  simp only [selectedQuery,packet,pairFst_pair,pairSnd_pair]
private theorem limit_packet (c w:List Bool) (j:ℕ):limit (pair (pair c w) (BinaryNatCode.encode j))=
    FormulaSignSlotRadialJointCoefficientCatalogue.degree (FormulaSignSlotRadialImplicitPrincipalWindow.header c)+1:=by
  simp only [limit,context,pairFst_pair,FormulaSignSlotRadialJointCoefficientCatalogue.limit]
private theorem center_bound (c:List Bool) (j:ℕ):FormulaSignSlotRadialCenterSelection.bound
    (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j)=
    FormulaSignSlotRadialJointCoefficientCatalogue.degree (FormulaSignSlotRadialImplicitPrincipalWindow.header c):=by
  apply FormulaSignSlotRadialEliminantRootProfiles.degree_eq
  rw [FormulaSignSlotRadialCoordinatePacket.root]
  simp only [FormulaSignSlotRadialJointCoefficientCatalogue.base,pairFst_pair]
  rfl

/-- The bounded native search is exactly the actual selected-principal interval condition. -/
theorem at_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j:ℕ) (hb:0<env c w hw 3):
    At (pair (pair c w) (BinaryNatCode.encode j)) ↔
      (coordinate c w hw j).natDegree=0 ∨RealParameterRootBranches.NoRoots
        (psc (coordinate c w hw j) (coordinate c w hw j).derivative (coordinate c w hw j).natDegree
          ((coordinate c w hw j).natDegree-1) (DomainSquarefree.index (coordinate c w hw j))) (env c w hw 3):=by
  constructor
  · rintro ⟨t,_,d,_,k,_,HC⟩
    rw [selected_packet] at HC
    obtain ⟨HS,HP⟩:=(candidate_packet c w hw j t d k hb).mp HC
    have HD:=FormulaSignSlotRadialCenterSquarefreeSelection.coordinate_degree _ _ t d HS.1
    have HK:=(FormulaSignSlotRadialCenterSquarefreeSelection.guards_iff _ _ t d k).mp HS |>.2
    change (coordinate c w hw j).natDegree=d at HD
    change k=DomainSquarefree.index (coordinate c w hw j) at HK
    rcases HP with H0|HP
    · exact Or.inl (HD.trans H0)
    · exact Or.inr (by simpa only [HD,←HK] using HP)
  · intro HP
    obtain ⟨t,ht,d,hD,k,hk,HS⟩:=FormulaSignSlotRadialCenterSquarefreeSelection.exists_guards
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialImplicitPrincipalWindow.original c) j)
      (fun i=>env c w hw (4*i.val))
    have HD:=FormulaSignSlotRadialCenterSquarefreeSelection.coordinate_degree _ _ t d HS.1
    have HK:=(FormulaSignSlotRadialCenterSquarefreeSelection.guards_iff _ _ t d k).mp HS |>.2
    change (coordinate c w hw j).natDegree=d at HD
    change k=DomainSquarefree.index (coordinate c w hw j) at HK
    have HB:=center_bound c j
    have HT:t<limit (pair (pair c w) (BinaryNatCode.encode j)):=by rw [limit_packet,←HB];omega
    have HD0:d<limit (pair (pair c w) (BinaryNatCode.encode j)):=by rw [limit_packet,←HB];omega
    have HK0:k<limit (pair (pair c w) (BinaryNatCode.encode j)):=by omega
    refine ⟨t,HT,d,HD0,k,HK0,?_⟩
    rw [selected_packet,candidate_packet c w hw j t d k hb]
    refine ⟨HS,?_⟩
    rcases HP with H0|HP
    · exact Or.inl (HD.symm.trans H0)
    · exact Or.inr (by simpa only [HD,←HK] using HP)

/-- Conjoining the native principal search with the actual leading interval is the full cut test. -/
theorem cut_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j:ℕ) (hb:0<env c w hw 3):
    RealParameterRootBranches.NoRoots (RealParameterRootBranches.cut (coordinate c w hw j)) (env c w hw 3) ↔
      RealParameterRootBranches.NoRoots (coordinate c w hw j).leadingCoeff (env c w hw 3) ∧
        At (pair (pair c w) (BinaryNatCode.encode j)):=by
  rw [RealParameterRootBranches.cut_no_roots_iff,at_packet_iff c w hw j hb]

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitBranchCutTest
