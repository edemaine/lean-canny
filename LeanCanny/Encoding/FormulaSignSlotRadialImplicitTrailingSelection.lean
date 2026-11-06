/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitHeadSelection
/-! # The literal trailing radius head from native finite zero tests -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitTrailingSelection
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
attribute [local instance 2000] Classical.propDecidable

def base (z:List Bool):=pairFst (pairFst (pairFst z))
def tauWord (z:List Bool):=pairSnd (pairFst (pairFst z))
def degreeWord (z:List Bool):=pairSnd (pairFst z)
def ellWord (z:List Bool):=pairSnd z
noncomputable def ell (z:List Bool):=Nat.fromBitsLE (ellWord z)
noncomputable def degree (z:List Bool):=Nat.fromBitsLE (degreeWord z)
theorem ell_binary:BinaryFn ell:=BinaryFn.fromBits pairSnd_mem_FP
theorem degree_binary:BinaryFn degree:=BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
def headQuery (z:List Bool):=pair (pairFst (base z)) (pair (pairSnd (base z)) (pair (tauWord z) (ellWord z)))
def lowerQuery (z:List Bool):=headQuery (pair (pairFst (pairFst z)) (pairSnd z))
def selectedQuery (z:List Bool):=FormulaSignSlotRadialImplicitHeadSelection.selectedQuery (pairFst z)
theorem headQuery_FP:headQuery∈FP:=by polytime [headQuery,base,tauWord,ellWord]
theorem lowerQuery_FP:lowerQuery∈FP:=mem_FP_comp (show (fun z=>pair (pairFst (pairFst z)) (pairSnd z))∈FP by polytime) headQuery_FP
theorem selectedQuery_FP:selectedQuery∈FP:=mem_FP_comp pairFst_mem_FP FormulaSignSlotRadialImplicitHeadSelection.selectedQuery_FP
noncomputable def Guards (z:List Bool):Prop:=FormulaSignSlotRadialImplicitCenterSelection.Guards (selectedQuery z) ∧
  ell z≤degree z ∧ (∀j<ell z,FormulaSignSlotRadialImplicitHeadWindow.Zero (lowerQuery (pair z (BinaryNatCode.encode j)))) ∧
  ¬FormulaSignSlotRadialImplicitHeadWindow.Zero (headQuery z)
theorem guards_evaluator:SpaceFunction (fun z=>[decide (Guards z)]):=by
  have EG:=FormulaSignSlotRadialImplicitCenterSelection.evaluator.precompose selectedQuery selectedQuery_FP
  have EB:=SpaceFunction.ofFP _ (ell_binary.le degree_binary).flag_mem_FP
  have EL:=IntegralPolynomialWindowTarskiDecision.flag_all
    (fun z=>FormulaSignSlotRadialImplicitHeadWindow.Zero (lowerQuery z)) ell
    (FormulaSignSlotRadialImplicitHeadWindow.zero_evaluator.precompose lowerQuery lowerQuery_FP) ell_binary
  have EN:=IntegralPolynomialWindowTarskiDecision.flag_not _
    (FormulaSignSlotRadialImplicitHeadWindow.zero_evaluator.precompose headQuery headQuery_FP)
  have EH:=IntegralPolynomialWindowTarskiDecision.flag_and _ _ EG
    (IntegralPolynomialWindowTarskiDecision.flag_and _ _ EB
      (IntegralPolynomialWindowTarskiDecision.flag_and _ _ EL EN))
  exact EH
noncomputable def Candidate (z:List Bool):Prop:=Guards z ∧FormulaSignSlotRadialImplicitHeadWindow.Empty (headQuery z)
theorem candidate_evaluator:SpaceFunction (fun z=>[decide (Candidate z)]):=
  IntegralPolynomialWindowTarskiDecision.flag_and _ _ guards_evaluator
    (FormulaSignSlotRadialImplicitHeadWindow.empty_evaluator.precompose headQuery headQuery_FP)
noncomputable abbrev limit:=FormulaSignSlotRadialImplicitHeadSelection.limit
theorem limit_packet (c w:List Bool) (j:ℕ):limit (pair (pair c w) (BinaryNatCode.encode j))=
    FormulaSignSlotRadialCenterSelection.bound (FormulaSignSlotRadialImplicitHeadWindow.radiusContext c j)+1:=
  FormulaSignSlotRadialImplicitHeadSelection.limit_packet c w j
noncomputable def At (p:List Bool):Prop:=∃tau<limit p,∃D<limit p,∃ell<limit p,
  Candidate (pair (pair (pair p (BinaryNatCode.encode tau)) (BinaryNatCode.encode D)) (BinaryNatCode.encode ell))
theorem at_evaluator:SpaceFunction (fun p=>[decide (At p)]):=by
  have H2:BinaryFn (fun z=>limit (pairFst (pairFst z))):=
    FormulaSignSlotRadialImplicitGridSelection.limit_binary.comp (show (fun z=>pairFst (pairFst z))∈FP by polytime)
  have H1:BinaryFn (fun z=>limit (pairFst z)):=FormulaSignSlotRadialImplicitGridSelection.limit_binary.comp pairFst_mem_FP
  have E2:=candidate_evaluator.exists_binary H2
  have E1:=E2.exists_binary H1
  have E0:=E1.exists_binary FormulaSignSlotRadialImplicitGridSelection.limit_binary
  exact E0.congr (funext fun p=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [At,List.cons.injEq,and_true,decide_eq_true_eq,pairFst_pair])
noncomputable abbrev radiusContext:=FormulaSignSlotRadialImplicitHeadWindow.radiusContext
noncomputable abbrev center:=FormulaSignSlotRadialImplicitHeadWindow.center
noncomputable abbrev bound:=FormulaSignSlotRadialImplicitHeadWindow.bound

def packet (c w:List Bool) (j tau D ell:ℕ):=pair
  (pair (pair (pair (pair c w) (BinaryNatCode.encode j)) (BinaryNatCode.encode tau)) (BinaryNatCode.encode D)) (BinaryNatCode.encode ell)
private theorem head_packet (c w:List Bool) (j tau D ell:ℕ):headQuery (packet c w j tau D ell)=
    FormulaSignSlotRadialImplicitHeadWindow.packet c w j tau ell:=by
  simp only [headQuery,base,tauWord,ellWord,packet,FormulaSignSlotRadialImplicitHeadWindow.packet,pairFst_pair,pairSnd_pair]
private theorem lower_packet (c w:List Bool) (j tau D ell k:ℕ):lowerQuery (pair (packet c w j tau D ell) (BinaryNatCode.encode k))=
    FormulaSignSlotRadialImplicitHeadWindow.packet c w j tau k:=by
  simp only [lowerQuery,headQuery,base,tauWord,ellWord,packet,FormulaSignSlotRadialImplicitHeadWindow.packet,pairFst_pair,pairSnd_pair]
private theorem selected_packet (c w:List Bool) (j tau D ell:ℕ):selectedQuery (packet c w j tau D ell)=
    FormulaSignSlotRadialImplicitCenterSelection.packet c w j tau D:=by
  simp only [selectedQuery,FormulaSignSlotRadialImplicitHeadSelection.selectedQuery,
    FormulaSignSlotRadialImplicitGridSelection.selectedQuery,packet,FormulaSignSlotRadialImplicitCenterSelection.packet,pairFst_pair,pairSnd_pair]

private theorem radius_zero_iff (c:List Bool) (a:Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c)→ℝ) (tau e:ℕ):
    FormulaSignSlotRadialRadiusHeadInterval.specialized c a tau e=0↔
      ∀r<FormulaSignSlotRadialCenterSelection.bound c+1,FormulaSignSlotRadialCenterSelection.Zero c a tau e r:=by
  unfold FormulaSignSlotRadialRadiusHeadInterval.specialized
  rw [FormulaSignSlotRadialRadiusHeadEvaluation.specialization]
  exact (FormulaSignSlotRadialCenterSelection.radius_zero_iff c a tau e).symm

theorem guards_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j tau D ell:ℕ):
    Guards (packet c w j tau D ell)↔
      FormulaSignSlotRadialCenterTrailingSelection.Guards (radiusContext c j) (center c w hw j) tau D ell:=by
  have HS:FormulaSignSlotRadialImplicitCenterSelection.Guards
      (FormulaSignSlotRadialImplicitCenterSelection.packet c w j tau D)↔
      FormulaSignSlotRadialCenterSelection.Guards (radiusContext c j) (center c w hw j) tau D:=
    FormulaSignSlotRadialImplicitCenterSelection.guards_packet c w hw j tau D
  have HE:FormulaSignSlotRadialImplicitTrailingSelection.ell (packet c w j tau D ell)=ell:=by
    simp only [FormulaSignSlotRadialImplicitTrailingSelection.ell,ellWord,packet,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HD:degree (packet c w j tau D ell)=D:=by
    simp only [degree,degreeWord,packet,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  rw [Guards,selected_packet,HS,HE,HD]
  simp_rw [lower_packet,head_packet,FormulaSignSlotRadialImplicitHeadWindow.zero_packet_iff c w hw,
    radius_zero_iff]
  rfl

private theorem candidate_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (j tau D ell:ℕ) (hb:0<bound c w hw):
    Candidate (packet c w j tau D ell)↔
      FormulaSignSlotRadialCenterTrailingSelection.Guards (radiusContext c j) (center c w hw j) tau D ell ∧
      ∀r,(FormulaSignSlotRadialRadiusHeadInterval.specialized (radiusContext c j) (center c w hw j) tau ell).eval r=0 → r ∉ Ioo 0 (bound c w hw):=by
  rw [Candidate,guards_packet,head_packet,FormulaSignSlotRadialImplicitHeadWindow.empty_packet_iff c w hw j tau ell hb]

private theorem trailing_eq (c:List Bool) (a:Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c)→ℝ)
    (tau D ell:ℕ) (h:FormulaSignSlotRadialCenterTrailingSelection.Guards c a tau D ell):
    FormulaSignSlotRadialRadiusHeadInterval.specialized c a tau ell=
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).trailingCoeff:=
  FormulaSignSlotRadialRadiusHeadEvaluation.trailing c a tau D ell h

attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialCenterSquarefreeSelection.coordinate
  FormulaSignSlotRadialImplicitHeadWindow.radiusContext FormulaSignSlotRadialImplicitHeadWindow.center
  FormulaSignSlotRadialImplicitHeadWindow.bound

/-- The actual trailing index is chosen from complete radius-coefficient zero tests. -/
theorem at_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (j:ℕ) (hb:0<bound c w hw):
    At (pair (pair c w) (BinaryNatCode.encode j))↔
      ∀r,(FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radiusContext c j)
        (center c w hw j)).trailingCoeff.eval r=0 → r ∉ Ioo 0 (bound c w hw):=by
  constructor
  · rintro ⟨tau,_,D,_,ell,_,HC⟩
    obtain ⟨HG,HN⟩:=(candidate_packet_iff c w hw j tau D ell hb).mp HC
    rw [trailing_eq _ _ _ _ _ HG] at HN
    exact HN
  · intro H
    obtain ⟨tau,ht,D,hD,ell,hell,HG⟩:=FormulaSignSlotRadialCenterTrailingSelection.exists_guards (radiusContext c j) (center c w hw j)
    refine ⟨tau,?_,D,?_,ell,?_,(candidate_packet_iff c w hw j tau D ell hb).mpr ⟨HG,?_⟩⟩
    · rw [limit_packet];exact Nat.lt_succ_of_le ht
    · rw [limit_packet];exact Nat.lt_succ_of_le hD
    · rw [limit_packet];exact Nat.lt_succ_of_le (hell.trans hD)
    · rw [trailing_eq _ _ _ _ _ HG]
      exact H

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitTrailingSelection
