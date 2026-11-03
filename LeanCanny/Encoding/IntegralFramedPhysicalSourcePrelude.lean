/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalIntegerVertex
public import LeanCanny.Algebra.IntegralMixedSourceIntegerRealization
/-! # A literal original-source integer prelude has a correlated full vertex

The saved prefix is proved equal to the actual integer command list.
Original chronological roots are re-adjoined at this target horizon and
width. No scalar-sampler label or tuple is transported from another plan.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSourcePrelude
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (Q : ∀r,SpatialSource (P.ambient r))
  (hdegree : ∀r,(Q r).degree=P.degree r)
  (hcap : ∀r,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient r+1) (P.degree r)≤2^P.width r)
  (S : IntegerPolynomialRootQueriesBits.Source) (N : List Bool→ℕ) (hz : ∀q,S.polynomial q≠0)
  (hd : ∀r i,S.degree (pair r (BinaryNatCode.encode i))≤2^P.width r)
  (hroom : ∀r,N r+2≤P.cap r+1)
local notation "D"=>IntegralMixedSourceIntegerPrelude.plan P Q hdegree hcap S N hz hd hroom

def key (N : List Bool→ℕ) (r : List Bool) :=keyAt r (N r) []

theorem rules_length (r : List Bool) : ((D).rules r).length=N r :=
  IntegralMixedSourceIntegerPrelude.commands_length _ _ _ _ _ _ _ _

theorem key_root (r : List Bool) : pairFst (key N r)=r :=by
  simp only [key,keyAt_root]

theorem commands_eq (r : List Bool) : commands P D (key N r)=(D).rules (pairFst (key N r)) :=by
  unfold commands
  have HL : ((D).rules (pairFst (key N r))).length=prefixLength P (key N r) :=by
    exact (rules_length P Q hdegree hcap S N hz hd hroom _).trans
      ((congrArg N (key_root N r)).trans
        (keyAt_prefix P r (N r) [] (by have HC:=hroom r; omega)).symm)
  rw [←HL]
  exact IntegralMixedFramedHistoryScript.paddedPast_full _ _

variable (H : IntegralMixedFramedHistoryFamilyBits.Data P (IntegralMixedSourceIntegerPrelude.plan P Q hdegree hcap S N hz hd hroom))
  (hN : ∀r,0<N r)

include hN in
theorem positive (r : List Bool) : 0<(family P D H).birth (key N r) :=by
  rw [family_birth]
  exact (hN r).trans_eq (keyAt_prefix P r (N r) [] (by have HC:=hroom r; omega)).symm

private theorem run_realizes_eq {n cap B : ℕ} {Q : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State Q cap B 0 ι) (cs ds : List (IntegralMixedFramedHistoryScript.Instruction n B))
    (he : cs=ds) (hc : cs.length≤cap+1) (hd : ds.length≤cap+1) (v : ℕ→ℝ)
    (h : IntegralMixedIntegerRealization.Realizes (IntegralMixedFramedHistoryScript.run x ds hd) v) :
    IntegralMixedIntegerRealization.Realizes (IntegralMixedFramedHistoryScript.run x cs hc) v :=by
  cases he
  exact h

theorem exists_vertex (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (r : List Bool) (values : ℕ→ℝ)
    (hr : ∀j<N r,(S.polynomial (pair r (BinaryNatCode.encode j))).eval₂ (Int.castRingHom ℝ) (values j)=0) :
    ∃w,∃hw : SquareSampleCompleteVertices.Valid
      (IntegralFramedPhysicalSquare.input P D H L F C hs (key N) (positive P Q hdegree hcap S N hz hd hroom H hN)) r w,
      w.length=SquareSampleCompleteVertices.width
        (IntegralFramedPhysicalSquare.input P D H L F C hs (key N) (positive P Q hdegree hcap S N hz hd hroom H hN)) r ∧
      ∀i : Fin ((family P D H).birth (key N r)),
        IntegralFramedPhysicalSquare.point P D H L F C hs (key N) (positive P Q hdegree hcap S N hz hd hroom H hN) r w hw i=
          values (N r-1-i.val) :=by
  have HK:=key_root N r
  have HR : ∀j<N (pairFst (key N r)),(S.polynomial (pair (pairFst (key N r)) (BinaryNatCode.encode j))).eval₂
      (Int.castRingHom ℝ) (values j)=0 :=by simpa only [key,keyAt_root] using hr
  have HE:=commands_eq P Q hdegree hcap S N hz hd hroom r
  let root:=pairFst (key N r)
  let x:=initial P D root
  let hq:=fun r=>(initial P D r).critical_cap
  have HC : ((D).rules root).length≤P.cap root+1+1 :=by
    rw [rules_length P Q hdegree hcap S N hz hd hroom]
    have HC:=hroom root
    omega
  have HC' : (commands P D (key N r)).length≤P.cap root+1+1 :=by rw [HE]; exact HC
  have HRuns : IntegralMixedIntegerRealization.Realizes (IntegralMixedFramedHistoryScript.run x ((D).rules root) HC)
      (fun i=>values (N root-1-i)) :=
    IntegralMixedSourceIntegerPrelude.realizes P Q hq S N hz hd root x (fun i : Fin 0=>Fin.elim0 i)
      (fun i=>Fin.elim0 i) HC values HR
  have HRun:=run_realizes_eq x _ _ HE HC' HC _ HRuns
  have HState : IntegralMixedIntegerRealization.Realizes ((family P D H).state (key N r))
      (fun i=>values (N (pairFst (key N r))-1-i)) :=HRun
  obtain ⟨w,hw,hlen,hvalues⟩:=IntegralFramedPhysicalSquare.exists_realized P D H L F C hs (key N)
    (positive P Q hdegree hcap S N hz hd hroom H hN) r (fun i=>values (N (pairFst (key N r))-1-i)) HState
  refine ⟨w,hw,hlen,fun i=>(hvalues i).trans ?_⟩
  exact congrArg (fun a=>values (a-1-i.val)) (congrArg N HK)
end LeanCanny.Encoding.IntegralFramedPhysicalSourcePrelude
