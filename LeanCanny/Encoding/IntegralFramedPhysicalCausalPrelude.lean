/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSourcePrelude
public import LeanCanny.Algebra.IntegralMixedSourceIntegerCausalPrefix
/-! # One full vertex at the integer boundary of an actual causal plan

Later records impose no roots at this saved prefix. All integer leaves are
re-adjoined at the actual extended plan's target horizon and scalar width.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalCausalPrelude
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (Q : ∀r,SpatialSource (P.ambient r))
  (hdegree : ∀r,(Q r).degree=P.degree r)
  (hcap : ∀r,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient r+1) (P.degree r)≤2^P.width r)
  (S : IntegerPolynomialRootQueriesBits.Source) (N : List Bool→ℕ) (hz : ∀q,S.polynomial q≠0)
  (hd : ∀r i,S.degree (pair r (BinaryNatCode.encode i))≤2^P.width r)
  (later : ∀r,List (IntegralMixedCausalRecordBits.Record (P.ambient r) (P.width r)))
  (hroom : ∀r,(later r).length+N r+2≤P.cap r+1)
local notation "D"=>IntegralMixedSourceIntegerPrelude.extendedPlan P Q hdegree hcap S N hz hd later hroom

variable (H : IntegralMixedFramedHistoryFamilyBits.Data P
  (IntegralMixedSourceIntegerPrelude.extendedPlan P Q hdegree hcap S N hz hd later hroom)) (hN : ∀r,0<N r)

include hN in
theorem positive (r : List Bool) : 0<(family P D H).birth (IntegralFramedPhysicalSourcePrelude.key N r) :=by
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
      (IntegralFramedPhysicalSquare.input P D H L F C hs (IntegralFramedPhysicalSourcePrelude.key N)
        (positive P Q hdegree hcap S N hz hd later hroom H hN)) r w,
      w.length=SquareSampleCompleteVertices.width
        (IntegralFramedPhysicalSquare.input P D H L F C hs (IntegralFramedPhysicalSourcePrelude.key N)
          (positive P Q hdegree hcap S N hz hd later hroom H hN)) r ∧
      ∀i : Fin ((family P D H).birth (IntegralFramedPhysicalSourcePrelude.key N r)),
        IntegralFramedPhysicalSquare.point P D H L F C hs (IntegralFramedPhysicalSourcePrelude.key N)
          (positive P Q hdegree hcap S N hz hd later hroom H hN) r w hw i=values (N r-1-i.val) :=by
  let key:=IntegralFramedPhysicalSourcePrelude.key N r
  let root:=pairFst key
  let x:=initial P D root
  let hq:=fun r=>(initial P D r).critical_cap
  have HK : root=r:=IntegralFramedPhysicalSourcePrelude.key_root N r
  have HR : ∀j<N root,(S.polynomial (pair root (BinaryNatCode.encode j))).eval₂
      (Int.castRingHom ℝ) (values j)=0 :=by simpa only [HK] using hr
  let I:=IntegralMixedSourceIntegerPrelude.plan P Q hdegree hcap S N hz hd
    (IntegralMixedSourceIntegerPrelude.prelude_room P N later hroom)
  have HE : commands P D key=I.rules root:=
    IntegralMixedSourceIntegerPrelude.extended_commands_key P Q hdegree hcap S N hz hd later hroom r []
  have HL : (I.rules root).length=N root:=
    IntegralMixedSourceIntegerPrelude.commands_length _ _ _ _ _ _ _ _
  have HC : (I.rules root).length≤P.cap root+1+1:=by
    rw [HL]
    have HC:=hroom root
    omega
  have HC' : (commands P D key).length≤P.cap root+1+1:=by rw [HE]; exact HC
  have HRuns : IntegralMixedIntegerRealization.Realizes (IntegralMixedFramedHistoryScript.run x (I.rules root) HC)
      (fun i=>values (N root-1-i)):=
    IntegralMixedSourceIntegerPrelude.realizes P Q hq S N hz hd root x (fun i : Fin 0=>Fin.elim0 i)
      (fun i=>Fin.elim0 i) HC values HR
  have HRun:=run_realizes_eq x _ _ HE HC' HC _ HRuns
  have HState : IntegralMixedIntegerRealization.Realizes ((family P D H).state key)
      (fun i=>values (N root-1-i)):=HRun
  obtain ⟨w,hw,hlen,hvalues⟩:=IntegralFramedPhysicalSquare.exists_realized P D H L F C hs
    (IntegralFramedPhysicalSourcePrelude.key N) (positive P Q hdegree hcap S N hz hd later hroom H hN)
    r (fun i=>values (N root-1-i)) HState
  refine ⟨w,hw,hlen,fun i=>(hvalues i).trans ?_⟩
  exact congrArg (fun a=>values (a-1-i.val)) (congrArg N HK)

end LeanCanny.Encoding.IntegralFramedPhysicalCausalPrelude
