/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedReservedParent
public import LeanCanny.Encoding.IntegralMixedRoadmapChainAppend
/-! # One full word realizes any unchanged original prefix at its new root

The root, total raw count and chronological bytes determine the actual
prefix rows. The full word is used only at its original sampler. Its one
natural raw tuple transfers to the new prefix before fresh sampling.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (prefixLength keyAt)
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "context"=>IntegralMixedMarkedReservedParent.context
local notation "bound"=>IntegralMixedMarkedReservedParent.bound hn ht ha hR0
local notation "view"=>IntegralMixedMarkedReservedParent.observation_view hn ht ha hR0
attribute [local irreducible] IntegralMixedMarkedReservedParent.bank

theorem fit (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    number n root+8+j≤prefixLength P ((B).key (context root)) :=by
  rw [IntegralMixedMarkedReservedParent.full_prefix hn ht ha hR0,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
  omega

variable (base w : List Bool) (hv : SquareSampleCompleteVertices.Valid
  (IntegralMixedMarkedReservedParent.input hn ht ha hR0) (context base) w)
noncomputable def tuple : ℕ→ℝ:=IntegralFramedPhysicalPrefixObservation.tuple P D H
  (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive (context base) w hv
noncomputable def values (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count base) : ℕ→ℝ:=
  (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 base j hj).point
    (tuple hn ht ha hR0 base w hv)

theorem base_roots (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count base) :
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 base j hj).Roots
      (tuple hn ht ha hR0 base w hv) :=by
  have HM:=fit hn ht ha hR0 base j hj
  have HR:=IntegralFramedPhysicalPrefixObservation.roots P D H (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (context base) w hv (number n base+8+j) HM
  have HE:=IntegralFramedPhysicalPrefixObservation.at_congr P D
    (pairFst ((B).key (context base))) base (number n base+8+j) (number n base+8+j)
    (HM.trans (min_le_right _ _)) (bound base j hj)
    (IntegralMixedMarkedReservedParent.key_root hn ht ha hR0 base) rfl
  exact (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots
    (tuple hn ht ha hR0 base w hv)) (HE.trans (view base j hj))).mp HR

theorem transfer_realizes (root : List Bool) (hc : candidate base=candidate root)
    (hcount : IntegralMixedCausalRecordPlanBits.count base=IntegralMixedCausalRecordPlanBits.count root)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count base)
    (hcode : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code base i=IntegralMixedCausalRecordPlanBits.code root i) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.runAt P D root (number n root+8+j) (bound root j (hj.trans_eq hcount)))
      (values hn ht ha hR0 base w hv j hj) :=by
  have HE:=IntegralMixedMarkedPrefixObservation.eq hn ht ha hR0 base root hc hcount j hj hcode
  have HZ : (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j (hj.trans_eq hcount)).Roots
      (tuple hn ht ha hR0 base w hv):=
    (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots
      (tuple hn ht ha hR0 base w hv)) HE).mp (base_roots hn ht ha hR0 base w hv j hj)
  have HZ' : (IntegralFramedPhysicalPrefixObservation.atRoot P D root (number n root+8+j)
      (bound root j (hj.trans_eq hcount))).Roots (tuple hn ht ha hR0 base w hv):=
    (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots
      (tuple hn ht ha hR0 base w hv)) (view root j (hj.trans_eq hcount))).mpr HZ
  have HR:=IntegralFramedPhysicalPrefixObservation.at_realizes P D root (number n root+8+j)
    (bound root j (hj.trans_eq hcount)) (tuple hn ht ha hR0 base w hv) HZ'
  have HP:=congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point
    (tuple hn ht ha hR0 base w hv)) ((view root j (hj.trans_eq hcount)).trans HE.symm)
  exact (congrArg (fun v : ℕ→ℝ=>IntegralMixedIntegerRealization.Realizes
    (IntegralMixedFramedFamilyRunView.runAt P D root (number n root+8+j) (bound root j (hj.trans_eq hcount))) v) HP).mp HR

theorem transfer_canonical_realizes (root aux : List Bool) (hc : candidate base=candidate root)
    (hcount : IntegralMixedCausalRecordPlanBits.count base=IntegralMixedCausalRecordPlanBits.count root)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count base)
    (hcode : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code base i=IntegralMixedCausalRecordPlanBits.code root i) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.stateView P D H (keyAt root (number n root+8+j) aux))
      (values hn ht ha hR0 base w hv j hj) :=
  (IntegralMixedSourceIntegerPaddingRealization.realizes_at_key_iff P D H root aux _
    (bound root j (hj.trans_eq hcount)) _).mpr
      (transfer_realizes hn ht ha hR0 base w hv root hc hcount j hj hcode)

def chainRoot (c q : List Bool):=pair c (pair (IntegralMixedRoadmapChain.raw q) [])
theorem chainRoot_count (c q : List Bool) :
    IntegralMixedCausalRecordPlanBits.count (chainRoot c q)=WordListRecords.count (IntegralMixedRoadmapChain.raw q) :=by
  simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,chainRoot,pairFst_pair,pairSnd_pair]
theorem chainRoot_code (c q : List Bool) (i : ℕ) :
    IntegralMixedCausalRecordPlanBits.code (chainRoot c q) i=WordList.get (IntegralMixedRoadmapChain.raw q) i :=by
  simp only [IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,chainRoot,pairFst_pair,pairSnd_pair]

theorem chain_prefix_good {dim scalar sourceCap initial budget : ℕ} {q : List Bool}
    (hq : IntegralMixedRoadmapChain.Checked dim scalar sourceCap initial budget q) (c : List Bool) :
    IntegralMixedRoadmapChain.rawStart dim q (IntegralMixedRoadmapChain.depth q)≤
      IntegralMixedCausalRecordPlanBits.count (chainRoot c q) :=by
  rw [chainRoot_count,hq.2.2.2.2.2.2.1]
  have HH:=IntegralMixedRoadmapChain.rawStart_bound dim q (IntegralMixedRoadmapChain.depth q) (by have :=hq.1;omega)
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  omega

theorem appended_parent_realizes {dim scalar sourceCap initial budget : ℕ} {q : List Bool}
    (hq : IntegralMixedRoadmapChain.Checked dim scalar sourceCap initial budget q)
    (c l r : List Bool) (s : Bool) (p w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (context (chainRoot c q)) w)
    (hd : IntegralMixedRoadmapChain.depth q<dim)
    (hnew : IntegralMixedRoadmapLevel.Good dim scalar sourceCap
      (IntegralMixedRoadmapChain.birth dim initial q (IntegralMixedRoadmapChain.depth q))
      (IntegralMixedRoadmapLevel.packet (IntegralMixedRoadmapChain.frozen q (IntegralMixedRoadmapChain.depth q)) l r s []))
    (hp : p.length≤IntegralMixedRoadmapRecordChain.codeBound dim initial budget) (aux : List Bool) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.stateView P D H
        (keyAt (chainRoot c (IntegralMixedRoadmapChain.appendPayload dim q l r s p))
          (number n (chainRoot c (IntegralMixedRoadmapChain.appendPayload dim q l r s p))+8+
            IntegralMixedRoadmapChain.rawStart dim q (IntegralMixedRoadmapChain.depth q)) aux))
      (values hn ht ha hR0 (chainRoot c q) w hv
        (IntegralMixedRoadmapChain.rawStart dim q (IntegralMixedRoadmapChain.depth q)) (chain_prefix_good hq c)) :=by
  have Hnext:=IntegralMixedRoadmapChain.append_checked hq l r s p hd hnew hp
  apply transfer_canonical_realizes hn ht ha hR0 (chainRoot c q) w hv _ aux ?_ ?_
    (IntegralMixedRoadmapChain.rawStart dim q (IntegralMixedRoadmapChain.depth q)) (chain_prefix_good hq c) ?_
  · simp only [candidate,chainRoot,pairFst_pair]
  · rw [chainRoot_count,chainRoot_count,hq.2.2.2.2.2.2.1,Hnext.2.2.2.2.2.2.1]
  · intro i hi
    rw [chainRoot_code,chainRoot_code]
    exact (IntegralMixedRoadmapChain.append_raw_before hq l r s p i hi).symm

end LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer
