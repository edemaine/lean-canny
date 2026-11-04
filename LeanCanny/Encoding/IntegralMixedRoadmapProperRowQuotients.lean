/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowFields
public import LeanCanny.Encoding.IntegralMixedRoadmapProperInputComposition
public import LeanCanny.Encoding.IntegralMixedPhysicalCutParentPoint
/-! # The actual statistic hom reads its own native parent bank values -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (family commands prefixLength keyAt)
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "D"=>IntegralFramedBankQuery.Bank.plan BK
local notation "H"=>IntegralFramedBankQuery.Bank.data BK
local notation "L"=>IntegralFramedBankQuery.Bank.nodes BK
local notation "F"=>IntegralFramedBankQuery.Bank.factor BK
local notation "C"=>IntegralFramedBankQuery.Bank.seed BK
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds BK
local notation "G"=>family P D H
local notation "I"=>IntegralFramedPhysicalSquare.input P D H L F C hs
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank dimension initial creating parentKey

private theorem terminal_root (mean : Bool) (z : List Bool) :
    pairFst (terminal hn ht ha hR0 mean z)=root hn ht ha hR0 mean z:=
  IntegralMixedPhysicalMarkedPlan.key_root hn ht ha (radius_binary hR0) false _

private theorem parent_observation (mean : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z)) :
    IntegralFramedPhysicalScalarObservation.atKeyObservation P D (parentKey hn ht ha hR0 mean z)=
      IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (root hn ht ha hR0 mean z)
        (IntegralMixedCausalRecordPlanBits.count (root hn ht ha hR0 mean z)-1) (Nat.sub_le _ _):=by
  have HC:=row_count_positive hn ht ha hR0 z hv
  let r:=root hn ht ha hR0 mean z
  let m:=creating hn ht ha hR0 z
  let j:=IntegralMixedCausalRecordPlanBits.count r-1
  have HM : m=number n r+8+j:=by
    dsimp only [r,j,m]
    rw [root_count hn ht ha hR0 mean z HC,root_number hn ht ha hR0 mean z]
    unfold creating IntegralMixedRoadmapBadProbePacket.creating
    omega
  have HB : m≤(P).cap r+1:=creating_bound hn ht ha hR0 mean z HC
  have HB' : number n r+8+j≤(P).cap r+1:=HM ▸ HB
  have HAt:=IntegralFramedPhysicalScalarObservation.observation_keyAt P D r m (BinaryNatCode.encode 2) HB
  have HChange:=IntegralFramedPhysicalPrefixObservation.at_congr P D r r m (number n r+8+j) HB HB' rfl HM
  have HView:=IntegralMixedPhysicalCutParentPoint.observation_view hn ht ha hR0 r j (Nat.sub_le _ _)
  exact (congrArg (IntegralFramedPhysicalScalarObservation.atKeyObservation P D)
    (parentKey_aux hn ht ha hR0 mean z hv)).trans (HAt.trans (HChange.trans HView))

theorem statistic_parent_quotients (mean : Bool) (z w : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (hw : SquareSampleCompleteVertices.Valid (I (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean)) z w)
    (hfit : (G).birth (parentKey hn ht ha hR0 mean z)≤(G).birth (terminal hn ht ha hR0 mean z))
    (φ : (IntegralMixedCutSource.Family.state G (parentKey hn ht ha hR0 mean z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ ((IntegralMixedCutSource.Family.state G (parentKey hn ht ha hR0 mean z)).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H L F C hs (terminal hn ht ha hR0 mean)
        (positive hn ht ha hR0 mean) z w hw (UniformIntegralPowerSchedule.embed hfit i)^
          UniformIntegralPowerSchedule.weights ((G).cap (parentKey hn ht ha hR0 mean z))
            (2^(G).width (parentKey hn ht ha hR0 mean z)) ((G).birth (parentKey hn ht ha hR0 mean z)) i) :
    ∀i : Fin (commands P D (parentKey hn ht ha hR0 mean z)).length,
      φ ((IntegralMixedCutSource.Family.state G (parentKey hn ht ha hR0 mean z)).bank.numerator i)/
        ((IntegralMixedCutSource.Family.state G (parentKey hn ht ha hR0 mean z)).bank.denominator i:ℝ)=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (root hn ht ha hR0 mean z) w
        ((valid_at_context hn ht ha hR0 mean z w).mp hw) i.val :=by
  intro i
  let old:=parentKey hn ht ha hR0 mean z
  have HC : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z) :=row_count_positive hn ht ha hR0 z hv
  have HM : (G).birth old=creating hn ht ha hR0 z:=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H old).trans (parentKey_prefix hn ht ha hR0 mean z HC)
  have HF : creating hn ht ha hR0 z≤prefixLength P (terminal hn ht ha hR0 mean z):=
    HM.symm.trans_le (hfit.trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _))
  have HE : old=keyAt (pairFst (terminal hn ht ha hR0 mean z)) (creating hn ht ha hR0 z) (BinaryNatCode.encode 2):=by
    rw [terminal_root]
    exact parentKey_aux hn ht ha hR0 mean z hv
  have HQ:=IntegralFramedPhysicalScalarObservation.quotient_prefix_at P D H L F C hs
    (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean) z w hw old
    (creating hn ht ha hR0 z) HF (BinaryNatCode.encode 2) HE hfit φ hφ
  have HO:=parent_observation hn ht ha hR0 mean z hv
  have HN:=natural_at_context hn ht ha hR0 mean z w hw ((valid_at_context hn ht ha hR0 mean z w).mp hw)
  exact (HQ i).trans ((congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point
    (IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs (terminal hn ht ha hR0 mean)
      (positive hn ht ha hR0 mean) z w hw) i.val) HO).trans
        (congrArg (fun a : ℕ→ℝ=>(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0
          (root hn ht ha hR0 mean z) (IntegralMixedCausalRecordPlanBits.count (root hn ht ha hR0 mean z)-1)
          (Nat.sub_le _ _)).point a i.val) HN))

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
