/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarObservation
public import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientPresence
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedContext
/-! # A reserved last-cut interpretation reads the actual native parent point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutParentPoint
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family prefixLength keyAt)
open IntegralMixedPhysicalCutOpenInterval (parent Bounds birthWord)
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
 IntegralMixedFramedNormalizationBits.requiredModulus
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H

theorem observation_view (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    IntegralFramedPhysicalPrefixObservation.atRoot P D root (number n root+8+j)
      (IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 root j hj)=
      IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj:=rfl

private theorem cap_eq (A : Parameters) (E : Plan A) (J : IntegralMixedFramedHistoryFamilyBits.Data A E) (key : List Bool) :
    (family A E J).cap key=A.cap (pairFst key)+1:=rfl

private theorem prefix_bound (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    number n root+8+j≤(P).cap root+1:=
 IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 root j hj

attribute [local irreducible] bank IntegralMixedPhysicalCutOpenInterval.parent IntegralMixedVirtualTaskBits.saved
 IntegralFramedPhysicalSquare.input IntegralFramedPhysicalSquare.point IntegralFramedPhysicalSquare.scalarTuple
variable (q w : List Bool)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false) q w)
 (hb : Bounds hn ht ha (radius_binary hR0) false (pair q w))
local notation "old"=>IntegralMixedVirtualTaskBits.saved P (parent hn ht ha (radius_binary hR0) false q)

include hv in
theorem empty_valid :SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
    (IntegralMixedMarkedPrefixFieldReadback.context (pairFst q)) w:=
 (IntegralMixedPhysicalMarkedContext.valid_iff hn ht ha (radius_binary hR0) q
   (IntegralMixedMarkedPrefixFieldReadback.context (pairFst q)) w (pairFst_pair _ _).symm).mp hv

include hb in
theorem observation_parent
    (hc : 0<IntegralMixedCausalRecordPlanBits.count (pairFst q))
    (hlast : (birthWord q).length+1=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst q)) :
    IntegralFramedPhysicalScalarObservation.atKeyObservation P D old=
      IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (pairFst q)
        (IntegralMixedCausalRecordPlanBits.count (pairFst q)-1) (Nat.sub_le _ _):=by
 have HK:=IntegralMixedPhysicalCutLocalInterpretation.parent_saved hn ht ha (radius_binary hR0) false q w hb
 have HM :(birthWord q).length=number n (pairFst q)+8+(IntegralMixedCausalRecordPlanBits.count (pairFst q)-1):=by
   unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount at hlast
   omega
 have HH:=IntegralMixedPhysicalCutLocalInterpretation.stage_bound hn ht ha (radius_binary hR0) false q w hb
 have H0:=congrArg (IntegralFramedPhysicalScalarObservation.atKeyObservation P D) HK
 have H1:=IntegralFramedPhysicalScalarObservation.observation_keyAt P D (pairFst q) (birthWord q).length
   (BinaryNatCode.encode 2) HH
 have H2:=IntegralFramedPhysicalPrefixObservation.at_congr P D (pairFst q) (pairFst q) _ _ HH
   (prefix_bound hn ht ha hR0 (pairFst q) (IntegralMixedCausalRecordPlanBits.count (pairFst q)-1) (Nat.sub_le _ _)) rfl HM
 exact H0.trans (H1.trans (H2.trans (observation_view hn ht ha hR0 _ _ (Nat.sub_le _ _))))

theorem quotients
    (hc : 0<IntegralMixedCausalRecordPlanBits.count (pairFst q))
    (hlast : (birthWord q).length+1=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst q))
    (φ : ((G).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : IntegralMixedPhysicalCutCoefficientPresence.FullTail hn ht ha (radius_binary hR0) false q w hv hb φ) :
    ∀i : Fin (IntegralMixedFramedHistoryFamilyBits.commands P D old).length,
      φ (((G).state old).bank.numerator i)/(((G).state old).bank.denominator i:ℝ)=
        IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (pairFst q) w
          (empty_valid hn ht ha hR0 q w hv) i.val:=by
 have HR:=IntegralMixedPhysicalCutLocalInterpretation.key_root hn ht ha (radius_binary hR0) false q
 have HE :old=keyAt (pairFst ((B).key q)) (birthWord q).length (BinaryNatCode.encode 2):=
   (IntegralMixedPhysicalCutLocalInterpretation.parent_saved hn ht ha (radius_binary hR0) false q w hb).trans
     (congrArg (fun r=>keyAt r (birthWord q).length (BinaryNatCode.encode 2)) HR.symm)
 have HM :(birthWord q).length≤prefixLength P ((B).key q):=by
   exact (IntegralMixedPhysicalCutLocalInterpretation.parent_birth hn ht ha (radius_binary hR0) false q w hb).symm.trans_le
     ((IntegralMixedPhysicalCutLocalInterpretation.fits hn ht ha (radius_binary hR0) false q w hb).trans_eq
       (IntegralMixedFramedHistoryFamilyBits.family_birth P D H ((B).key q)))
 have HGen :∀i,φ (((G).state old).sampler.scalarPrefix.basis.generator i)=
     IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive q w hv
       (UniformIntegralPowerSchedule.embed (IntegralMixedPhysicalCutLocalInterpretation.fits hn ht ha (radius_binary hR0) false q w hb) i)^
       UniformIntegralPowerSchedule.weights ((G).cap old) (2^(G).width old) ((G).birth old) i:=by
   simpa only [IntegralMixedPhysicalCutCoefficientPresence.FullTail,cap_eq] using hφ
 have HV:=IntegralFramedPhysicalScalarObservation.quotient_prefix_at P D H (B).nodes (B).factor (B).seed (B).bounds
   (B).key (B).positive q w hv old (birthWord q).length HM (BinaryNatCode.encode 2) HE
   (IntegralMixedPhysicalCutLocalInterpretation.fits hn ht ha (radius_binary hR0) false q w hb) φ HGen
 have HO:=observation_parent hn ht ha hR0 q w hb hc hlast
 have HZ:=IntegralMixedPhysicalMarkedContext.natural_eq hn ht ha (radius_binary hR0) q
   (IntegralMixedMarkedPrefixFieldReadback.context (pairFst q)) w (pairFst_pair _ _).symm hv (empty_valid hn ht ha hR0 q w hv)
 intro i
 exact (HV i).trans ((congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point
   (IntegralFramedPhysicalSquare.naturalPoint P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive q w hv) i.val) HO).trans
     (congrArg (fun z : ℕ→ℝ=>(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (pairFst q)
       (IntegralMixedCausalRecordPlanBits.count (pairFst q)-1) (Nat.sub_le _ _)).point z i.val) HZ))

end LeanCanny.Encoding.IntegralMixedPhysicalCutParentPoint
