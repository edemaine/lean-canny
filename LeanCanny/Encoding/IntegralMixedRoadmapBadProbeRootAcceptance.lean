/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbePresence
public import LeanCanny.Algebra.IntegralMixedCutCreationInstruction
/-! # A full chosen-factor receipt yields the actual native reverse guards -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeRootAcceptance
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedRoadmapBadProbePacket IntegralMixedFramedHistoryFamilyBits
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralFramedPhysicalSquare.input
 IntegralFramedPhysicalSquare.point IntegralMixedPhysicalCutOpenInterval.parent IntegralMixedVirtualTaskBits.saved
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
local notation "ctx"=>IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0)
local notation "EP"=>IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha (radius_binary hR0) false
variable (z w : List Bool)
 (hh : HintGood (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
   (IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0) z) w)
 (hb : IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha (radius_binary hR0) false
   (pair (IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0) z) w))
local notation "old"=>IntegralMixedVirtualTaskBits.saved P
 (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha (radius_binary hR0) false (ctx z))
local notation "hl"=>IntegralMixedPhysicalCutOrderedInterval.left_bound hn ht ha (radius_binary hR0) false (ctx z) w hb
local notation "hr"=>IntegralMixedPhysicalCutOrderedInterval.right_bound hn ht ha (radius_binary hR0) false (ctx z) w hb

include hh in
theorem accepted (a : ℝ)
    (ha' : a∈Set.Ioo (EP false (ctx z) w hv hl) (EP true (ctx z) w hv hr))
    (hroot : (IntegralMixedCutCreationReceipt.native P D H old).HasRoot
      (IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (pairFst (ctx z)) w
        (IntegralMixedPhysicalCutParentPoint.empty_valid hn ht ha hR0 (ctx z) w hv)) a) :
    IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha (radius_binary hR0) false (pair (ctx z) w) ∧
      pair (ctx z) w∉IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha (radius_binary hR0) false:=by
 obtain ⟨φ,hφ,HV,HD,HRoot⟩:=(IntegralMixedCutCreationReceipt.native_root_iff P D H old _ _).mp hroot
 obtain ⟨ψ,hψ,_⟩:=IntegralMixedPhysicalCutLocalInterpretation.coefficient_evaluation hn ht ha (radius_binary hR0) false (ctx z) w hv hb
 have HC :0<IntegralMixedCausalRecordPlanBits.count (pairFst (ctx z)):=by
   rw [IntegralMixedRoadmapBadProbeProvenance.context_root hn ht ha hR0 z,prepared_count _ z hh.1]
   exact hh.1
 have Hψ:=IntegralMixedPhysicalCutParentPoint.quotients hn ht ha hR0 (ctx z) w hv hb HC
   (IntegralMixedRoadmapBadProbeProvenance.last_birth hn ht ha hR0 z hh) ψ
   (IntegralMixedPhysicalCutCoefficientComplete.full_tail hn ht ha (radius_binary hR0) false (ctx z) w hv hb ψ hψ)
 have HE :φ=ψ:=IntegralMixedBankValueInterpretation.hom_ext ((G).state old) (family_canonical P D H old)
   φ ψ (fun i=>(hφ i).trans (Hψ i).symm)
 subst φ
 have HG:=(IntegralMixedPhysicalCutCoefficientComplete.guards_iff_valid_degree hn ht ha (radius_binary hR0) false
   (ctx z) w hv hb ψ hψ).mpr ⟨HV,HD⟩
 refine ⟨HG,?_⟩
 have HI:=IntegralMixedPhysicalCutCoefficientComplete.empty_iff_at hn ht ha (radius_binary hR0) false
   (ctx z) w hv hb ψ hψ HV HD
 intro HEmpty
 have HR : (IntegralMixedFramedFullCutIntervalSelected.factor P D H
     (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha (radius_binary hR0) false) (ctx z) ψ).eval a=0:=by
   simpa only [IntegralMixedFramedFullCutIntervalSelected.factor,IntegralMixedFramedFullCutHead.saved,Polynomial.eval_map] using HRoot
 exact ((HI.mp HEmpty).2 a HR) ha'

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeRootAcceptance
