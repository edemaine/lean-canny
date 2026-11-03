/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedReservedParent
public import LeanCanny.Encoding.IntegralMixedReservedCutActualVertex
public import LeanCanny.Encoding.IntegralMixedPhysicalCutStrictMargin
/-! # Typed original-source view of the actual marked reserved-cut frontend -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReservedCutView
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
 IntegralMixedAuxiliaryMarkedIntegerPlan.seed IntegralMixedAuxiliaryMarkedRecordPlan.factor
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B

noncomputable def spatial (root : List Bool) : SpatialSource ((P).ambient root):=
 IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root

theorem positive (root : List Bool) : 0<(P).ambient root:=IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha root

theorem degree (root : List Bool) : (spatial hn ht ha hR0 root).degree=(P).degree root:=
 IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) root

theorem ambient_eq : (P).ambient=(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).ambient:=rfl

theorem degree_eq : (P).degree=(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).degree:=rfl

theorem width_eq : (P).width=(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).width:=rfl

theorem scalar_cap (root : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient root+1) ((P).degree root)≤2^(P).width root:=by
 rw [ambient_eq hn ht ha hR0,degree_eq hn ht ha hR0,width_eq hn ht ha hR0]
 exact IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap (n:=n) (t:=t) hn ht ha root

noncomputable def integerSource (_hR0 : BinaryFn R0) : IntegerPolynomialRootQueriesBits.Source:=
 IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (radius R0)

theorem integer_nonzero (q : List Bool) : (integerSource hn ht ha hR0).polynomial q≠0:=
 IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha (radius R0) q

theorem integer_cap (root : List Bool) (i : ℕ) :
    (integerSource hn ht ha hR0).degree (pair root (BinaryNatCode.encode i))≤2^(P).width root:=
 by
 rw [width_eq hn ht ha hR0]
 exact IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha (radius R0) root i

theorem room (root : List Bool) :
    IntegralMixedCausalRecordPlanBits.count root+(number n root+8)+2≤(P).cap root+1:=
 IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha root

noncomputable def plan : Plan P:=IntegralMixedSourceIntegerRecordAppend.plan P
 (fun root _=>spatial hn ht ha hR0 root) (positive hn ht ha hR0) (fun root _=>degree hn ht ha hR0 root)
 (scalar_cap hn ht ha hR0) (fun root=>number n root+8) (integerSource hn ht ha hR0)
 (integer_nonzero hn ht ha hR0) (integer_cap hn ht ha hR0) (room hn ht ha hR0)

theorem plan_eq : plan hn ht ha hR0=(B).plan:=rfl

noncomputable abbrev data : IntegralMixedFramedHistoryFamilyBits.Data P (plan hn ht ha hR0):=(B).data

noncomputable abbrev bounds : IntegralMixedFramedStepHeight.FamilyInputs P (plan hn ht ha hR0) (B).nodes (B).factor (B).seed:=(B).bounds

attribute [local irreducible] IntegralMixedMarkedReservedParent.bank

theorem state_realizes (key : List Bool) (v : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.stateView P (B).plan (B).data key) v) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.stateView P (plan hn ht ha hR0) (data hn ht ha hR0) key) v:=by
 simpa only [plan_eq] using hv

theorem full_realizes (root : List Bool) (v : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedHistoryScript.run (initial P (plan hn ht ha hR0) root)
        ((plan hn ht ha hR0).rules root) (by have HH:=(plan hn ht ha hR0).room root;omega)) v) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedHistoryScript.run (initial P (B).plan root)
        ((B).plan.rules root) (by have HH:=(B).plan.room root;omega)) v:=by
 simpa only [plan_eq] using hv

theorem strict_margin (root : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient root+1) ((P).degree root)<2^(P).width root:=
 by
 rw [ambient_eq hn ht ha hR0,degree_eq hn ht ha hR0,width_eq hn ht ha hR0]
 exact IntegralMixedPhysicalCutStrictMargin.source_cap_lt (fun c=>number n c+3)
   (IntegralMixedAuxiliaryMarkedIntegerPlan.degree t) (IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound hn ht ha)
   (fun c=>number n c+8+IntegralMixedCausalRecordPlanBits.count c) root

end LeanCanny.Encoding.IntegralMixedMarkedReservedCutView
