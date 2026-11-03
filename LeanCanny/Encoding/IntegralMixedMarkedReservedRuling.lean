/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedReservedCutView
public import LeanCanny.Encoding.IntegralMixedReservedCutModuloInstruction
/-! # Actual original marked plans inherit the literal reserved cut ruling -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReservedRuling
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedCausalRecordBits
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
 IntegralMixedFramedNormalizationBits.requiredModulus
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B

theorem planData_eq :
    (⟨IntegralMixedMarkedReservedCutView.plan hn ht ha hR0,IntegralMixedMarkedReservedCutView.data hn ht ha hR0⟩ :
      (D : Plan P)×IntegralMixedFramedHistoryFamilyBits.Data P D)=⟨(B).plan,(B).data⟩:=rfl

attribute [local irreducible] IntegralMixedMarkedReservedParent.bank IntegralMixedSourceIntegerRecordAppend.plan
variable (key : List Bool) (codes : List (List Bool))
 (d : IntegralMixedCutRecordConstructor.Data
   ((IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters.ambient (pairFst key))
   (number n (pairFst key)+8+codes.length))
 (tag : Tag) (choice rawDegree : ℕ)
 (htable : IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode (codes++[d.code tag choice rawDegree]))
 (hk : prefixLength (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters key=number n (pairFst key)+8+codes.length)

include htable hk in
theorem ordinary
    (ho : IntegralMixedCutRecordConstructor.tagIndex tag<3) :
    IntegralMixedSelectedBadMembership.Ordinary ((family P (B).plan (B).data).rule key)
      ((family P (B).plan (B).data).kind key):=by
 have HV:=IntegralMixedReservedCutModuloInstruction.ordinary_at_parent P
   (fun root _=>IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.positive hn ht ha hR0)
   (fun root _=>IntegralMixedMarkedReservedCutView.degree hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0) (fun root=>number n root+8)
   (IntegralMixedMarkedReservedCutView.integerSource hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_nonzero hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_cap hn ht ha hR0) (IntegralMixedMarkedReservedCutView.room hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.data hn ht ha hR0) key codes d tag choice rawDegree htable hk ho
 have HP:=IntegralMixedReservedCutModuloInstruction.selected_ordinary P
   (IntegralMixedMarkedReservedCutView.plan hn ht ha hR0) (IntegralMixedMarkedReservedCutView.data hn ht ha hR0) key HV
 exact (congrArg (fun dh : (D : Plan P)×IntegralMixedFramedHistoryFamilyBits.Data P D=>
   IntegralMixedSelectedBadMembership.Ordinary ((family P dh.1 dh.2).rule key) ((family P dh.1 dh.2).kind key))
     (planData_eq hn ht ha hR0)).mp HP

include htable hk in
theorem rule_eq : (family P (B).plan (B).data).rule key=
    d.rule (commonDenominator (IntegralMixedFramedFamilyRunView.stateView P (B).plan (B).data key))
      (commonDenominator_ne_zero (IntegralMixedFramedFamilyRunView.stateView P (B).plan (B).data key)):=by
 have HP:=IntegralMixedReservedCutModuloInstruction.rule_at_parent P
   (fun root _=>IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.positive hn ht ha hR0)
   (fun root _=>IntegralMixedMarkedReservedCutView.degree hn ht ha hR0 root)
   (IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0) (fun root=>number n root+8)
   (IntegralMixedMarkedReservedCutView.integerSource hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_nonzero hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.integer_cap hn ht ha hR0) (IntegralMixedMarkedReservedCutView.room hn ht ha hR0)
   (IntegralMixedMarkedReservedCutView.data hn ht ha hR0) key codes d tag choice rawDegree htable hk
 exact (congrArg (fun dh : (D : Plan P)×IntegralMixedFramedHistoryFamilyBits.Data P D=>
   (family P dh.1 dh.2).rule key=d.rule
     (commonDenominator (IntegralMixedFramedFamilyRunView.stateView P dh.1 dh.2 key))
     (commonDenominator_ne_zero (IntegralMixedFramedFamilyRunView.stateView P dh.1 dh.2 key)))
       (planData_eq hn ht ha hR0)).mp HP

end LeanCanny.Encoding.IntegralMixedMarkedReservedRuling
