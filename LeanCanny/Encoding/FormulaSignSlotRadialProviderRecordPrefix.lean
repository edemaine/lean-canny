/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordReceipt
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrelude
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshot
public import LeanCanny.Encoding.IntegralFramedPhysicalPrefixObservation
/-! # Literal provider prefixes preserve the full coefficient state -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "RP" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "count" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "records" => FormulaSignSlotRadialProviderRecordReceipt.records
local notation "provider" => FormulaSignSlotRadialProviderRecordPlan.providerContext
attribute [local irreducible] FormulaSignSlotRadialProviderIntegerSource.degreeBound
  FormulaSignSlotRadialExternalPrelude.spatial FormulaSignSlotRadialProviderIntegerSource.source

theorem ambient (a b : List Bool) (hp : provider a=provider b) : (P).ambient a=(P).ambient b := by
  change FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient (provider a)=
    FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient (provider b)
  rw [hp]
theorem width (a b : List Bool) (hp : provider a=provider b) : (P).width a=(P).width b := by
  let f (c : List Bool) := (IntegralMixedExceptionalBounds.auxiliaryCap
    (FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient c+1)
    (FormulaSignSlotRadialProviderIntegerPlan.parameters.degree c)+
    FormulaSignSlotRadialProviderIntegerPlan.degreeBound c).size
  change f (provider a)=f (provider b)
  exact congrArg f hp
theorem count_eq (a b : List Bool) (hp : provider a=provider b) : count a=count b := by
  unfold FormulaSignSlotRadialProviderRecordPlan.count
  rw [hp]
theorem cap (a b : List Bool) (hp : provider a=provider b)
    (hc : IntegralMixedCausalRecordPlanBits.count a=IntegralMixedCausalRecordPlanBits.count b) :
    (P).cap a=(P).cap b := by
  change count a+IntegralMixedCausalRecordPlanBits.count a+2=count b+IntegralMixedCausalRecordPlanBits.count b+2
  rw [count_eq a b hp,hc]

private theorem source_congr {a b : List Bool} (hp : a=b) :
    HEq (FormulaSignSlotRadialProviderIntegerPlan.spatial a)
      (FormulaSignSlotRadialProviderIntegerPlan.spatial b) := by
  subst b
  rfl

theorem source_heq (a b : List Bool) (hp : provider a=provider b) :
    HEq (FormulaSignSlotRadialProviderRecordPlan.spatial a) (FormulaSignSlotRadialProviderRecordPlan.spatial b) := by
  change HEq (FormulaSignSlotRadialProviderIntegerPlan.spatial (provider a))
    (FormulaSignSlotRadialProviderIntegerPlan.spatial (provider b))
  exact source_congr hp

private theorem base_heq {n m S T B C : ℕ} (Q : SpatialSource n) (Q' : SpatialSource m)
    (hQ : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (hQ' : PurePowerReductionBounds.dimension (m+1) Q'.degree≤2^C)
    (en : n=m) (eS : S=T) (eB : B=C) (eQ : HEq Q Q') :
    HEq (IntegralMixedHistory.base Q (IntegralHistorySampler.base S (2^B)) hQ)
      (IntegralMixedHistory.base Q' (IntegralHistorySampler.base T (2^C)) hQ') := by
  subst m
  subst T
  subst C
  cases eq_of_heq eQ
  rfl

theorem initial_heq (a b : List Bool) (hp : provider a=provider b)
    (hc : IntegralMixedCausalRecordPlanBits.count a=IntegralMixedCausalRecordPlanBits.count b) :
    HEq (initial P D a) (initial P D b) := by
  change HEq (IntegralMixedHistory.base (FormulaSignSlotRadialProviderRecordPlan.spatial a)
    (IntegralHistorySampler.base ((P).cap a+1) (2^(P).width a)) _)
    (IntegralMixedHistory.base (FormulaSignSlotRadialProviderRecordPlan.spatial b)
    (IntegralHistorySampler.base ((P).cap b+1) (2^(P).width b)) _)
  exact base_heq _ _ _ _ (ambient a b hp) (congrArg (·+1) (cap a b hp hc))
    (width a b hp) (source_heq a b hp)

theorem polynomial_eq (a b : List Bool) (hp : provider a=provider b) (i : ℕ) :
    FormulaSignSlotRadialProviderRecordReceipt.polynomial a i=
      FormulaSignSlotRadialProviderRecordReceipt.polynomial b i := by
  unfold FormulaSignSlotRadialProviderRecordReceipt.polynomial
  rw [FormulaSignSlotRadialProviderRecordPlan.source_polynomial_packet,
    FormulaSignSlotRadialProviderRecordPlan.source_polynomial_packet,hp]

theorem prefix_heq (a b : List Bool) (hp : provider a=provider b)
    (hc : IntegralMixedCausalRecordPlanBits.count a=IntegralMixedCausalRecordPlanBits.count b)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count a)
    (hw : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code a i=IntegralMixedCausalRecordPlanBits.code b i) :
    HEq ((records a).reverse.take (count a+j)) ((records b).reverse.take (count b+j)) := by
  unfold FormulaSignSlotRadialProviderRecordReceipt.records
  apply IntegralMixedStaticRecordPrefix.prefix_heq
  · exact hj
  · exact ambient a b hp
  · exact width a b hp
  · exact count_eq a b hp
  · exact hc
  · exact source_heq a b hp
  · exact polynomial_eq a b hp
  · exact hw

theorem bound (a : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count a) :
    count a+j≤(P).cap a+1 := by
  change _≤count a+IntegralMixedCausalRecordPlanBits.count a+2+1
  omega

noncomputable def snapshot (a : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count a) :=
  IntegralMixedPrefixSnapshot.ofCommands (initial P D a)
    (paddedPast (defaultInstruction P D a) ((D).rules a) (count a+j))
    (by rw [paddedPast_length]; exact (bound a j hj).trans (Nat.le_succ _))

private theorem snapshot_commands {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    IntegralMixedPrefixSnapshot.ofCommands x cs hc=IntegralMixedPrefixSnapshot.ofCommands x ds hd := by
  cases he
  rfl

theorem initial_source (a : List Bool) : (D).initialSource a=FormulaSignSlotRadialProviderRecordPlan.spatial a := rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.plan
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordReceipt.records
  snapshot

private theorem snapshot_factor (a : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count a) :
    snapshot a j hj=IntegralMixedPrefixSnapshot.ofCommands (initial P D a)
      (paddedPast (defaultInstruction P D a)
        (IntegralMixedCausalPlanBits.commands (initial P D a) (records a)
          (FormulaSignSlotRadialProviderRecordReceipt.room a)) (count a+j))
      (by rw [paddedPast_length]; exact (bound a j hj).trans (Nat.le_succ _)) := by
  unfold snapshot
  apply snapshot_commands
  exact congrArg (fun cs=>paddedPast (defaultInstruction P D a) cs (count a+j))
    (FormulaSignSlotRadialProviderRecordReceipt.rules a)

theorem snapshot_eq (a b : List Bool) (hp : provider a=provider b)
    (hc : IntegralMixedCausalRecordPlanBits.count a=IntegralMixedCausalRecordPlanBits.count b)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count a)
    (hw : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code a i=IntegralMixedCausalRecordPlanBits.code b i) :
    snapshot a j hj=snapshot b j (hj.trans_eq hc) := by
  rw [snapshot_factor a j hj,snapshot_factor b j (hj.trans_eq hc)]
  apply IntegralMixedPrefixSnapshot.prefix_congr
  · rw [FormulaSignSlotRadialProviderRecordReceipt.records_length]; omega
  · rw [FormulaSignSlotRadialProviderRecordReceipt.records_length]; omega
  · exact ambient a b hp
  · exact congrArg (·+1) (cap a b hp hc)
  · exact width a b hp
  · exact congrArg (·+j) (count_eq a b hp)
  · simpa only [initial_source] using source_heq a b hp
  · exact initial_heq a b hp hc
  · exact prefix_heq a b hp hc j hj hw

noncomputable def observation (a : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count a) :=
  IntegralFramedPhysicalPrefixObservation.atRoot P D a (count a+j) (bound a j hj)

private theorem observation_commands {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    IntegralMixedFramedRunObservation.ofCommands x cs hc=IntegralMixedFramedRunObservation.ofCommands x ds hd := by
  cases he
  rfl

private theorem observation_factor (a : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count a) :
    observation a j hj=IntegralMixedFramedRunObservation.ofCommands (initial P D a)
      (paddedPast (defaultInstruction P D a)
        (IntegralMixedCausalPlanBits.commands (initial P D a) (records a)
          (FormulaSignSlotRadialProviderRecordReceipt.room a)) (count a+j))
      (by rw [paddedPast_length]; exact (bound a j hj).trans (Nat.le_succ _)) := by
  unfold observation IntegralFramedPhysicalPrefixObservation.atRoot
  apply observation_commands
  exact congrArg (fun cs=>paddedPast (defaultInstruction P D a) cs (count a+j))
    (FormulaSignSlotRadialProviderRecordReceipt.rules a)

attribute [local irreducible] observation

theorem observation_eq (a b : List Bool) (hp : provider a=provider b)
    (hc : IntegralMixedCausalRecordPlanBits.count a=IntegralMixedCausalRecordPlanBits.count b)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count a)
    (hw : ∀i,i<j→IntegralMixedCausalRecordPlanBits.code a i=IntegralMixedCausalRecordPlanBits.code b i) :
    observation a j hj=observation b j (hj.trans_eq hc) := by
  rw [observation_factor a j hj,observation_factor b j (hj.trans_eq hc)]
  apply IntegralMixedFramedRunObservation.prefix_congr
  · rw [FormulaSignSlotRadialProviderRecordReceipt.records_length]; omega
  · rw [FormulaSignSlotRadialProviderRecordReceipt.records_length]; omega
  · exact ambient a b hp
  · exact congrArg (·+1) (cap a b hp hc)
  · exact width a b hp
  · exact congrArg (·+j) (count_eq a b hp)
  · simpa only [initial_source] using source_heq a b hp
  · exact initial_heq a b hp hc
  · exact prefix_heq a b hp hc j hj hw

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
