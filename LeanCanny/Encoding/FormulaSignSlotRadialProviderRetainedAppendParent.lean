/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPrefix
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixWord
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordContinuation
public import LeanCanny.Algebra.IntegralMixedFramedCompanionColumns
/-! # The new provider root receives its parent interpretation from the old word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial)
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "cap" => FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap

noncomputable def oldNatural (old : List Bool) (hv : A old) :=
  FormulaSignSlotRadialProviderRecordPrefix.natural (FormulaSignSlotRadialProviderAtomic.root old)
    (FormulaSignSlotRadialProviderAtomic.word old) (FormulaSignSlotRadialProviderAtomic.full_valid old hv)

noncomputable def parentCommands (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :=
  FormulaSignSlotRadialProviderRecordContinuation.beforeCommands (preparedRoot old e) (start old)
    (prefix_fit old hv hd e he)

theorem parent_length (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    (parentCommands old hv hd e he).length=endBirth (dimension old) (N old) old := by
  rw [parentCommands,FormulaSignSlotRadialProviderRecordContinuation.beforeCommands_length,prepared_initial]
  rfl

theorem parent_room (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    (parentCommands old hv hd e he).length≤(P).cap (preparedRoot old e)+1+1 := by
  rw [parentCommands,FormulaSignSlotRadialProviderRecordContinuation.beforeCommands_length]
  exact (FormulaSignSlotRadialProviderRecordPrefix.bound _ _ (prefix_fit old hv hd e he)).trans (Nat.le_succ _)

noncomputable def parentTuple (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    Index (Fin 0) (parentCommands old hv hd e he)→ℝ :=
  fun i=>oldNatural old hv (enumerate (parentCommands old hv hd e he) i).val

noncomputable def parentState (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :=
  reframe (run (initial P D (preparedRoot old e)) (parentCommands old hv hd e he) (parent_room old hv hd e he))
    (Q (preparedRoot old e)) (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot old e)) (cap (preparedRoot old e)))

private theorem observation_commands {n S B : ℕ} {V : SpatialSource n}
    (x : State V S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    IntegralMixedFramedRunObservation.ofCommands x cs hc=IntegralMixedFramedRunObservation.ofCommands x ds hd := by
  cases he
  rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.bank parentCommands parentTuple
  FormulaSignSlotRadialProviderRecordPrefix.observation

theorem parent_observation (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    FormulaSignSlotRadialProviderRecordPrefix.observation (preparedRoot old e) (start old)
      (prefix_fit old hv hd e he)=
    IntegralMixedFramedRunObservation.ofCommands (initial P D (preparedRoot old e))
      (parentCommands old hv hd e he) (parent_room old hv hd e he) := by
  unfold FormulaSignSlotRadialProviderRecordPrefix.observation IntegralFramedPhysicalPrefixObservation.atRoot
  apply observation_commands
  simpa only [parentCommands] using
    FormulaSignSlotRadialProviderRecordContinuation.before_commands _ _ (prefix_fit old hv hd e he)

theorem parent_roots (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    ∀i,((parentState old hv hd e he).sampler.rows i).eval₂ (Int.castRingHom ℝ)
      (parentTuple old hv hd e he)=0 := by
  have HR := FormulaSignSlotRadialProviderRecordPrefix.word_roots
    (FormulaSignSlotRadialProviderAtomic.root old) (FormulaSignSlotRadialProviderAtomic.word old)
    (FormulaSignSlotRadialProviderAtomic.full_valid old hv) (start old) (start_fit old hv)
  have HE := prefix_observation old hv hd e he (start old) (Nat.le_refl _)
  have HZ := (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots (oldNatural old hv)) HE).mpr HR
  have HO := parent_observation old hv hd e he
  have HZ' := (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots (oldNatural old hv)) HO).mp HZ
  unfold parentState parentTuple
  exact (IntegralMixedFramedRunObservation.roots_actual _ _ _ _).mp HZ'

theorem parent_interpretation (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    ∃φ : (parentState old hv hd e he).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((parentState old hv hd e he).sampler.scalarPrefix.basis.generator i)=
        parentTuple old hv hd e he ((parentState old hv hd e he).sampler.scalar i)^
          UniformIntegralPowerSchedule.weights ((P).cap (preparedRoot old e)+1) (2^(P).width (preparedRoot old e))
            (parentCommands old hv hd e he).length i) ∧
      ∀i,φ ((parentState old hv hd e he).bank.numerator i)/
        ((parentState old hv hd e he).bank.denominator i:ℝ)=
        IntegralMixedFullBankPoint.point (parentState old hv hd e he) (parentTuple old hv hd e he) i := by
  have HZ := parent_roots old hv hd e he
  unfold parentState at HZ ⊢
  exact IntegralMixedFramedFixedContinuation.before_interprets _ _ _ _ _ _ HZ

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
