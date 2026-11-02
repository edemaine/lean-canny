/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryPreparedSampling
/-! # The literal packed run realizes the sample, using only scalar cut births -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Geometry.CoerciveComponentSampling
open LeanCanny.Algebra.AuxiliaryTiltedTerm (polynomial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem noncritical_heq {a a' B B' : ℕ} (ha : a=a') (hB : B=B')
    (cs : List (Instruction a B)) (ds : List (Instruction a' B')) (h : HEq cs ds)
    (hd : ∀ c∈ds,c.command.isCritical=false) : ∀ c∈cs,c.command.isCritical=false := by
  cases ha
  cases hB
  cases eq_of_heq h
  exact hd

attribute [local irreducible] terminalState nativeRun dataAt planAt parameters scalarWidth scalarCeiling spatialDegree root

theorem native_realization_of_terminal {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool)
    (p : Fin (n original) → ℝ)
    (hp : OriginalRealization (terminalState hn ht ha original labels advice context) p) :
    OriginalRealization (nativeRun hn ht ha original labels advice) p := by
  let R := source 0 (degreeCharge n t original) (t original)
    (augmented n t original).degreeBound_le_dataSize 0 (scalarWidth n t original) (seed n t original+1)
  have HB : (parameters (dimension n) (term t)).width (root original labels advice)=scalarWidth n t original := by
    simp only [parameters,scalarWidth,scalarCeiling,spatialDegree,degreeCharge,augmented,dimension,term,root_original]
  have hRN : PurePowerReductionBounds.dimension (n original+3) R.degree≤
      2^(parameters (dimension n) (term t)).width (root original labels advice) := by
    rw [HB]
    exact (initialGeometric n t original).critical_cap
  have Hxy := terminalState_nativeRun hn ht ha original labels advice context R
    (terminalCap hn ht ha original labels advice context R (initialGeometric n t original).critical_cap) hRN
  have Hroom := (planAt hn ht ha).room (root original labels advice)
  have HC : ((planAt hn ht ha).rules (root original labels advice)).length≤
      (parameters (dimension n) (term t)).cap (root original labels advice)+1 := by omega
  have Hindex := IntegralMixedFramedFamilyRunView.commands_index_full (parameters (dimension n) (term t))
    (planAt hn ht ha) (root original labels advice) context HC
  have HS : (parameters (dimension n) (term t)).cap (root original labels advice)+1=n original+3 := by
    simpa only [parameters,stateHorizon] using root_stateHorizon n original labels advice
  have HR := originalRealization_transport
    (reframe (nativeRun hn ht ha original labels advice) R hRN)
    (reframe (terminalState hn ht ha original labels advice context) R
      (terminalCap hn ht ha original labels advice context R (initialGeometric n t original).critical_cap))
    (HS.trans (terminal_horizon hn ht ha original labels advice context).symm)
    (HB.trans (terminal_width hn ht ha original labels advice context).symm)
    ((script_length hn ht ha original labels advice).trans (terminal_birth hn ht ha original labels advice context).symm)
    Hindex.symm Hxy.symm p ((originalRealization_reframe _ _ _ _).mpr hp)
  exact (originalRealization_reframe _ _ _ _).mp HR

theorem rules_noncritical {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice : List Bool) :
    ∀ c∈(planAt hn ht ha).rules (root original labels advice),c.command.isCritical=false := by
  have HA : (parameters (dimension n) (term t)).ambient (root original labels advice)=n original+2 := by
    simp only [parameters,dimension,root_original]
  have HB : (parameters (dimension n) (term t)).width (root original labels advice)=scalarWidth n t original := by
    simp only [parameters,scalarWidth,scalarCeiling,spatialDegree,degreeCharge,augmented,dimension,term,root_original]
  apply noncritical_heq HA HB _ _ (script_replay hn ht ha original labels advice)
  intro c hc
  rw [replay,List.mem_reverse] at hc
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hc
  simp only [recipeInstruction,IntegralMixedAuxiliaryLimitRecord.instruction,
    IntegralMixedCanonicalUnitRuleBits.command,IntegralMixedAuxiliaryLimitRecord.critical_record,
    Bool.false_eq_true,ite_false,IntegralMixedFullHistoryScript.Command.isCritical]

theorem exists_prepared_run_sample_uniform {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool)
    (C : Set (Zeros (polynomial (n original) (t original)))) (hC : IsClopen C)
    (x0 : Zeros (polynomial (n original) (t original))) (hx0 : x0∈C) :
    ∃ labels : Fin (n original) → ℕ × ℕ,
      (∀ i,(labels i).1≤scalarCeiling n t original ∧ (labels i).2≤scalarCeiling n t original) ∧
      ∃ p : Zeros (polynomial (n original) (t original)), p∈C ∧
        ∀ advice, OriginalRealization (nativeRun hn ht ha original labels advice) p.val := by
  obtain ⟨labels,hb,p,hp,hr⟩:=exists_prepared_sample_uniform hn ht ha original C hC x0 hx0
  exact ⟨labels,hb,p,hp,fun advice => native_realization_of_terminal hn ht ha original labels advice [] p.val (hr advice [])⟩
end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
