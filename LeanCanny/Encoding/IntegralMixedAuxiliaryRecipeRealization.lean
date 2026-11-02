/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeMetadata
public import LeanCanny.Geometry.CanonicalAuxiliaryRealizationTransport
/-! # Original quotient readbacks belong to the actual packed saved bank -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open IntegralMixedAuxiliaryPreparedRoot (dimension term)
open LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] dataAt terminalState nativeRun parameters scalarWidth scalarCeiling spatialDegree root planAt

theorem terminal_realization_of_replay {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool) (labels : Fin (n original) → ℕ × ℕ) (advice context : List Bool)
    (L : SampleFrame (n original) (n original+3) (scalarWidth n t original)
      (degreeCharge n t original) (t original) (augmented n t original).degreeBound_le_dataSize)
    (hbirth : L.birth=n original)
    (hcs : (replay (n:=n original) (S:=n original+3)
      (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
      (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original)
      (seed n t original+1) labels).length≤n original+3+1)
    (hindex : Index (Fin 0) (replay (n:=n original) (S:=n original+3)
      (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
      (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original)
      (seed n t original+1) labels)=L.carrier)
    (hState : HEq (reframe (run (initialGeometric n t original)
      (replay (n:=n original) (S:=n original+3)
        (B:=scalarWidth n t original) (D:=degreeCharge n t original) (t:=t original)
        (ht:=(augmented n t original).degreeBound_le_dataSize) (recipeCap n t original)
        (seed n t original+1) labels) hcs)
      (source L.frozen (degreeCharge n t original) (t original)
        (augmented n t original).degreeBound_le_dataSize L.birth (scalarWidth n t original) L.height)
      L.state.critical_cap) L.state)
    (p : Fin (n original) → ℝ) (hp : OriginalRealization L.state p) :
    OriginalRealization (terminalState hn ht ha original labels advice context) p := by
  let R := source L.frozen (degreeCharge n t original) (t original)
    (augmented n t original).degreeBound_le_dataSize L.birth (scalarWidth n t original) L.height
  have H := (terminalState_replay hn ht ha original labels advice context R L.state.critical_cap hcs).trans hState
  have HR := originalRealization_transport
    (reframe (terminalState hn ht ha original labels advice context) R
      (terminalCap hn ht ha original labels advice context R L.state.critical_cap))
    L.state (terminal_horizon hn ht ha original labels advice context)
    (terminal_width hn ht ha original labels advice context)
    ((terminal_birth hn ht ha original labels advice context).trans hbirth.symm)
    ((terminal_index hn ht ha original labels advice context).trans hindex) H p hp
  exact (originalRealization_reframe _ _ _ _).mp HR
end LeanCanny.Encoding.IntegralMixedAuxiliaryRecipeRoot
