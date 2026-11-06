/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixFields
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotFamily
/-! # Provider prefix snapshots realize their own full word's actual quotients -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
def Data.Realizes (d : Data) (values : ℕ→ℝ) : Prop :=
  IntegralMixedIntegerRealization.Realizes d.state values
theorem Data.realizes_iff (d : Data) (values : ℕ→ℝ) :
    d.Realizes values ↔ IntegralMixedIntegerRealization.Realizes d.state values := Iff.rfl
end LeanCanny.Algebra.IntegralMixedPrefixSnapshot

namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation
  LeanCanny.ETR.Term.finitePolynomial
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count

private theorem realizes_at_snapshot (a : Parameters) (d : IntegralMixedFramedHistoryFamilyBits.Plan a)
    (r : List Bool) (m : ℕ) (hm : m≤a.cap r+1) (z : ℕ→ℝ)
    (hz : (IntegralFramedPhysicalPrefixObservation.atRoot a d r m hm).Roots z) :
    (IntegralMixedPrefixSnapshot.atRoot a d r m hm).Realizes
      ((IntegralFramedPhysicalPrefixObservation.atRoot a d r m hm).point z) := by
  unfold IntegralMixedPrefixSnapshot.Data.Realizes
  apply (IntegralMixedPrefixSnapshot.ofCommands_realizes _ _ _ _).mpr
  exact IntegralFramedPhysicalPrefixObservation.at_realizes a d r m hm z hz

theorem snapshot_birth (r : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count r) :
    (snapshot r j hj).birth=N r+j :=
  (IntegralMixedPrefixSnapshot.ofCommands_birth (initial P D r)
    (paddedPast (defaultInstruction P D r) ((D).rules r) (N r+j)) _).trans (paddedPast_length _ _ _)

theorem snapshot_canonical (r : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count r) :
    Canonical (snapshot r j hj).state :=
  IntegralMixedPrefixSnapshot.ofCommands_canonical _ (fun i=>Fin.elim0 i) _ _

attribute [local irreducible] IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderRecordPlan.source snapshot observation IntegralMixedIntegerRealization.Realizes
  IntegralMixedPrefixSnapshot.Data.Realizes

theorem snapshot_word_realizes (r w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context r) w)
    (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count r) :
    (snapshot r j hj).Realizes
      ((observation r j hj).point (natural r w hw)) := by
  have HR := word_roots r w hw j hj
  unfold observation at HR
  unfold snapshot observation
  have H := realizes_at_snapshot P D r (N r+j) (bound r j hj) (natural r w hw) HR
  exact H

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefix
