/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendTail
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendObservation
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendTuple
/-! # One complete numerical tuple for a proper child and its seed completion -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedFramedRunObservation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "cap" => FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap

private theorem observation_eq {n S B : ℕ} {V : SpatialSource n}
    (x : State V S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd := by cases he;rfl

theorem prepared_degree_power (old l r : List Bool) (side : Bool) :
    (Q (preparedRoot old l r side)).degree=
      BoundedZeroSource.powerDegree (FormulaSignSlotRadialProviderRetainedAppend.charge old) := by
  rw [FormulaSignSlotRadialProviderRecordPlan.spatial_degree]
  change IntegralMixedAuxiliaryMarkedIntegerPlan.degree LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (preparedRoot old l r side))=_
  rw [(prepared_provider old l r side).trans (FormulaSignSlotRadialProviderAtomic.root_provider old)]
  rfl

variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  compiledObservation compiledProgram

noncomputable def fullObservation :=
  ofCommands (initial P D r) ((D).rules r)
    (FormulaSignSlotRadialProviderRetainedAppend.retained_full_room P D r)
attribute [local irreducible] fullObservation

def PaddingTuple (z : ℕ→ℝ) (p : Fin ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)+1)→ℝ) : Prop :=
  ∃u : ℕ→ℝ,(fullObservation old hv hd left right R side).Roots u ∧
    (∀i,i<arity (compiledProgram old hv hd left right R side)→u i=z i) ∧
    (∀j : Fin (IntegralMixedCanonicalPadding.paddingSelections
        ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)) (tailCount old hv hd left right R side)).length,
      ∀i : Fin ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)+1),
      u (arity (compiledProgram old hv hd left right R side)+
        (2*(P).ambient (preparedRoot old R.leftSpec R.rightSpec side)+4)*
          ((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)) (tailCount old hv hd left right R side)).length-1-j.val)+i.val)^
        UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot old R.leftSpec R.rightSpec side)+1) (2^(P).width (preparedRoot old R.leftSpec R.rightSpec side))
          ((compiledProgram old hv hd left right R side).length+
            ((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)) (tailCount old hv hd left right R side)).length-1-j.val))=p i) ∧
    ∀i : Fin ((compiledProgram old hv hd left right R side).length+
        (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)) (tailCount old hv hd left right R side)).length),
      (fullObservation old hv hd left right R side).point u i.val=IntegralMixedPointCompanion.values p
        (fun j=>(compiledObservation old hv hd left right R side).point z j.val)
        (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)) (tailCount old hv hd left right R side)) i

theorem exists_padding_tuple (z : ℕ→ℝ) (hz : (compiledObservation old hv hd left right R side).Roots z)
    (p : Fin ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial (Q (preparedRoot old R.leftSpec R.rightSpec side)).low
      (Q (preparedRoot old R.leftSpec R.rightSpec side)).leading (Q (preparedRoot old R.leftSpec R.rightSpec side)).degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q (preparedRoot old R.leftSpec R.rightSpec side)).low
        (Q (preparedRoot old R.leftSpec R.rightSpec side)).leading (Q (preparedRoot old R.leftSpec R.rightSpec side)).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    PaddingTuple old hv hd left right R side z p := by
  unfold PaddingTuple fullObservation
  have HE := full_commands old hv hd left right R side
  have HR : ((D).rules (preparedRoot old R.leftSpec R.rightSpec side)).length≤(P).cap (preparedRoot old R.leftSpec R.rightSpec side)+1+1 :=
    FormulaSignSlotRadialProviderRetainedAppend.retained_full_room P D (preparedRoot old R.leftSpec R.rightSpec side)
  have HRoom := (congrArg List.length HE).symm.le.trans HR
  have HZ : (ofCommands (initial P D (preparedRoot old R.leftSpec R.rightSpec side)) (compiledProgram old hv hd left right R side)
      (compiled_program_room old hv hd left right R side)).Roots z := by
    simpa only [compiledObservation] using hz
  obtain ⟨u,hu,ho,hblocks,hpoint⟩ := IntegralMixedCanonicalPadding.run_physical_observation
    (initial P D (preparedRoot old R.leftSpec R.rightSpec side)) (compiledProgram old hv hd left right R side)
    (compiled_program_room old hv hd left right R side) (Q (preparedRoot old R.leftSpec R.rightSpec side))
    (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot old R.leftSpec R.rightSpec side)) (cap (preparedRoot old R.leftSpec R.rightSpec side)))
    (FormulaSignSlotRadialProviderRecordPlan.positive (preparedRoot old R.leftSpec R.rightSpec side))
    (FormulaSignSlotRadialProviderRetainedAppend.charge old) (prepared_degree_power old R.leftSpec R.rightSpec side) (cap (preparedRoot old R.leftSpec R.rightSpec side)) z HZ p hp hg (tailCount old hv hd left right R side) HRoom
  have HO := observation_eq (initial P D (preparedRoot old R.leftSpec R.rightSpec side)) _ _ HR HRoom HE
  refine ⟨u,?_,ho,?_,?_⟩
  · exact (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots u) HO).mpr hu
  · exact hblocks
  · intro i
    simpa only [compiledObservation] using
      (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point u i.val) HO).trans (hpoint i)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
