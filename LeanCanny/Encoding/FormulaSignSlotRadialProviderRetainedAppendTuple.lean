/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendTail
public import LeanCanny.Geometry.IntegralMixedCanonicalPaddingPhysicalObservation
/-! # One full natural root tuple for a retained child and its seed completion -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedFramedRunObservation
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem observation_eq {n S B : ℕ} {V : SpatialSource n}
    (x : State V S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd := by cases he;rfl

theorem retained_full_room (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (root : List Bool) :
    (D.rules root).length≤P.cap root+1+1 := by have H := D.room root;omega

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "cap" => FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom levelObservation levelProgram

noncomputable def fullObservation (old : List Bool) (e : ℕ) :=
  ofCommands (initial P D (preparedRoot old e)) ((D).rules (preparedRoot old e))
    (retained_full_room P D (preparedRoot old e))

attribute [local irreducible] fullObservation

def PaddingTuple (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he)
    (z : ℕ→ℝ) (p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ) : Prop :=
  ∃u : ℕ→ℝ,(fullObservation old e).Roots u ∧
    (∀i,i<arity (levelProgram old hv hd e he R false)→u i=z i) ∧
    (∀j : Fin (IntegralMixedCanonicalPadding.paddingSelections
        ((P).ambient (preparedRoot old e)) (tailCount old e)).length,
      ∀i : Fin ((P).ambient (preparedRoot old e)+1),
      u (arity (levelProgram old hv hd e he R false)+
        (2*(P).ambient (preparedRoot old e)+4)*
          ((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)).length-1-j.val)+i.val)^
        UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot old e)+1) (2^(P).width (preparedRoot old e))
          ((levelProgram old hv hd e he R false).length+
            ((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)).length-1-j.val))=p i) ∧
    ∀i : Fin ((levelProgram old hv hd e he R false).length+
        (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)).length),
      (fullObservation old e).point u i.val=IntegralMixedPointCompanion.values p
        (fun j=>(levelObservation old hv hd e he R false).point z j.val)
        (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)) i

theorem exists_padding_tuple (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he)
    (z : ℕ→ℝ) (hz : (levelObservation old hv hd e he R false).Roots z)
    (p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial (Q (preparedRoot old e)).low
      (Q (preparedRoot old e)).leading (Q (preparedRoot old e)).degree).eval₂ (Int.castRingHom ℝ) p=0)
    (hg : ∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q (preparedRoot old e)).low
        (Q (preparedRoot old e)).leading (Q (preparedRoot old e)).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    PaddingTuple old hv hd e he R z p := by
  unfold PaddingTuple fullObservation
  have HE := full_commands old hv hd e he R
  have HR : ((D).rules (preparedRoot old e)).length≤(P).cap (preparedRoot old e)+1+1 :=
    retained_full_room P D (preparedRoot old e)
  have HRoom := (congrArg List.length HE).symm.le.trans HR
  have HZ : (ofCommands (initial P D (preparedRoot old e)) (levelProgram old hv hd e he R false)
      (levelProgram_room old hv hd e he R false)).Roots z := by
    simpa only [levelObservation] using hz
  obtain ⟨u,hu,ho,hblocks,hpoint⟩ := IntegralMixedCanonicalPadding.run_physical_observation
    (initial P D (preparedRoot old e)) (levelProgram old hv hd e he R false)
    (levelProgram_room old hv hd e he R false) (Q (preparedRoot old e))
    (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot old e)) (cap (preparedRoot old e)))
    (FormulaSignSlotRadialProviderRecordPlan.positive (preparedRoot old e))
    (charge old) (degree_power old e) (cap (preparedRoot old e)) z HZ p hp hg (tailCount old e) HRoom
  have HO := observation_eq (initial P D (preparedRoot old e)) _ _ HR HRoom HE
  refine ⟨u,?_,ho,?_,?_⟩
  · exact (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots u) HO).mpr hu
  · exact hblocks
  · intro i
    simpa only [levelObservation] using
      (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point u i.val) HO).trans (hpoint i)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
