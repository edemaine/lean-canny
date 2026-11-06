/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendLevel
public import LeanCanny.Geometry.IntegralMixedChronologicalGuardedEqualLevel
/-! # Genuine child-critical points realize both actual retained blocks -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Connectivity IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedChronologicalFrame IntegralMixedChronologicalEndpoint IntegralMixedFrozenFrame
open IntegralMixedFramedHistoryFamilyBits (initial)
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def PhysicalLevelTuple {n S B : ℕ} {V Q0 : SpatialSource n}
    (initial0 : State V S B 0 (Fin 0))
    (hQ0 : PurePowerReductionBounds.dimension (n+1) Q0.degree≤2^B)
    (older : List (Instruction n B)) (_ho : older.length≤S+1)
    (x : State Q0 S B older.length (Index (Fin 0) older))
    (d : Descriptor n older.length) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)
    (hn : 0<n) (hcapQ : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q0.degree≤2^B)
    (z : Index (Fin 0) older→ℝ) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin older.length→ℝ) (left right : IntegralMixedOptionalEndpoints.Endpoint older.length)
    (horizon : older.length+2+2+2*(n-d.labels.length)≤S+1) (p : Fin (n+1)→ℝ) : Prop :=
  ∃R : NativePair x d z φ values left right hn hcapQ,∀side,
    let hr : older.length+R.result.commands.length+2+2*(R.orderedFree hk).length≤S+1 := by
      have HC := R.result.count
      have HQ := R.orderedFree_length hk
      omega
    ∃u : ℕ→ℝ,
      (IntegralMixedFramedRunObservation.ofCommands initial0
        ((R.levelCommands hk g hg side).map (IntegralMixedFramedFixedContinuation.wrap Q0 hQ0)++older)
        (by have HH := R.level_room hk g hg side (by omega);simp only [List.length_append,List.length_map];omega)).Roots u ∧
      R.PhysicalReadback hQ0 older hk g hg side hr
        (arity ((R.levelCommands hk g hg side).map (IntegralMixedFramedFixedContinuation.wrap Q0 hQ0)++older)) u p p
        (fun j=>(IntegralMixedFramedRunObservation.ofCommands initial0
          ((R.levelCommands hk g hg side).map (IntegralMixedFramedFixedContinuation.wrap Q0 hQ0)++older)
          (by have HH := R.level_room hk g hg side (by omega);simp only [List.length_append,List.length_map];omega)).point u j) ∧
      ∀j : Index (Fin 0) older,u (enumerate older j).val=z j

private theorem physical_level_exists {n S B : ℕ} {V Q0 : SpatialSource n}
    (initial0 : State V S B 0 (Fin 0))
    (hQ0 : PurePowerReductionBounds.dimension (n+1) Q0.degree≤2^B)
    (older : List (Instruction n B)) (ho : older.length≤S+1)
    (x : State Q0 S B older.length (Index (Fin 0) older))
    (hx : x=reframe (run initial0 older ho) Q0 hQ0)
    (d : Descriptor n older.length) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(line d.frame (IntegralMixedChronologicalSweepFrame.next d hk)).frozen)
    (HG : g.val=d.labels.length+1) (hn : 0<n) (charge0 : ℕ)
    (hd : Q0.degree=BoundedZeroSource.powerDegree charge0)
    (hcapQ : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q0.degree≤2^B)
    (z : Index (Fin 0) older→ℝ) (hz : ∀i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^
      UniformIntegralPowerSchedule.weights S (2^B) older.length i)
    (values : Fin older.length→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (horizon : older.length+2+2+2*(n-d.labels.length)≤S+1)
    (choices : IntegralMixedRelativeCuts.Choices x (by omega)
      (cutRule x d.frame (IntegralMixedChronologicalSweepFrame.next d hk) g hg) φ)
    (left right : IntegralMixedOptionalEndpoints.Endpoint older.length)
    (HL : left.Allowed (jointEndpointSet x (by omega) φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values choices))
    (HR : right.Allowed (jointEndpointSet x (by omega) φ d.frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg values choices))
    (he : left.value values=right.value values) (p : Fin (n+1)→ℝ)
    (HS : p∈slice Q0 d.frame values) (Hh : p (IntegralMixedChronologicalSweepFrame.next d hk)=left.value values)
    (Hgrad : ∀i,i∉insert (IntegralMixedChronologicalSweepFrame.next d hk) d.frame.frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial Q0.low Q0.leading Q0.degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    PhysicalLevelTuple initial0 hQ0 older ho x d hk g hg hn hcapQ z φ values left right horizon p := by
  exact exists_physical_equal_level_at_state initial0 hQ0 older ho x hx d hk g hg HG hn charge0 hd
    hcapQ z hz φ hφ values H horizon choices left right HL HR he p HS Hh Hgrad

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "cap" => FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap

noncomputable def charge (old : List Bool) :=
  (CanonicalAuxiliaryCandidateCover.equation (FormulaSignSlotRadialProviderAtomic.original old)).toData.size

theorem degree_power (old : List Bool) (e : ℕ) :
    (Q (preparedRoot old e)).degree=BoundedZeroSource.powerDegree (charge old) := by
  rw [FormulaSignSlotRadialProviderRecordPlan.spatial_degree]
  change IntegralMixedAuxiliaryMarkedIntegerPlan.degree CanonicalAuxiliaryCandidateCover.equation
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (preparedRoot old e))=_
  rw [(prepared_provider old e).trans (FormulaSignSlotRadialProviderAtomic.root_provider old)]
  rfl

theorem cap_full (old : List Bool) (e : ℕ) :
    (P).cap (preparedRoot old e)=FormulaSignSlotRadialProviderRecordPlan.fullCount (preparedRoot old e)+2 := rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderIntegerSource.source parentState parentTuple parentValues parentHom
  parentDescriptor parentCommands

theorem equal_horizon (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    (parentCommands old hv hd e he).length+2+2+2*((P).ambient (preparedRoot old e)-
      (parentDescriptor old hv hd e he).labels.length)≤(P).cap (preparedRoot old e)+1+1 := by
  have HF := finish_le_full old hv hd e he
  rw [finish_eq] at HF
  rw [parent_descriptor_length,parent_length,prepared_dimension]
  rw [cap_full]
  unfold fullBirth at HF
  omega

noncomputable def levelChoices (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :=
  Classical.choice (IntegralMixedRelativeCuts.exists_choices (parentState old hv hd e he)
    (parent_horizon old hv hd e he)
    (cutRule (parentState old hv hd e he) (parentDescriptor old hv hd e he).frame
      (IntegralMixedChronologicalSweepFrame.next (parentDescriptor old hv hd e he)
        (parent_descriptor_fit old hv hd e he))
      (childCoordinate old hv hd e he) (child_coordinate_free old hv hd e he))
    (parentHom old hv hd e he))

noncomputable abbrev Pair (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :=
  NativePair (parentState old hv hd e he) (parentDescriptor old hv hd e he) (parentTuple old hv hd e he)
    (parentHom old hv hd e he) (parentValues old hv hd e he)
    (.retained (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)))
    (.retained (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)))
    (FormulaSignSlotRadialProviderRecordPlan.positive (preparedRoot old e)) (cap (preparedRoot old e))

theorem pair_level_room (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he) :
    (parentCommands old hv hd e he).length+R.result.commands.length+2+
      2*(R.orderedFree (parent_descriptor_fit old hv hd e he)).length≤(P).cap (preparedRoot old e)+1+1 := by
  have HC := R.count
  simp only [IntegralMixedOptionalEndpoints.Endpoint.freshCount,Nat.add_zero] at HC
  have HF := R.orderedFree_length (parent_descriptor_fit old hv hd e he)
  have HD : FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (preparedRoot old e)=dimension old :=
    prepared_dimension old e
  have HK := parent_descriptor_length old hv hd e he
  have HFree : (R.orderedFree (parent_descriptor_fit old hv hd e he)).length=dimension old-depth old := by omega
  rw [HC,Nat.add_zero,HFree]
  exact level_room old hv hd e he

noncomputable def levelProgram (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he) (side : Bool) :
    List (Instruction ((P).ambient (preparedRoot old e)) ((P).width (preparedRoot old e))) :=
  ((R.levelCommands (parent_descriptor_fit old hv hd e he) (childCoordinate old hv hd e he)
    (child_coordinate_free old hv hd e he) side).map
      (IntegralMixedFramedFixedContinuation.wrap (Q (preparedRoot old e))
        (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot old e)) (cap (preparedRoot old e)))) :
          List (Instruction ((P).ambient (preparedRoot old e)) ((P).width (preparedRoot old e))))++parentCommands old hv hd e he

theorem levelProgram_room (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he) (side : Bool) :
    (levelProgram old hv hd e he R side).length≤(P).cap (preparedRoot old e)+1+1 := by
  have HH := R.level_room (parent_descriptor_fit old hv hd e he) (childCoordinate old hv hd e he)
    (child_coordinate_free old hv hd e he) side (by have H := pair_level_room old hv hd e he R;omega)
  simp only [levelProgram,List.length_append,List.length_map]
  omega

noncomputable def levelObservation (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he) (side : Bool) :=
  IntegralMixedFramedRunObservation.ofCommands (initial P D (preparedRoot old e))
    (levelProgram old hv hd e he R side) (levelProgram_room old hv hd e he R side)

attribute [local irreducible] levelProgram levelObservation

def LevelTuple (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old)
    (p : Fin (FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (preparedRoot old e)+1)→ℝ) : Prop :=
  PhysicalLevelTuple (initial P D (preparedRoot old e))
    (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot old e)) (cap (preparedRoot old e)))
    (parentCommands old hv hd e he) (parent_room old hv hd e he) (parentState old hv hd e he)
    (parentDescriptor old hv hd e he) (parent_descriptor_fit old hv hd e he)
    (childCoordinate old hv hd e he) (child_coordinate_free old hv hd e he)
    (FormulaSignSlotRadialProviderRecordPlan.positive (preparedRoot old e)) (cap (preparedRoot old e))
    (parentTuple old hv hd e he) (parentHom old hv hd e he) (parentValues old hv hd e he)
    (.retained (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)))
    (.retained (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)))
    (equal_horizon old hv hd e he) p

theorem exists_level_tuple (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old)
    (p : Fin (FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (preparedRoot old e)+1)→ℝ)
    (HS : p∈slice (Q (preparedRoot old e)) (parentDescriptor old hv hd e he).frame (parentValues old hv hd e he))
    (Hh : p (IntegralMixedChronologicalSweepFrame.next (parentDescriptor old hv hd e he)
      (parent_descriptor_fit old hv hd e he))=
        parentValues old hv hd e he (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)))
    (Hgrad : ∀i,i∉insert (IntegralMixedChronologicalSweepFrame.next (parentDescriptor old hv hd e he)
      (parent_descriptor_fit old hv hd e he)) (parentDescriptor old hv hd e he).frame.frozen→
        i≠childCoordinate old hv hd e he→(MvPolynomial.pderiv i
          (FermatCriticalHomogenization.polynomial (Q (preparedRoot old e)).low
            (Q (preparedRoot old e)).leading (Q (preparedRoot old e)).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    LevelTuple old hv hd e he p := by
  exact physical_level_exists
    (initial P D (preparedRoot old e))
    (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot old e)) (cap (preparedRoot old e)))
    (parentCommands old hv hd e he) (parent_room old hv hd e he) (parentState old hv hd e he)
    (by unfold parentState;rfl)
    (parentDescriptor old hv hd e he) (parent_descriptor_fit old hv hd e he)
    (childCoordinate old hv hd e he) (child_coordinate_free old hv hd e he) rfl
    (FormulaSignSlotRadialProviderRecordPlan.positive (preparedRoot old e)) (charge old) (degree_power old e)
    (cap (preparedRoot old e)) (parentTuple old hv hd e he) (parent_roots old hv hd e he)
    (parentHom old hv hd e he) (parentHom_generators old hv hd e he) (parentValues old hv hd e he)
    (parentHom_quotients old hv hd e he) (equal_horizon old hv hd e he) (levelChoices old hv hd e he)
    (.retained (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)))
    (.retained (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)))
    True.intro True.intro rfl p HS Hh Hgrad

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
