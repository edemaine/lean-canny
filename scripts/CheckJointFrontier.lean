import LeanCanny.Connectivity
open LeanCanny LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.ETR
open scoped Classical
namespace JointFrontierRegression
attribute [local irreducible] FormulaSignSlotRadialJointStratum.source ImplicitSourceGramGrid.input
  SquareSampleCompleteVertices.Valid SquareSampleCompleteVertices.candidate
  FormulaSignSlotRadialProviderJointWitness.Witness FormulaSignSlotRadialProviderGuardedJointWitness.language


example (d : Description) (hd : d.WellFormed) (i j : CanonicalAuxiliaryCandidateCover.Index d)
    (h : FormulaSignSlotRadialJointFeasibility.Feasible (CanonicalAuxiliaryJointHeader.header d i j)) :
    CanonicalAuxiliaryCandidateCover.edge d i j :=
  (CanonicalAuxiliaryFrontierJointCodec.edge_iff d hd i j).mpr (Or.inr (Or.inl h))

example : FormulaSignSlotRadialProviderGuardedJointWitness.language
    FormulaSignSlotRadialImplicitGridSelection.language ∈ PSPACE :=
  FormulaSignSlotRadialProviderGuardedJointWitness.mem_PSPACE _ FormulaSignSlotRadialImplicitGridSelection.decider

/-- One supplied actual sample with both labels and grid gives a native
bounded certificate, retaining its entire original Gamma and OWN word. -/
example (H : List Bool) (k : ℕ) (Gamma w : List Bool)
    (hGamma : Gamma.length ≤ FormulaSignSlotRadialJointStratumSampler.tableBound (FormulaSignSlotRadialJointStratum.packet H k))
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialJointStratumSampler.input
      (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w)
    (hq : pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w ∈ FormulaSignSlotRadialJointStratumSampler.language)
    (x : FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k))
    (hx : HEq (SquareSampleCompleteVertices.candidate FormulaSignSlotRadialJointStratumSampler.input
      (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w hw).val x.val)
    (HB : FormulaSignSlotRadialJointStratumLabels.BothLabels (FormulaSignSlotRadialJointStratum.packet H k) x)
    (HG : FormulaSignSlotRadialJointGridRetention.Grid (FormulaSignSlotRadialJointStratum.packet H k) x) :
    H ∈ FormulaSignSlotRadialProviderGuardedJointWitness.language FormulaSignSlotRadialImplicitGridSelection.language := by
  obtain ⟨aL,eL,aR,eR,HW⟩ := FormulaSignSlotRadialProviderJointSampleWitness.witness_of_sampled_point H k Gamma w hGamma hw hq x hx HB
  have HO : pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w ∈ FormulaSignSlotRadialImplicitGridSelection.language := by
    simp only [FormulaSignSlotRadialImplicitGridSelection.language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]
    exact ⟨hw,(FormulaSignSlotRadialImplicitSampleReadback.grid_iff _ Gamma w hw x hx).mpr HG⟩
  exact (FormulaSignSlotRadialProviderGuardedJointWitness.language_iff FormulaSignSlotRadialImplicitGridSelection.language H).mpr
    ⟨k,Gamma,w,aL,eL,aR,eR,HW,HO⟩

#print axioms CanonicalAuxiliaryFrontierJointCodec.edge_iff
#print axioms CanonicalAuxiliaryRadialCodec.feasible_iff_raw_descriptor
#print axioms CanonicalAuxiliarySampleEndpoints.original_point_iff_samples
#print axioms CanonicalEndpointSampleBits.evaluator
#print axioms CanonicalEndpointSampleBits.value_source_point
#print axioms CanonicalEndpointSampleBits.value_target_point
#print axioms FormulaSignSlotRadialImplicitGridSelection.mem_PSPACE
#print axioms FormulaSignSlotRadialImplicitGridSelection.holds_packet_iff
#print axioms FormulaSignSlotRadialProviderGuardedJointWitness.mem_PSPACE
#print axioms FormulaSignSlotRadialProviderJointSampleWitness.witness_of_sampled_point
#print axioms FormulaSignSlotRadialImplicitSampleReadback.cut_free_iff
#print axioms FormulaSignSlotRadialJointCutRetention.component_hit
end JointFrontierRegression
