/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabConnectivity
public import LeanCanny.Encoding.FlatAffineSlabGraphContextChoice
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Slab connectivity from a frame and gap index alone

The native algorithm computes the algebraic context before running graph
connectivity. On every valid bounded gap it decides preconnectedness of the
actual original root set over the closure of that gap. No endpoint, sample,
branch, or marker labels are part of its input.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineGapConnectivity
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source gapWord)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineSlabGraphContext.endpointValue FlatAffineEndpointSampleSlab.roots

noncomputable def selectedGapAt (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s g : List Bool) : Set ℝ :=
  let S := FlatAffineEndpointSampleSlab.roots F cone height s
  OrderedRealCells.gap S ⟨min (Nat.fromBitsLE g) S.card, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

noncomputable def solutionSetAt (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s g : List Bool) :
    Set (ℝ × (Fin (count F (pairFst (pairFst s))) → ℝ)) :=
  {z | z.1 ∈ closure (selectedGapAt F cone height s g) ∧
    z.2 ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s z.1}

theorem context_solution_iff (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) :
    IsPreconnected (univ : Set (FlatAffineSlabGraphBranches.Space F cone height c)) ↔
      IsPreconnected (solutionSetAt F cone height (source c) (gapWord c)) := by
  have HB := (FlatAffineSlabGraphContext.gapIndex F cone height c hc).isLt
  have HK : min (Nat.fromBitsLE (gapWord c)) (FlatAffineSlabGraphContext.roots F cone height c).card = Nat.fromBitsLE (gapWord c) :=
    Nat.min_eq_left (Nat.le_of_lt_succ HB)
  have HG : selectedGapAt F cone height (source c) (gapWord c) =
      Ioo (FlatAffineSlabGraphContext.endpointValue F cone height false c) (FlatAffineSlabGraphContext.endpointValue F cone height true c) := by
    unfold selectedGapAt
    dsimp only
    have HI : (⟨min (Nat.fromBitsLE (gapWord c)) (FlatAffineEndpointSampleSlab.roots F cone height (source c)).card,
        Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ : Fin ((FlatAffineEndpointSampleSlab.roots F cone height (source c)).card + 1)) =
        FlatAffineSlabGraphContext.gapIndex F cone height c hc := Fin.ext HK
    rw [HI]
    exact FlatAffineSlabGraphContext.gap_eq_interval F cone height c hc
  let A : Set (ℝ × (Fin (count F (FlatAffineSlabGraphArcs.original c)) → ℝ)) :=
    {z | z.1 ∈ Icc (FlatAffineSlabGraphContext.endpointValue F cone height false c)
      (FlatAffineSlabGraphContext.endpointValue F cone height true c) ∧ FlatAffineSlabGraphArcs.equation F height c z.1 z.2}
  have H := (Topology.IsInducing.subtypeVal (t := A)).isPreconnected_image (s := univ)
  simp only [image_univ, Subtype.range_val] at H
  have HE : {z : ℝ × (Fin (count F (FlatAffineSlabGraphArcs.original c)) → ℝ) | z.1 ∈ Icc (FlatAffineSlabGraphContext.endpointValue F cone height false c)
      (FlatAffineSlabGraphContext.endpointValue F cone height true c) ∧ FlatAffineSlabGraphArcs.equation F height c z.1 z.2} =
      solutionSetAt F cone height (source c) (gapWord c) := by
    ext z
    simp only [solutionSetAt, Set.mem_ofPred_eq, HG,
      closure_Ioo (FlatAffineSlabGraphContext.endpoints_lt F cone height c hc).ne]
    rfl
  exact H.symm.trans (Iff.of_eq (congrArg IsPreconnected HE))

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  FlatAffineSlabGraphContextChoice.value F cone height ⁻¹' FlatAffineSlabConnectivity.language F cone height

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (language F cone height) := by
  apply SpaceDecider.of_computable ((FlatAffineSlabConnectivity.decider h cone height hh).computable.comp
    (FlatAffineSlabGraphContextChoice.evaluator h cone height hh).computable)
  intro q
  simp only [language, Set.mem_preimage, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : language F cone height ∈ PSPACE :=
  (decider h cone height hh).mem_PSPACE

theorem bounded_gap_correct (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (k : Fin ((FlatAffineEndpointSampleSlab.roots F cone height s).card + 1))
    (h0 : 0 < k.val) (hk : k.val < (FlatAffineEndpointSampleSlab.roots F cone height s).card) :
    pair s (BinaryNatCode.encode k.val) ∈ language F cone height ↔
      IsPreconnected (solutionSetAt F cone height s (BinaryNatCode.encode k.val)) := by
  have HV := FlatAffineSlabGraphContextChoice.value_valid F cone height s hs k h0 hk
  have H := context_solution_iff F cone height _ HV.1
  rw [HV.2.1, HV.2.2] at H
  simp only [language, Set.mem_preimage, FlatAffineSlabConnectivity.language, Set.mem_ofPred_eq, HV.1, true_and]
  exact H

end LeanCanny.Connectivity.FlatAffineGapConnectivity
