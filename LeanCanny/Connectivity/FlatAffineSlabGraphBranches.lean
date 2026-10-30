/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabGraphArcs
public import LeanCanny.Encoding.FlatAffineSlabGraphJointLabels
public import LeanCanny.Encoding.FlatAffineEndpointBranchLabelComplete

/-! # Complete slab branches with constructed native reference labels

Every accepted scalar context supplies its actual complete branch family and
accepted joint labels at both retained samples. These references certify the
native graph; they are not extra inputs to its algorithms.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source gapWord endpointWord sampleWord)
open FlatAffineSlabGraphArcs (original equation Index)
open FlatAffineSlabGraphContext (endpointValue sampleValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

structure Family (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) where
  curve : Index F cone height c → ℝ → Fin (count F (original c)) → ℝ
  anchor : ∀ j, curve j (sampleValue F cone height false c) = j.val
  continuous : ∀ j, ContinuousOn (curve j) (Icc (endpointValue F cone height false c) (endpointValue F cone height true c))
  roots : ∀ j t, t ∈ Icc (endpointValue F cone height false c) (endpointValue F cone height true c) → equation F height c t (curve j t)
  complete : ∀ t : Ioo (endpointValue F cone height false c) (endpointValue F cone height true c), ∀ x,
    equation F height c t.val x ↔ ∃! j, curve j t.val = x
  reference : Bool → Index F cone height c → List Bool
  valid : ∀ side j, SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (source c) (reference side j)
  sample : ∀ side j, FlatAffineEndpointRankWord.sampleValue F cone height (source c) (reference side j) = sampleValue F cone height side c
  current : ∀ side j, FlatAffineEndpointRankWord.currentValue F cone height (source c) (reference side j) = curve j (sampleValue F cone height side c)
  endpoint : ∀ side j, FlatAffineEndpointFiniteProjection.copy F (source c)
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (source c) (reference side j) (valid side j)).val 1 =
      curve j (endpointValue F cone height side c)
  adjacent : ∀ side j, pair (pair (source c) (reference side j)) (pair (endpointWord side c) (sampleWord side c)) ∈
    FlatAffineEndpointFiniteAdjacent.language F cone height (!side)
  slab : ∀ side j, pair (pair (source c) (reference side j)) (pair (sampleWord side c) (gapWord c)) ∈
    FlatAffineEndpointSampleSlab.language F cone height

theorem exists_family (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) :
    Finite (Index F cone height c) ∧ Nonempty (Family F cone height c) := by
  obtain ⟨hfin, curve, ha, hcont, hroot, hcomplete, _⟩ := FlatAffineSlabGraphArcs.anchored_arcs F cone height c hc
  have H (side : Bool) (j : Index F cone height c) := FlatAffineSlabGraphContext.joint_label_exists F cone height side c hc
    (curve j (sampleValue F cone height side c)) (curve j (endpointValue F cone height side c))
    (hroot j _ (Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between F cone height side c hc)))
    (hroot j _ (by
      have hab := (FlatAffineSlabGraphContext.endpoints_lt F cone height c hc).le
      cases side
      · exact ⟨le_rfl, hab⟩
      · exact ⟨hab, le_rfl⟩))
  choose refs hv ht hx he hadj hslab using H
  exact ⟨hfin, ⟨⟨curve, ha, hcont, hroot, hcomplete, refs, hv, ht, hx, he, hadj, hslab⟩⟩⟩

theorem Family.injective {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
    {height : (u : List Bool) → Fin (count F u)} {c : List Bool} (B : Family F cone height c)
    (t : Ioo (endpointValue F cone height false c) (endpointValue F cone height true c)) :
    Function.Injective (fun j => B.curve j t.val) := by
  intro j k he
  have H := (B.complete t (B.curve j t.val)).mp (B.roots j t.val (Ioo_subset_Icc_self t.property))
  exact H.unique rfl he.symm

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
