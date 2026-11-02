/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Logic.Relation
/-! # Finite refinement chains through small connected open neighborhoods

This is the finite-chain step of the complete-metric local-path construction.
Connectedness, not an already supplied path, gives the chain. Every chain
vertex remains in the original connected set; consecutive vertices lie in an
actual small connected open neighborhood inside the prescribed working set.
-/
@[expose] public section
namespace LeanCanny.Geometry.SmallConnectedChains
open Set Filter
open scoped Classical Topology
variable {X : Type*}
section Topological
variable [TopologicalSpace X]

theorem reachable [PreconnectedSpace X] (R : X → X → Prop)
    (symm : ∀ x y, R x y → R y x) (nhds : ∀ x, {y | R x y}∈𝓝 x) (x y : X) :
    Relation.ReflTransGen R x y := by
  let A := {z | Relation.ReflTransGen R x z}
  have HA : IsOpen A := isOpen_iff_mem_nhds.mpr (by
    intro z hz
    exact Filter.mem_of_superset (nhds z) (fun w hw => hz.tail hw))
  have HB : IsOpen Aᶜ := isOpen_iff_mem_nhds.mpr (by
    intro z hz
    apply Filter.mem_of_superset (nhds z)
    intro w hw H
    exact hz (H.tail (symm z w hw)))
  have HE : A=univ := (show IsClopen A from ⟨isOpen_compl_iff.mp HB,HA⟩).eq_univ ⟨x,Relation.ReflTransGen.refl⟩
  have H : y∈A := HE ▸ mem_univ y
  exact H

end Topological
section Metric
variable [PseudoMetricSpace X]
def Small (U : Set X) (ε : ℝ) (x y : X) : Prop :=
  ∃ V : Set X, IsOpen V ∧ IsConnected V ∧ V⊆U ∧
    (∀ a∈V, ∀ b∈V, dist a b<ε) ∧ x∈V ∧ y∈V

theorem small_symm (U : Set X) (ε : ℝ) (x y : X) (h : Small U ε x y) : Small U ε y x := by
  obtain ⟨V,HO,HC,HU,HD,HX,HY⟩ := h
  exact ⟨V,HO,HC,HU,HD,HY,HX⟩

variable [LocallyConnectedSpace X]
theorem small_nhds (U : Set X) (hU : IsOpen U) (ε : ℝ) (hε : 0 < ε) (x : X) (hx : x∈U) :
    {y | Small U ε x y}∈𝓝 x := by
  have HN : U∩Metric.ball x (ε/2)∈𝓝 x := Filter.inter_mem (hU.mem_nhds hx) (Metric.ball_mem_nhds _ (by linarith))
  obtain ⟨V,HV,HO,HX,HC⟩ := (locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance) x _ HN
  apply Filter.mem_of_superset (HO.mem_nhds HX)
  intro y hy
  refine ⟨V,HO,HC,fun z hz => (HV hz).1,?_,HX,hy⟩
  intro a ha b hb
  have HA := (HV ha).2
  have HB := (HV hb).2
  rw [Metric.mem_ball] at HA HB
  calc
    dist a b≤dist a x+dist x b := dist_triangle _ _ _
    _ < ε := by rw [dist_comm x b]; linarith

theorem chain (C U : Set X) (hC : IsPreconnected C) (hU : IsOpen U) (hCU : C⊆U)
    (ε : ℝ) (hε : 0 < ε) (x y : C) :
    Relation.ReflTransGen (fun a b : C => Small U ε a.val b.val) x y := by
  let : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp hC
  apply reachable _ (fun a b h => small_symm U ε a.val b.val h)
  intro a
  exact continuous_subtype_val.continuousAt.preimage_mem_nhds (small_nhds U hU ε hε a.val (hCU a.property))
end Metric
end LeanCanny.Geometry.SmallConnectedChains
