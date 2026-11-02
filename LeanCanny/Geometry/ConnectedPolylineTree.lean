/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.SmallConnectedChains
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.UniformSpace.Path
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Isometry
/-! # Actual connected-region refinements of ambient polyline trees

Leaves retain their source endpoints and an open connected region. Local
connectedness constructs arbitrarily fine leaf expansions inside each old
region. Ambient straight segments provide continuous approximate paths; no
path in the source is assumed when constructing these expansions.
-/
@[expose] public section
namespace LeanCanny.Geometry.ConnectedPolylineTree
open Set SmallConnectedChains
open scoped Classical unitInterval
variable {X : Type*} [MetricSpace X]

structure Region (a b : X) where
  carrier : Set X
  isOpen : IsOpen carrier
  isConnected : IsConnected carrier
  left : a∈carrier
  right : b∈carrier

inductive Tree : X → X → Type _
  | edge {a b : X} (region : Region a b) : Tree a b
  | join {a b c : X} (left : Tree a b) (right : Tree b c) : Tree a c

namespace Tree
variable {a b c : X}
def Inside (K : Set X) : {a b : X} → Tree a b → Prop
  | _,_,.edge r => r.carrier⊆K
  | _,_,.join p q => p.Inside K ∧ q.Inside K

def Fine (ε : ℝ) : {a b : X} → Tree a b → Prop
  | _,_,.edge r => ∀ x∈r.carrier, ∀ y∈r.carrier, dist x y≤ε
  | _,_,.join p q => p.Fine ε ∧ q.Fine ε

theorem inside_mono (p : Tree a b) (K L : Set X) (hp : p.Inside K) (hKL : K⊆L) : p.Inside L := by
  induction p with
  | edge r => exact hp.trans hKL
  | join p q ihp ihq => exact ⟨ihp hp.1,ihq hp.2⟩

inductive Refines : {a b : X} → Tree a b → Tree a b → Prop
  | edge {a b : X} (r : Region a b) (q : Tree a b) (inside : q.Inside r.carrier) : Refines (.edge r) q
  | join {a b c : X} {p p' : Tree a b} {q q' : Tree b c}
      (left : Refines p p') (right : Refines q q') : Refines (.join p q) (.join p' q')

variable [LocallyConnectedSpace X]
omit [LocallyConnectedSpace X] in
private theorem tree_of_small (U : Set X) (ε : ℝ) {a b : X} (h : Small U ε a b) :
    ∃ p : Tree a b, p.Inside U ∧ p.Fine ε := by
  obtain ⟨V,HO,HC,HU,HD,HA,HB⟩ := h
  exact ⟨.edge ⟨V,HO,HC,HA,HB⟩,HU,fun x hx y hy => (HD x hx y hy).le⟩

private theorem tree_of_chain (U : Set X) (hU : IsOpen U) (ε : ℝ) (hε : 0 < ε) (a b : U)
    (h : Relation.ReflTransGen (fun x y : U => Small U ε x.val y.val) a b) :
    ∃ p : Tree a.val b.val, p.Inside U ∧ p.Fine ε := by
  induction h with
  | refl => exact tree_of_small U ε (mem_of_mem_nhds (small_nhds U hU ε hε a.val a.property))
  | @tail b c _h H ih =>
    obtain ⟨p,HP,HF⟩ := ih
    obtain ⟨q,HQ,HG⟩ := tree_of_small U ε H
    exact ⟨.join p q,⟨HP,HQ⟩,⟨HF,HG⟩⟩

theorem exists_inside (U : Set X) (hU : IsOpen U) (hC : IsPreconnected U) (ε : ℝ) (hε : 0 < ε) (a b : U) :
    ∃ p : Tree a.val b.val, p.Inside U ∧ p.Fine ε :=
  tree_of_chain U hU ε hε a b (chain U U hC hU subset_rfl ε hε a b)

theorem exists_refinement (p : Tree a b) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : Tree a b, p.Refines q ∧ q.Fine ε := by
  induction p with
  | edge r =>
    obtain ⟨q,HQ,HF⟩ := exists_inside r.carrier r.isOpen r.isConnected.isPreconnected ε hε ⟨_,r.left⟩ ⟨_,r.right⟩
    exact ⟨q,.edge r q HQ,HF⟩
  | join p q ihp ihq =>
    obtain ⟨p',HP,HF⟩ := ihp
    obtain ⟨q',HQ,HG⟩ := ihq
    exact ⟨.join p' q',.join HP HQ,⟨HF,HG⟩⟩
end Tree

section Ambient
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (e : X → V)
noncomputable def realize (e : X → V) : {a b : X} → Tree a b → Path (e a) (e b)
  | _,_,.edge _ => Path.segment _ _
  | _,_,.join p q => (realize e p).trans (realize e q)

theorem realize_mem {a b : X} (p : Tree a b) (K : Set V) (hK : Convex ℝ K)
    (hp : p.Inside (e ⁻¹' K)) : ∀ t, realize e p t∈K := by
  induction p with
  | edge r =>
    intro t
    apply hK.segment_subset (hp r.left) (hp r.right)
    rw [← Path.range_segment]
    exact mem_range_self t
  | join p q ihp ihq =>
    intro t
    rw [realize,Path.trans_apply]
    split_ifs
    · exact ihp hp.1 _
    · exact ihq hp.2 _

theorem realize_dist_refinement {a b : X} (he : Isometry e) {p q : Tree a b}
    (hr : p.Refines q) (ε : ℝ) (hp : p.Fine ε) : ∀ t, dist (realize e p t) (realize e q t)≤2*ε := by
  induction hr with
  | @edge a b r q hinside =>
    have HK : ∀ x∈r.carrier, e x∈Metric.closedBall (e a) ε := by
      intro x hx
      rw [Metric.mem_closedBall,he.dist_eq]
      exact hp x hx a r.left
    have HQ : q.Inside (e ⁻¹' Metric.closedBall (e a) ε) :=
      Tree.inside_mono q _ _ hinside HK
    have Hq := realize_mem e q _ (convex_closedBall _ _) HQ
    have Hp := realize_mem e (Tree.edge r) _ (convex_closedBall _ _) HK
    intro t
    have HL := Hp t
    have HR := Hq t
    rw [Metric.mem_closedBall] at HL HR
    calc
      dist (realize e (.edge r) t) (realize e q t)≤
          dist (realize e (.edge r) t) (e a)+dist (e a) (realize e q t) := dist_triangle _ _ _
      _ ≤ 2*ε := by rw [dist_comm (e a)]; linarith
  | join _ _ ihp ihq =>
    intro t
    rw [realize,realize,Path.trans_apply,Path.trans_apply]
    split_ifs
    · exact ihp hp.1 _
    · exact ihq hp.2 _
theorem realize_near_source {a b : X} (he : Isometry e) (p : Tree a b) (ε : ℝ) (hp : p.Fine ε) :
    ∀ t, ∃ x : X, dist (realize e p t) (e x)≤ε := by
  induction p with
  | @edge a b r =>
    have HK : (Tree.edge r).Inside (e ⁻¹' Metric.closedBall (e a) ε) := by
      intro x hx
      change e x∈Metric.closedBall (e a) ε
      rw [Metric.mem_closedBall,he.dist_eq]
      exact hp x hx a r.left
    intro t
    exact ⟨a,Metric.mem_closedBall.mp (realize_mem e (.edge r) _ (convex_closedBall _ _) HK t)⟩
  | join p q ihp ihq =>
    intro t
    rw [realize,Path.trans_apply]
    split_ifs
    · exact ihp hp.1 _
    · exact ihq hp.2 _

end Ambient
end LeanCanny.Geometry.ConnectedPolylineTree
