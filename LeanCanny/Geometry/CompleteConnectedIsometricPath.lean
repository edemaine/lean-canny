/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.ConnectedPolylineSequence
public import Mathlib.Analysis.SpecificLimits.Normed
/-! # Constructed paths in complete locally connected sources embedded in a Banach space

Actual connected-region polyline refinements give a uniformly Cauchy sequence
of continuous ambient maps. The limit retains both endpoints and lies in the
closed isometric source because its distance from that source tends to zero.
This is a geometric existence theorem, with no effective/native bound asserted.
-/
@[expose] public section
namespace LeanCanny.Geometry.CompleteConnectedIsometricPath
open Set Filter ConnectedPolylineSequence
open scoped Classical Topology unitInterval
variable {X : Type*} [MetricSpace X] [CompleteSpace X] [LocallyConnectedSpace X] [PreconnectedSpace X]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

theorem joined (e : X → V) (he : Isometry e) (a b : X) : Joined a b := by
  obtain ⟨P,HP,HD,HN⟩ := exists_sequence e he a b
  have HC : CauchySeq P := cauchySeq_of_le_geometric (1/2) 2 (by norm_num) (fun n => HD n)
  obtain ⟨f,HF⟩ := cauchySeq_tendsto_of_complete HC
  have HE (t : I) : Tendsto (fun n => P n t) atTop (𝓝 (f t)) :=
    (continuous_eval_const t).continuousAt.tendsto.comp HF
  have H0 : f 0=e a := by
    have H : Tendsto (fun _ : ℕ => e a) atTop (𝓝 (f 0)) := by
      convert HE 0 using 1
      funext n
      exact (HP n).1.symm
    exact tendsto_nhds_unique H tendsto_const_nhds
  have H1 : f 1=e b := by
    have H : Tendsto (fun _ : ℕ => e b) atTop (𝓝 (f 1)) := by
      convert HE 1 using 1
      funext n
      exact (HP n).2.symm
    exact tendsto_nhds_unique H tendsto_const_nhds
  have HS : Tendsto scale atTop (𝓝 (0 : ℝ)) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have HR (t : I) : f t∈range e := by
    apply he.isClosedEmbedding.isClosed_range.closure_subset
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    have HA : ∀ᶠ n in atTop, dist (P n t) (f t)<δ/2 :=
      (HE t).eventually (Metric.ball_mem_nhds _ (by linarith))
    have HB : ∀ᶠ n in atTop, scale n<δ/2 := HS.eventually (gt_mem_nhds (by linarith))
    obtain ⟨n,HA,HB⟩ := (HA.and HB).exists
    obtain ⟨x,HX⟩ := HN n t
    refine ⟨e x,mem_range_self x,?_⟩
    calc
      dist (f t) (e x)≤dist (f t) (P n t)+dist (P n t) (e x) := dist_triangle _ _ _
      _ < δ := by rw [dist_comm (f t)]; linarith
  choose g HG using HR
  have Hcont : Continuous g := he.isEmbedding.isInducing.continuous_iff.mpr (by
    have H : e ∘ g=f := funext HG
    rw [H]
    exact f.continuous)
  refine ⟨{toFun := g,continuous_toFun := Hcont,source' := ?_,target' := ?_}⟩
  · exact he.injective ((HG 0).trans H0)
  · exact he.injective ((HG 1).trans H1)
end LeanCanny.Geometry.CompleteConnectedIsometricPath
