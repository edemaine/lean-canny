/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineEndpointCellIncidence
public import LeanCanny.Encoding.FlatAffineEndpointAdjacentComplete

/-! # Accepted native sample labels identify original endpoint edges

The native adjacency language selects a sample in the correct refined gap.
Every such accepted sample identifies the original slab's endpoint edge by
midpoint matching. No new attachment is needed at extra refinement roots.
Computing the multivariate midpoint predicate is the remaining native step.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineEndpointNativeIncidence
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointMidpoint (equation)
open IntegerPolynomialAdjacentSamples (endpointRecord sampleRecord)
open OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def record (q : List Bool) : List Bool := pairFst (pairFst q)

noncomputable def endpoint (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : ℝ :=
  IntegerPolynomialSampleSlice.point (FlatAffineEndpointAdjacentSamples.heightSource F hcone height) (endpointRecord q)

noncomputable def sample (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) : ℝ :=
  IntegerPolynomialSampleSlice.point (FlatAffineEndpointSamples.source F hcone height) (sampleRecord q)

theorem endpoint_root (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (ha : endpointRecord q ∈ IntegerPolynomialSampleSlice.valid (FlatAffineEndpointAdjacentSamples.heightSource F hcone height)) :
    SymbolicScaledSquarefree.scalarEvaluation (endpoint F hcone height q)
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (record q))) = 0 := by
  have hp := IntegerPolynomialSampleSlice.point_root (FlatAffineEndpointAdjacentSamples.heightSource F hcone height)
    (endpointRecord q) ha (FlatAffineHeightSlabExceptional.ne_zero F hcone height _)
  have hc : pairFst (pairFst (endpointRecord q)) = record q := by simp only [endpointRecord, record, pairFst_pair]
  rw [hc] at hp
  exact hp

theorem left_iff {J : Type*} [Finite J] (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointAdjacentSamples.language F hcone height true) {b : ℝ}
    (hab : endpoint F hcone height q < b)
    (hb : SymbolicScaledSquarefree.scalarEvaluation b (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (record q))) = 0)
    (curve : J → ℝ → Fin (count F (pairFst (record q))) → ℝ)
    (hc : ∀ j, ContinuousOn (curve j) (Icc (endpoint F hcone height q) b))
    (hroot : ∀ j t, t ∈ Icc (endpoint F hcone height q) b → equation F height (record q) t (curve j t))
    (j : J) (x : FiniteFiberSlab.Fiber (equation F height (record q)) (endpoint F hcone height q)) :
    EndpointMidpoint.Matches {y | equation F height (record q) (endpoint F hcone height q) y} x.val
        (curve j (sample F hcone height q)) ↔
      FiniteFiberSlab.Edge (equation F height (record q)) curve (endpoint F hcone height q) b (.inl j) (.inr (.inl x)) := by
  have hr := hq.1
  have ha := hq.2.1
  have ht := hq.2.2.1
  have he := endpoint_root F hcone height q ha
  let R := FlatAffineEndpointCells.roots F hcone height (record q)
  obtain ⟨i, hi⟩ := exists_root R (endpoint F hcone height q) (FlatAffineEndpointCells.endpoint_mem F hcone height (record q) hr _ he)
  obtain ⟨k, hk⟩ := exists_root R b (FlatAffineEndpointCells.endpoint_mem F hcone height (record q) hr b hb)
  dsimp only [R] at hi hk
  have hgap : sample F hcone height q ∈ gap R (rightGap R i) :=
    (FlatAffineEndpointAdjacentSamples.gap_packet F hcone height true q hr ha ht i hi).mp hq
  have hsb : sample F hcone height q < b := by
    simpa only [R, hk] using rightGap_lt_root R i k (by rw [hi, hk]; exact hab) hgap
  let x' : FiniteFiberSlab.Fiber (equation F height (record q)) (root R i) :=
    ⟨x.val, by rw [hi]; exact x.property⟩
  have H := FlatAffineEndpointCellIncidence.left_iff F hcone height (record q) hr i
    (by simpa only [hi] using he) curve (fun l => by simpa only [hi] using hc l)
    (fun l t h => hroot l t (by simpa only [hi] using h)) j x' (sample F hcone height q) hgap hsb
  change EndpointMidpoint.Matches {y | equation F height (record q) (root R i) y} x.val
      (curve j (sample F hcone height q)) ↔ curve j (root R i) = x.val at H
  change EndpointMidpoint.Matches {y | equation F height (record q) (endpoint F hcone height q) y} x.val
      (curve j (sample F hcone height q)) ↔ curve j (endpoint F hcone height q) = x.val
  simpa only [R, hi] using H

theorem right_iff {J : Type*} [Finite J] (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointAdjacentSamples.language F hcone height false) {a : ℝ}
    (hab : a < endpoint F hcone height q)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (record q))) = 0)
    (curve : J → ℝ → Fin (count F (pairFst (record q))) → ℝ)
    (hc : ∀ j, ContinuousOn (curve j) (Icc a (endpoint F hcone height q)))
    (hroot : ∀ j t, t ∈ Icc a (endpoint F hcone height q) → equation F height (record q) t (curve j t))
    (j : J) (x : FiniteFiberSlab.Fiber (equation F height (record q)) (endpoint F hcone height q)) :
    EndpointMidpoint.Matches {y | equation F height (record q) (endpoint F hcone height q) y} x.val
        (curve j (sample F hcone height q)) ↔
      FiniteFiberSlab.Edge (equation F height (record q)) curve a (endpoint F hcone height q) (.inl j) (.inr (.inr x)) := by
  have hr := hq.1
  have heValid := hq.2.1
  have ht := hq.2.2.1
  have he := endpoint_root F hcone height q heValid
  let R := FlatAffineEndpointCells.roots F hcone height (record q)
  obtain ⟨i, hi⟩ := exists_root R (endpoint F hcone height q) (FlatAffineEndpointCells.endpoint_mem F hcone height (record q) hr _ he)
  obtain ⟨k, hk⟩ := exists_root R a (FlatAffineEndpointCells.endpoint_mem F hcone height (record q) hr a ha)
  dsimp only [R] at hi hk
  have hgap : sample F hcone height q ∈ gap R (leftGap R i) :=
    (FlatAffineEndpointAdjacentSamples.gap_packet F hcone height false q hr heValid ht i hi).mp hq
  have has : a < sample F hcone height q := by
    simpa only [R, hk] using root_lt_leftGap R i k (by rw [hi, hk]; exact hab) hgap
  let x' : FiniteFiberSlab.Fiber (equation F height (record q)) (root R i) :=
    ⟨x.val, by rw [hi]; exact x.property⟩
  have H := FlatAffineEndpointCellIncidence.right_iff F hcone height (record q) hr i
    (by simpa only [hi] using he) curve (fun l => by simpa only [hi] using hc l)
    (fun l t h => hroot l t (by simpa only [hi] using h)) j x' (sample F hcone height q) hgap has
  change EndpointMidpoint.Matches {y | equation F height (record q) (root R i) y} x.val
      (curve j (sample F hcone height q)) ↔ curve j (root R i) = x.val at H
  change EndpointMidpoint.Matches {y | equation F height (record q) (endpoint F hcone height q) y} x.val
      (curve j (sample F hcone height q)) ↔ curve j (endpoint F hcone height q) = x.val
  simpa only [R, hi] using H

end LeanCanny.Connectivity.FlatAffineEndpointNativeIncidence
