/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointBranchRelation
public import LeanCanny.Encoding.FlatAffineHeightOrdinals

/-! # Checked native descriptors identify actual original slab branches

The original equations imply the computed coordinate relations. The native
slab code supplies avoidance of their exceptions, so descriptor comparison
identifies the original branch across independently labeled sample heights.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineEndpointBranchRelation
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem coordinate_root (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (r : List Bool)
    (t : ℝ) (x : Fin (count F (pairFst r)) → ℝ) (hx : FlatAffineEndpointMidpoint.equation F height r t x)
    (i : Fin (count F (pairFst r))) :
    (FlatAffineHeightGrid.coordinate F height (pairFst r) i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t) (x i) = 0 := by
  apply FlatAffineHeightOrdinals.coordinate_root F height (pairFst r) t x _ i
  have H := (AffineConstantParameterShift.roots_iff (FlatAffinePowerPositive.system F (pairFst r))
    (fun j => if j = height (pairFst r) then Polynomial.X else 0) (SymbolicScaledSquarefree.scalarEvaluation t) x).mpr (by
      intro j
      by_cases hj : j = height (pairFst r)
      · simpa only [hj, ite_true, SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hx j
      · simpa only [hj, ite_false, map_zero] using hx j)
  funext j
  rw [IntegerGridArcs.real_value]
  exact H j

theorem coordinate_avoid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (t : ℝ)
    (ht : t ∉ FlatAffineEndpointSampleSlab.roots F cone height s)
    (i : Fin (FlatAffineEndpointFiniteSide.originalCount F s)) :
    SymbolicScaledSquarefree.scalarEvaluation t
      (SymbolicScaledSquarefree.exceptional (FlatAffineHeightGrid.coordinate F height (pairFst (pairFst s)) i)) ≠ 0 := by
  have hR : FlatAffineHeightCells.roots F cone height (pairFst (pairFst s)) =
      FlatAffineEndpointSampleSlab.roots F cone height s := rfl
  have hn : t ∉ FlatAffineHeightCells.roots F cone height (pairFst (pairFst s)) := by rwa [hR]
  have he := (FlatAffineHeightCells.mem_roots_iff F cone height (pairFst (pairFst s)) t).not.mp hn
  have H := FlatAffineHeightSlabExceptional.avoids (SymbolicScaledSquarefree.scalarEvaluation t)
    F cone height (pairFst (pairFst s)) he
  simp only [FlatAffineHeightArcs.exceptional, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_const] at H
  exact H.1 i

theorem identifies {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j l : J) (s w v tWord uWord : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (hW : FlatAffineEndpointRankWord.BranchView F cone height points j s w)
    (hV : FlatAffineEndpointRankWord.BranchView F cone height points l s v)
    (k : Fin ((FlatAffineEndpointSampleSlab.roots F cone height s).card + 1))
    (hleft : pair (pair s w) (pair tWord (BinaryNatCode.encode k.val)) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    (hright : pair (pair s v) (pair uWord (BinaryNatCode.encode k.val)) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    {a b : ℝ} (hgap : OrderedRealCells.gap (FlatAffineEndpointSampleSlab.roots F cone height s) k = Ioo a b)
    (hc : ∀ m, ContinuousOn (fun t => points s t m) (Ioo a b))
    (hroot : ∀ m t, t ∈ Ioo a b → FlatAffineEndpointMidpoint.equation F height (pairFst s) t (points s t m))
    (hinj : Function.Injective (points s (FlatAffineEndpointRankWord.sampleValue F cone height s v))) :
    pair (pair s (BinaryNatCode.encode k.val)) (pair (pair w tWord) (pair v uWord)) ∈
      Encoding.FlatAffineEndpointBranchRelation.language F cone height ↔ j = l := by
  have hws := FlatAffineEndpointSampleSlab.gap_of_mem F cone height s w tWord hs hw k hleft
  have hvs := FlatAffineEndpointSampleSlab.gap_of_mem F cone height s v uWord hs hv k hright
  have hwpoint := congrArg (FlatAffineEndpointFiniteProjection.sample F s) (FlatAffineEndpointRankWord.anchorPoint_packet F cone height s w hw)
  have hvpoint := congrArg (FlatAffineEndpointFiniteProjection.sample F s) (FlatAffineEndpointRankWord.anchorPoint_packet F cone height s v hv)
  have hsW : FlatAffineEndpointRankWord.sampleValue F cone height s w ∈ Ioo a b := by
    rw [← hgap]
    exact (congrArg (fun t => t ∈ OrderedRealCells.gap (FlatAffineEndpointSampleSlab.roots F cone height s) k) hwpoint.symm).mp hws
  have hsV : FlatAffineEndpointRankWord.sampleValue F cone height s v ∈ Ioo a b := by
    rw [← hgap]
    exact (congrArg (fun t => t ∈ OrderedRealCells.gap (FlatAffineEndpointSampleSlab.roots F cone height s) k) hvpoint.symm).mp hvs
  rw [Encoding.FlatAffineEndpointBranchRelation.packet F cone height s w v tWord uWord (BinaryNatCode.encode k.val) hs hw hv hleft hright]
  exact FlatAffineEndpointRankWord.word_eq_iff_branch F cone height points j l s w v hs hw hv hW hV
    (FlatAffineHeightGrid.coordinate F height (pairFst (pairFst s)))
    (fun t ht i => coordinate_avoid F cone height s t (OrderedRealCells.gap_no_root _ k (by rwa [hgap])) i)
    hc (fun m t ht i => coordinate_root F height (pairFst s) t (points s t m) (hroot m t ht) i) hsW hsV hinj

end LeanCanny.Connectivity.FlatAffineEndpointBranchRelation
