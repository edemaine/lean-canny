/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointRankWordGeometry

/-! # Native descriptor words distinguish points and persist along branches -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointRankWord
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry Set
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

theorem ranks_eq_of_word_eq {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j k : J) (s w v : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (hW : BranchView F cone height points j s w) (hV : BranchView F cone height points k s v)
    (he : word F cone height (pair s w) = word F cone height (pair s v)) :
    AlgebraicFiberImageRank.rank (points s (sampleValue F cone height s w)) j =
      AlgebraicFiberImageRank.rank (points s (sampleValue F cone height s v)) k := by
  have hwords : branchWord F cone height points j s w = branchWord F cone height points k s v :=
    (word_packet_pair F cone height points j s w hs hw hW).symm.trans
      (he.trans (word_packet_pair F cone height points k s v hs hv hV))
  funext i
  let W := SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) s + 1
  have H := congrArg (fun z : List Bool => Nat.fromBitsLE ((z.drop (i.val * W)).take W)) hwords
  rw [branchWord_decode F cone height points j s w hs hw hW i.val i.isLt,
    branchWord_decode F cone height points k s v hs hv hV i.val i.isLt] at H
  simpa only [branchOrdinal, FlatAffineEndpointFiniteSide.coordinate_encode] using H

theorem word_eq_implies_current_eq {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j k : J) (s w v : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (hW : BranchView F cone height points j s w) (hV : BranchView F cone height points k s v)
    (ht : sampleValue F cone height s w = sampleValue F cone height s v)
    (he : word F cone height (pair s w) = word F cone height (pair s v)) :
    currentValue F cone height s w = currentValue F cone height s v := by
  have hrank := ranks_eq_of_word_eq F cone height points j k s w v hs hw hv hW hV he
  rw [ht] at hrank
  have hpoints := (AlgebraicFiberImageRank.rank_eq_iff (points s (sampleValue F cone height s v)) j k).mp hrank
  calc
    currentValue F cone height s w = points s (sampleValue F cone height s w) j := hW.2.2
    _ = points s (sampleValue F cone height s v) j := by rw [ht]
    _ = points s (sampleValue F cone height s v) k := hpoints
    _ = currentValue F cone height s v := hV.2.2.symm

theorem word_eq_of_same_branch {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s w v : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (hW : BranchView F cone height points j s w) (hV : BranchView F cone height points j s v)
    {a b : ℝ} (p : Fin (FlatAffineEndpointFiniteSide.originalCount F s) → Polynomial (Polynomial ℤ))
    (havoid : ∀ u ∈ Ioo a b, ∀ i, SymbolicScaledSquarefree.scalarEvaluation u (SymbolicScaledSquarefree.exceptional (p i)) ≠ 0)
    (hc : ∀ k, ContinuousOn (fun t => points s t k) (Ioo a b))
    (hroot : ∀ k u, u ∈ Ioo a b → ∀ i, (p i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u) (points s u k i) = 0)
    (hws : sampleValue F cone height s w ∈ Ioo a b) (hvs : sampleValue F cone height s v ∈ Ioo a b) :
    word F cone height (pair s w) = word F cone height (pair s v) := by
  let curve : J → C(Ioo a b, Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ) :=
    fun k => ⟨fun u => points s u.val k, continuousOn_iff_continuous_domRestrict.mp (hc k)⟩
  have H := AlgebraicFiberImageRank.rank_eq p havoid curve (fun k u i => hroot k u.val u.property i) j
    ⟨sampleValue F cone height s w, hws⟩ ⟨sampleValue F cone height s v, hvs⟩
  rw [word_packet_pair F cone height points j s w hs hw hW, word_packet_pair F cone height points j s v hs hv hV]
  unfold branchWord
  apply congrArg (FixedWidthNatVector.encode (FlatAffineEndpointFiniteSide.originalCount F s)
    (SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) s + 1))
  funext i
  exact congrFun H (FlatAffineEndpointFiniteSide.coordinate F s (BinaryNatCode.encode i))

theorem word_eq_iff_branch {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j k : J) (s w v : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (hW : BranchView F cone height points j s w) (hV : BranchView F cone height points k s v)
    {a b : ℝ} (p : Fin (FlatAffineEndpointFiniteSide.originalCount F s) → Polynomial (Polynomial ℤ))
    (havoid : ∀ u ∈ Ioo a b, ∀ i, SymbolicScaledSquarefree.scalarEvaluation u (SymbolicScaledSquarefree.exceptional (p i)) ≠ 0)
    (hc : ∀ l, ContinuousOn (fun t => points s t l) (Ioo a b))
    (hroot : ∀ l u, u ∈ Ioo a b → ∀ i, (p i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation u) (points s u l i) = 0)
    (hws : sampleValue F cone height s w ∈ Ioo a b) (hvs : sampleValue F cone height s v ∈ Ioo a b)
    (hinj : Function.Injective (points s (sampleValue F cone height s v))) :
    word F cone height (pair s w) = word F cone height (pair s v) ↔ j = k := by
  constructor
  · intro he
    have H := ranks_eq_of_word_eq F cone height points j k s w v hs hw hv hW hV he
    let curve : J → C(Ioo a b, Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ) :=
      fun l => ⟨fun u => points s u.val l, continuousOn_iff_continuous_domRestrict.mp (hc l)⟩
    have P := AlgebraicFiberImageRank.rank_eq p havoid curve (fun l u i => hroot l u.val u.property i) j
      ⟨sampleValue F cone height s w, hws⟩ ⟨sampleValue F cone height s v, hvs⟩
    apply hinj
    apply (AlgebraicFiberImageRank.rank_eq_iff (points s (sampleValue F cone height s v)) j k).mp
    exact P.symm.trans H
  · intro he
    subst k
    exact word_eq_of_same_branch F cone height points j s w v hs hw hv hW hV p havoid hc hroot hws hvs

end LeanCanny.Encoding.FlatAffineEndpointRankWord
